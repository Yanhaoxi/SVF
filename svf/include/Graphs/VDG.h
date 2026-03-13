//===- VDG.h -- Version Dependency Graph -----------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2025>  <Yulei Sui>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * VDG.h  -  Version Dependency Graph (adjacency-set, version-keyed)
 *
 *  Created on: Jan 31, 2026
 *      Author: Codex
 */

#ifndef VDG_H_
#define VDG_H_

#include "Graphs/GraphTraits.h"
#include "Util/DenseBitVector.h"
#include "Util/GeneralType.h"
#include "Util/SmallDenseSet.h"
#include "Util/WorkList.h"
#include <cassert>
#include <functional>
#include <limits>
#include <memory>
#include <stack>
#include <string>
#include <vector>

namespace SVF
{

//===----------------------------------------------------------------------===//
// VDGNode - lightweight node, version-keyed.
//   No version field: the version IS the index into VDG::verVec_.
//   No GenericGraph base: adjacency stored as 4 SmallDenseSets of Version.
//===----------------------------------------------------------------------===//
class VDGNode
{
public:
    using AdjSet = SmallDenseSet<Version, 4>;

    VDGNode(bool loadConsume = false, bool storeYield = false)
        : loadConsume_(loadConsume),
          storeYield_(storeYield)
    {
    }

    // --- Properties ---
    inline bool isLoadConsume() const { return loadConsume_; }
    inline bool isStoreYield() const { return storeYield_; }
    inline void setLoadConsume(bool v = true) { loadConsume_ = loadConsume_ || v; }
    inline void setStoreYield(bool v = true) { storeYield_ = storeYield_ || v; }

    // --- Stmt reliance ---
    inline const NodeBS& getStmtRelianceSet() const { return stmtReliance_; }
    inline void mergeStmtReliance(const NodeBS& s) { stmtReliance_ |= s; }

    // --- Adjacency (read) ---
    inline const AdjSet& getSolidOut() const { return solidOut_; }
    inline const AdjSet& getVirtualOut() const { return virtualOut_; }
    inline const AdjSet& getSolidIn() const { return solidIn_; }
    inline const AdjSet& getVirtualIn() const { return virtualIn_; }

    inline size_t outDegree() const { return solidOut_.size() + virtualOut_.size(); }
    inline size_t inDegree() const { return solidIn_.size() + virtualIn_.size(); }
    inline bool hasOutEdge() const { return outDegree() != 0; }
    inline bool hasInEdge() const { return inDegree() != 0; }

    /// Get single outgoing edge info.  Returns false if out-degree != 1.
    inline bool getSingleOutEdge(Version& dst, bool& isVirtual) const
    {
        if (outDegree() != 1) return false;
        if (!solidOut_.empty()) { dst = *solidOut_.begin(); isVirtual = false; }
        else { dst = *virtualOut_.begin(); isVirtual = true; }
        return true;
    }

    /// Get single incoming edge info.  Returns false if in-degree != 1.
    inline bool getSingleInEdge(Version& src, bool& isVirtual) const
    {
        if (inDegree() != 1) return false;
        if (!solidIn_.empty()) { src = *solidIn_.begin(); isVirtual = false; }
        else { src = *virtualIn_.begin(); isVirtual = true; }
        return true;
    }

private:
    friend class VDG;

    bool loadConsume_;
    bool storeYield_;
    NodeBS stmtReliance_;

    AdjSet solidOut_;
    AdjSet virtualOut_;
    AdjSet solidIn_;
    AdjSet virtualIn_;
};


//===----------------------------------------------------------------------===//
// VDG - Version Dependency Graph for one memory object.
//
//   Version-keyed:  Version is the primary key (index into verVec_).
//   Adjacency-set:  Edges stored in VDGNode::AdjSet, no separate edge objects.
//   Super-version:  A version that has not been merged away (= liveness bit).
//===----------------------------------------------------------------------===//
class VDG
{
public:
    typedef VDGNode NodeType;
    typedef std::function<bool(Version, Version)> PropagateCallback;
    typedef std::function<void(Version)> StmtRelianceCallback;

    // --- Construction / destruction ---
    explicit VDG(NodeID obj) : objId_(obj), nodeNum_(0) {}

    ~VDG()
    {
        for (size_t i = 0; i < verVec_.size(); ++i)
        {
            VDGNode* n = verVec_[i];
            if (n && superVersions_[i])
                delete n;
        }
    }

    VDG(const VDG&) = delete;
    VDG& operator=(const VDG&) = delete;

    // --- Accessors ---
    inline NodeID getObjId() const { return objId_; }
    inline u32_t  getTotalNodeNum() const { return nodeNum_; }
    inline size_t capacity() const { return verVec_.size(); }

    inline void reserve(size_t n)
    {
        verVec_.reserve(n);
        repVec_.reserve(n);
        subVec_.reserve(n);
        superVersions_.reserve(n);
    }

    // --- Iteration ---

    /// Iterate over all live (super) node.  fn(Version, VDGNode*).
    template<typename Fn>
    inline void forEachSuperNode(Fn&& fn) const
    {
        for (size_t i = 0; i < superVersions_.size(); ++i)
            if (superVersions_[i])
                fn(static_cast<Version>(i), verVec_[i]);
    }

    // --- Node access ---
    inline VDGNode* getNode(Version v) const
    {
        assert(v < verVec_.size() && verVec_[v] && "version not found!");
        return verVec_[v];
    }

    inline bool hasVersion(Version v) const
    {
        return v < capacity() && repVec_[v] != 0;
    }

    VDGNode* getOrAddNode(Version ver, bool loadConsume = false, bool storeYield = false)
    {
        if (ver < verVec_.size() && verVec_[ver])
        {
            VDGNode* n = verVec_[ver];
            if (loadConsume) n->setLoadConsume();
            if (storeYield) n->setStoreYield();
            return n;
        }

        if (ver >= verVec_.size())
        {
            verVec_.resize(ver + 1, nullptr);
            repVec_.resize(ver + 1, 0);
            subVec_.resize(ver + 1);
            superVersions_.resize(ver + 1, false);
        }

        VDGNode* node = new VDGNode(loadConsume, storeYield);
        verVec_[ver] = node;
        subVec_[ver].set(ver);
        repVec_[ver] = ver;
        superVersions_[ver] = true;
        ++nodeNum_;
        return node;
    }

    // --- Rep / sub version mapping ---
    inline Version getRepVersion(Version v) const
    {
        assert(v < repVec_.size() && "version out of range!");
        return repVec_[v];
    }

    inline const NodeBS& getSubVersions(Version repV) const
    {
        assert(repV < subVec_.size() && "not a rep version!");
        return subVec_[repV];
    }

    inline bool isSuperVersion(Version v) const
    {
        assert(v < superVersions_.size() && "version out of range!");
        return superVersions_[v];
    }

    // --- Stmt reliance ---
    inline const NodeBS& getStmtReliance(Version v) const
    {
        return getNode(v)->getStmtRelianceSet();
    }

    inline void bindStmtReliance(Version v, const NodeBS& stmts)
    {
        getNode(v)->mergeStmtReliance(stmts);
    }

    // --- Edge API ---
    bool addEdge(Version srcV, Version dstV, bool isVirtual);
    bool removeEdge(Version srcV, Version dstV, bool isVirtual);

    inline bool addSolidEdge(Version s, Version d) { return addEdge(s, d, false); }
    inline bool addVirtualEdge(Version s, Version d) { return addEdge(s, d, true); }

    inline const VDGNode::AdjSet& solidOutOf(Version v) const
    {
        return getNode(v)->getSolidOut();
    }

    // --- Update tracking ---
    inline void markVersionUpdated(Version v)
    {
        updatedNodes_.push_back(getRepVersion(v));
    }

    inline void clearUpdates() { updatedNodes_.clear(); }
    inline bool hasPendingUpdates() const { return !updatedNodes_.empty(); }
    inline const NodeVector& getUpdatedNodes() const { return updatedNodes_; }

    // --- Merge / simplify ---
    void mergeVersionsIntoRep(const NodeVector& versions, Version repVer);
    NodeVector sccMergeSolidEdges(const NodeVector& candidates = NodeVector());
    void propagateInTopoOrder(PropagateCallback propagate, StmtRelianceCallback onChanged);

    void pruneUnreachableToLoadConsume();
    void pruneUnreachableFromStoreYield();
    void reduceByStableSrcReachability();
    void reduceByStableDstReachability();
    void reverseReachMergeByAnchors();
    void chainContraction();
    void transitiveRedundancyElimination();

    // --- Lifecycle ---
    void enterSolve();

    // --- Debug / dump ---
    void dump(const std::string& filename);
    void view();

private:
    /// Edge internals
    bool addEdgeInternal(Version srcRep, Version dstRep, bool isVirtual);
    void removeAllVirtualEdges();
    void moveEdgesToRep(Version sub, Version rep);

    void removeNodeAndEdges(Version repV);
    void deleteNode(Version repV);

    // --- Data ---
    NodeID objId_;
    u32_t  nodeNum_;

    std::vector<VDGNode*> verVec_;          ///< version -> node (or rep node)
    std::vector<Version>  repVec_;          ///< sub -> rep (0 = invalid)
    std::vector<NodeBS>   subVec_;          ///< rep -> {all sub versions}
    std::vector<bool>     superVersions_;   ///< liveness bit per version
    NodeVector            updatedNodes_;    ///< pending updated rep versions
};


//===----------------------------------------------------------------------===//
// VDGSCCDetection - Tarjan SCC on solid edges of a VDG.
//===----------------------------------------------------------------------===//
class VDGSCCDetection
{
public:
    typedef std::stack<Version> GNodeStack;

    explicit VDGSCCDetection(VDG* graph)
        : graph_(graph),
          counter_(0),
          capacity_(graph->capacity()),
          disc_(capacity_, 0),
          rep_(capacity_, UINT_MAX),
          inSCC_(capacity_, false),
          visited_(capacity_, false)
    {
    }

    void find()
    {
        graph_->forEachSuperNode([this](Version v, VDGNode*)
        {
            if (!visited_[v]) visit(v);
        });
    }

    void find(const NodeVector& candidates)
    {
        for (Version v : candidates)
        {
            if (!graph_->hasVersion(v)) continue;
            if (!graph_->isSuperVersion(v)) continue;
            if (!visited_[v]) visit(v);
        }
    }

    GNodeStack&       topoNodeStack()       { return topoStack_; }
    const GNodeStack& topoNodeStack() const { return topoStack_; }

    const NodeBS& subNodes(Version repV) const
    {
        auto it = subNodes_.find(repV);
        assert(it != subNodes_.end() && "rep should have sub-node set!");
        return it->second;
    }

private:
    void visit(Version v)
    {
        ++counter_;
        disc_[v] = counter_;
        setRep(v, v);
        visited_[v] = true;

        for (Version w : graph_->solidOutOf(v))
        {
            if (!graph_->isSuperVersion(w)) continue;
            if (!visited_[w]) visit(w);
            if (!inSCC_[w])
            {
                Version r = (disc_[rep_[v]] < disc_[rep_[w]]) ? rep_[v] : rep_[w];
                setRep(v, r);
            }
        }

        if (rep_[v] == v)
        {
            inSCC_[v] = true;
            while (!sccStack_.empty())
            {
                Version w = sccStack_.top();
                if (disc_[w] <= disc_[v]) break;
                sccStack_.pop();
                inSCC_[w] = true;
                setRep(w, v);
            }
            topoStack_.push(v);
        }
        else
        {
            sccStack_.push(v);
        }
    }

    void setRep(Version n, Version r)
    {
        Version old = rep_[n];
        if (old == r) return;

        if (old != UINT_MAX)
        {
            auto it = subNodes_.find(old);
            if (it != subNodes_.end())
            {
                it->second.reset(n);
                if (it->second.empty()) subNodes_.erase(it);
            }
        }

        rep_[n] = r;
        subNodes_[r].set(n);
    }

    VDG* graph_;
    unsigned counter_;
    size_t capacity_;
    std::vector<unsigned> disc_;
    std::vector<Version>  rep_;
    std::vector<bool>     inSCC_;
    std::vector<bool>     visited_;
    Map<Version, NodeBS>  subNodes_;
    GNodeStack sccStack_;
    GNodeStack topoStack_;
};


//===----------------------------------------------------------------------===//
// VDGManager - owns all per-object VDGs.
//===----------------------------------------------------------------------===//
class VDGManager
{
public:
    typedef Map<NodeID, std::unique_ptr<VDG>> VDGMapTy;

    VDGManager() = default;
    ~VDGManager() = default;

    inline VDG* getOrCreateVDG(NodeID obj)
    {
        auto it = vdgMap.find(obj);
        if (it != vdgMap.end()) return it->second.get();
        vdgMap[obj] = std::make_unique<VDG>(obj);
        return vdgMap[obj].get();
    }

    inline VDG* getVDG(NodeID obj) const
    {
        auto it = vdgMap.find(obj);
        assert(it != vdgMap.end() && "VDG not found!");
        return it->second.get();
    }

    inline VDG* tryGetVDG(NodeID obj) const
    {
        auto it = vdgMap.find(obj);
        return it != vdgMap.end() ? it->second.get() : nullptr;
    }

    inline bool hasVDG(NodeID obj) const
    {
        return vdgMap.find(obj) != vdgMap.end();
    }

    inline void markVersionUpdated(NodeID obj, Version v)
    {
        getVDG(obj)->markVersionUpdated(v);
        pendingVDGs.push(obj);
    }

    inline void markEdgeAdded(NodeID obj, Version srcV)
    {
        markVersionUpdated(obj, srcV);
    }

    inline bool hasPendingVDGs() const { return !pendingVDGs.empty(); }
    inline NodeID popPendingVDG() { return pendingVDGs.pop(); }

    inline VDGMapTy&       getAllVDGs()       { return vdgMap; }
    inline const VDGMapTy& getAllVDGs() const { return vdgMap; }

    void enterSolveAll();

    inline void clear()
    {
        vdgMap.clear();
        pendingVDGs.clear();
    }

    inline Version getRepVersion(NodeID obj, Version v) const
    {
        return getVDG(obj)->getRepVersion(v);
    }

    inline Version getRepVersionOrInvalid(NodeID obj, Version v) const
    {
        const VDG* g = tryGetVDG(obj);
        if (!g || !g->hasVersion(v)) return 0;
        return g->getRepVersion(v);
    }

    inline VersionedVar atRepKey(NodeID obj, Version v) const
    {
        assert(v != 0 && "atRepKey: invalid version!");
        return std::make_pair(obj, getRepVersion(obj, v));
    }

    inline bool tryAtRepKey(NodeID obj, Version v, VersionedVar& out) const
    {
        const VDG* g = tryGetVDG(obj);
        if (!g || !g->hasVersion(v)) return false;
        out = std::make_pair(obj, g->getRepVersion(v));
        return true;
    }

    void dumpStats() const;
    void writeToFile(const std::string& filename) const;

private:
    VDGMapTy vdgMap;
    FIFOWorkList<NodeID> pendingVDGs;
};

} // namespace SVF

#endif // VDG_H_
