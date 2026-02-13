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
 * VDG.h
 *
 *  Created on: Jan 31, 2026
 *      Author: Codex
 */

#ifndef VDG_H_
#define VDG_H_

#include "Graphs/GenericGraph.h"
#include "Util/DenseBitVector.h"
#include "Util/GeneralType.h"
#include "Util/WorkList.h"
#include <algorithm>
#include <cassert>
#include <functional>
#include <iterator>
#include <limits>
#include <memory>
#include <string>
#include <vector>

namespace SVF
{

class VDGNode;
class VDG;

typedef GenericEdge<VDGNode> GenericVDGEdgeTy;

class VDGEdge : public GenericVDGEdgeTy
{
public:
    // virtual => may / flow solid => must flow
    // kind => src to dst edge kind (from direct dependency/store flow/indirect call)
    enum VDGEdgeK
    {
        Depend = 1 << 0,
        StoreFlow = 1 << 1,
        IndCallFlow = 1 << 2
    };

    // NOTE: equalGEdge must be defined BEFORE VDGEdgeSetTy to ensure
    // GenericNode uses this comparator instead of the base class version
    typedef struct equalGEdge
    {
        bool operator()(const VDGEdge* lhs, const VDGEdge* rhs) const
        {
            if (lhs->getSrcID() != rhs->getSrcID())
                return lhs->getSrcID() < rhs->getSrcID();
            return lhs->getDstID() < rhs->getDstID();
        }
    } equalGEdge;

    typedef GenericNode<VDGNode, VDGEdge>::GEdgeSetTy VDGEdgeSetTy;

    inline bool operator==(const GenericVDGEdgeTy* rhs) const override
    {
        return rhs && rhs->getSrcID() == getSrcID() && rhs->getDstID() == getDstID();
    }

    ~VDGEdge() override = default;

    inline VDGEdgeK getVDGEdgeKind() const
    {
        return static_cast<VDGEdgeK>(getEdgeKind() & KindMask);
    }

    inline bool isStoreEdge() const
    {
        return hasKind(StoreFlow);
    }

    inline bool hasKind(VDGEdgeK kind) const
    {
        return (static_cast<u8_t>(getVDGEdgeKind()) & static_cast<u8_t>(kind)) != 0;
    }

    inline void addKind(VDGEdgeK kind)
    {
        const GEdgeFlag cur = getEdgeKindWithoutMask();
        const GEdgeFlag merged = (static_cast<GEdgeFlag>(getVDGEdgeKind())
            | static_cast<GEdgeFlag>(kind)) & KindMask;
        setEdgeFlag((cur & ~KindMask) | merged);
    }

    inline void setVirtual(bool isVirtual)
    {
        const GEdgeFlag cur = getEdgeKindWithoutMask();
        if (isVirtual)
            setEdgeFlag(cur | VirtualEdgeFlag);
        else
            setEdgeFlag(cur & ~VirtualEdgeFlag);
    }

    inline bool isVirtualEdge() const
    {
        return (getEdgeKindWithoutMask() & VirtualEdgeFlag) != 0;
    }

protected:
    static constexpr GEdgeFlag VirtualEdgeFlag = (1ULL << (EdgeKindMaskBits - 1));
    static constexpr GEdgeFlag KindMask = VirtualEdgeFlag - 1;

private:
    friend class VDG;
    VDGEdge(VDGNode *src, VDGNode *dst, VDGEdgeK kind, bool isVirtual = false)
        : GenericVDGEdgeTy(src, dst,
                           (static_cast<GEdgeFlag>(kind) & KindMask)
                           | (isVirtual ? VirtualEdgeFlag : 0))
    {
    }
};

typedef GenericNode<VDGNode, VDGEdge> GenericVDGNodeTy;

class VDGNode : public GenericVDGNodeTy
{
public:
    typedef GenericVDGNodeTy::GEdgeSetTy VDGEdgeSetTy;

    VDGNode(NodeID id, Version ver, bool loadConsume = false, bool storeYield = false,
            GNodeK k = VDGNodeKd)
        : GenericVDGNodeTy(id, k),
          version(ver),
          loadConsume(loadConsume),
          storeYield(storeYield),
          mergedCount(1)  // Initially represents 1 version (itself)
    {
    }

    ~VDGNode() override = default;

    inline Version getVersion() const
    {
        return version;
    }

    inline bool isLoadConsume() const
    {
        return loadConsume;
    }

    inline bool isStoreYield() const
    {
        return storeYield;
    }

    inline void setLoadConsume(bool value = true)
    {
        loadConsume = loadConsume || value;
    }

    inline void setStoreYield(bool value = true)
    {
        storeYield = storeYield || value;
    }

    /// Get number of versions merged into this rep node
    inline u32_t getMergedCount() const
    {
        return mergedCount;
    }

    /// Increment merged count when merging another version
    inline void incrementMergedCount(u32_t count = 1)
    {
        mergedCount += count;
    }

    /// Get statement reliance set bound to this node's version.
    inline const NodeBS& getStmtRelianceSet() const
    {
        return stmtReliance;
    }

    /// Add one statement into this node's reliance set.
    inline void addStmtReliance(NodeID stmt)
    {
        stmtReliance.set(stmt);
    }

    /// Merge another reliance set into this node.
    inline void mergeStmtReliance(const NodeBS& stmts)
    {
        stmtReliance |= stmts;
    }

    static inline bool classof(const VDGNode *)
    {
        return true;
    }

    static inline bool classof(const GenericVDGNodeTy *node)
    {
        return node->getNodeKind() == VDGNodeKd;
    }

private:
    friend class VDG;
    using GenericVDGNodeTy::addIncomingEdge;
    using GenericVDGNodeTy::addOutgoingEdge;
    using GenericVDGNodeTy::removeIncomingEdge;
    using GenericVDGNodeTy::removeOutgoingEdge;

    bool addIncomingEdgeWithKind(VDGEdge* inEdge)
    {
        bool nondup=GenericVDGNodeTy::addIncomingEdge(inEdge);
        assert(nondup && "adding duplicate in edge to VDG node!!!");
        return true;
    }

    bool addOutgoingEdgeWithKind(VDGEdge* outEdge)
    {
        bool nondup=GenericVDGNodeTy::addOutgoingEdge(outEdge);
        assert(nondup && "adding duplicate out edge to VDG node!!!");
        return true;
    }

    bool removeIncomingEdgeWithKind(VDGEdge* inEdge)
    {
        u32_t num1 = GenericVDGNodeTy::removeIncomingEdge(inEdge);
        bool removed = (num1 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    bool removeOutgoingEdgeWithKind(VDGEdge* outEdge)
    {
        u32_t num1 = GenericVDGNodeTy::removeOutgoingEdge(outEdge);
        bool removed = (num1 > 0);
        assert(removed && "edge not in the set, can not remove!!!");
        return removed;
    }

    Version version;
    bool loadConsume;
    bool storeYield;
    u32_t mergedCount;  ///< Number of versions merged into this rep node
    NodeBS stmtReliance; ///< Statements relying on this (rep) version
};

//===----------------------------------------------------------------------===//
// VDG: Self-contained graph with O(1) vector-based node storage
// Does NOT inherit GenericGraph (avoids std::map overhead for node lookup).
// VDGNode still inherits GenericNode for edge storage (OrderedSet).
//===----------------------------------------------------------------------===//
class VDG
{
public:
    typedef VDGNode NodeType;
    typedef VDGEdge EdgeType;

    /// Callback type for version propagation: (srcVersion, dstVersion) -> bool (changed)
    typedef std::function<bool(Version, Version)> PropagateCallback;
    /// Callback type for notifying statement reliance: (version) -> void
    typedef std::function<void(Version)> StmtRelianceCallback;

    //===--- Iterator over live nodes in nodeVec (skips nulls) ---===//
    template<bool IsConst>
    class NodeIterator
    {
    public:
        using VecTy = std::vector<VDGNode*>;
        using VecIter = typename std::conditional<IsConst, VecTy::const_iterator, VecTy::iterator>::type;
        using value_type = std::pair<NodeID, VDGNode*>;
        using iterator_category = std::forward_iterator_tag;
        using difference_type = std::ptrdiff_t;
        using pointer = value_type*;
        using reference = value_type;

        NodeIterator() = default;
        NodeIterator(VecIter cur, VecIter end) : cur_(cur), end_(end) { skipNulls(); }

        /// Allow implicit conversion from non-const to const iterator
        template<bool OtherConst, typename = typename std::enable_if<IsConst && !OtherConst>::type>
        NodeIterator(const NodeIterator<OtherConst>& other) : cur_(other.cur_), end_(other.end_) {}

        value_type operator*() const
        {
            VDGNode* n = *cur_;
            return std::make_pair(n->getId(), n);
        }

        NodeIterator& operator++() { ++cur_; skipNulls(); return *this; }
        NodeIterator operator++(int) { auto tmp = *this; ++(*this); return tmp; }
        bool operator==(const NodeIterator& o) const { return cur_ == o.cur_; }
        bool operator!=(const NodeIterator& o) const { return cur_ != o.cur_; }

    private:
        VecIter cur_, end_;
        void skipNulls() { while (cur_ != end_ && *cur_ == nullptr) ++cur_; }

        // Allow const iterator to access non-const iterator's members
        template<bool> friend class NodeIterator;
    };

    typedef NodeIterator<false> iterator;
    typedef NodeIterator<true>  const_iterator;

    explicit VDG(NodeID obj) : objId(obj), nextNodeId(0), nodeNum(0)
    {
    }

    ~VDG()
    {
        for (VDGNode* n : nodeVec)
            delete n;
    }

    //===--- O(1) Node Lookup ---===//

    /// O(1) node lookup by NodeID
    inline VDGNode* getNodeFast(NodeID id) const
    {
        assert(id < nodeVec.size() && nodeVec[id] != nullptr && "Node not found in nodeVec!");
        return nodeVec[id];
    }

    /// O(1) node existence check
    inline bool hasNodeFast(NodeID id) const
    {
        return id < nodeVec.size() && nodeVec[id] != nullptr;
    }

    //===--- Iteration (compatible with GenericGraph interface) ---===//
    inline iterator begin()       { return iterator(nodeVec.begin(), nodeVec.end()); }
    inline iterator end()         { return iterator(nodeVec.end(), nodeVec.end()); }
    inline const_iterator begin() const { return const_iterator(nodeVec.begin(), nodeVec.end()); }
    inline const_iterator end()   const { return const_iterator(nodeVec.end(), nodeVec.end()); }

    inline u32_t getTotalNodeNum() const { return nodeNum; }

    /// Get the next node ID (upper bound for dense allocation)
    inline NodeID getNextNodeId() const { return nextNodeId; }

    /// Get the object ID this VDG belongs to
    inline NodeID getObjId() const { return objId; }

    void dump(const std::string& filename);
    void view();
    void mergeVersionsIntoRep(const NodeVector& versions, Version repVer);
    void pruneUnreachableToLoadConsume();
    void pruneUnreachableFromStoreYield();
    void reduceByStableDstReachability();
    void reduceByStableSrcReachability();
    void chainContraction();
    void transitiveRedundancyElimination();

    /// Mark a version as updated (stores rep node ID)
    inline void markVersionUpdated(Version v)
    {
        VDGNode* node = getNode(v);  // verVec_ already returns rep node
        updatedNodes_.push_back(node->getId());
    }

    /// Clear all update markers after propagation
    inline void clearUpdateMarkers()
    {
        updatedNodes_.clear();
    }

    /// Check if there are any pending updates
    inline bool hasPendingUpdates() const
    {
        return !updatedNodes_.empty();
    }

    /// Get updated node IDs
    inline const NodeVector& getUpdatedNodes() const
    {
        return updatedNodes_;
    }

    /// SCC merge on solid edges and compute topological order
    /// @param candidates: if non-empty, only traverse from these node IDs; otherwise traverse all
    /// @return topological order of SCC rep node IDs
    NodeVector sccMergeSolidEdges(const NodeVector& candidates = NodeVector());

    //===--- Version Propagation API ---===//

    /// Propagate points-to along solid edges in topological order
    /// @param propagate: callback(srcVersion, dstVersion) returns true if pts changed
    /// @param onVersionChanged: callback(version) called when a version's pts changes
    void propagateInTopoOrder(PropagateCallback propagate, StmtRelianceCallback onVersionChanged);

    //===--- Node Operations ---===//

    VDGNode* getOrAddNode(Version ver, bool loadConsume = false, bool storeYield = false)
    {
        // Ensure verVec_ is large enough for this version
        if (ver < verVec_.size() && verVec_[ver] != nullptr)
        {
            VDGNode* existing = verVec_[ver];
            if (loadConsume) existing->setLoadConsume(true);
            if (storeYield) existing->setStoreYield(true);
            return existing;
        }

        VDGNode *node = new VDGNode(nextNodeId++, ver, loadConsume, storeYield);
        // Add to nodeVec (primary storage)
        if (node->getId() >= nodeVec.size())
            nodeVec.resize(node->getId() + 1, nullptr);
        nodeVec[node->getId()] = node;
        ++nodeNum;

        // Grow version-indexed vectors
        if (ver >= verVec_.size())
        {
            verVec_.resize(ver + 1, nullptr);
            repVec_.resize(ver + 1, 0);
            subVec_.resize(ver + 1);
        }
        verVec_[ver] = node;
        
        // Initialize: each new version is its own rep with itself as sole sub.
        subVec_[ver].set(ver);
        
        // Expand superNodes vector if needed and mark as super
        if (node->getId() >= superNodes.size())
            superNodes.resize(node->getId() + 1, false);
        superNodes[node->getId()] = true;
        
        return node;
    }

    /// Get node by version (always returns rep node after merge)
    inline VDGNode* getNode(Version ver)
    {
        assert(ver < verVec_.size() && verVec_[ver] != nullptr && "version not found in graph!");
        return verVec_[ver];
    }

    inline const VDGNode* getNode(Version ver) const
    {
        assert(ver < verVec_.size() && verVec_[ver] != nullptr && "version not found in graph!");
        return verVec_[ver];
    }

    /// Try get node (returns nullptr if not exists)
    inline VDGNode* tryGetNode(Version ver)
    {
        return (ver < verVec_.size()) ? verVec_[ver] : nullptr;
    }

    inline bool hasVersion(Version ver) const
    {
        return ver < verVec_.size() && verVec_[ver] != nullptr;
    }

    /// Get the version vector capacity (max version + 1)
    inline size_t getVersionCapacity() const
    {
        return verVec_.size();
    }

    //===--- Rep/Sub Version Management ---===//

    /// Get rep version (returns self if already rep, repVec_[v]==0 means self-rep)
    inline Version getRepVersion(Version v) const
    {
        assert(v < repVec_.size() && "version out of range in getRepVersion!");
        return repVec_[v] != 0 ? repVec_[v] : v;
    }

    /// Check if version is a rep version (repVec_[v]==0 means self-rep)
    inline bool isRepVersion(Version v) const
    {
        return v < repVec_.size() && repVec_[v] == 0;
    }

    /// Get all sub versions for a rep (including self)
    inline const NodeBS& getSubVersions(Version repV) const
    {
        assert(repV < subVec_.size() && !subVec_[repV].empty() && "not a rep version!");
        return subVec_[repV];
    }

    /// Get statement reliance of the rep node for a version.
    inline const NodeBS& getStmtReliance(Version v) const
    {
        return getNode(v)->getStmtRelianceSet();
    }

    /// Bind statement reliance to a version's rep node.
    inline void bindStmtReliance(Version v, const NodeBS& stmts)
    {
        getNode(v)->mergeStmtReliance(stmts);
    }

    /// Check if NodeID is a super node (fast O(1) bitset check)
    inline bool isSuperNode(NodeID id) const
    {
        assert(id < superNodes.size() && "NodeID exceeds superNodes size!");
        return superNodes[id];
    }

    /// Get number of super nodes
    size_t getSuperNodeCount() const
    {
        size_t count = 0;
        for (bool b : superNodes) if (b) ++count;
        return count;
    }

    //===--- Edge Operations ---===//

    /// Deep-copy this VDG for a different object ID.
    /// Creates an independent copy with identical structure (nodes, edges, rep/sub maps).
    inline std::unique_ptr<VDG> clone(NodeID newObjId) const
    {
        auto copy = std::make_unique<VDG>(newObjId);
        copy->nextNodeId = nextNodeId;
        copy->superNodes = superNodes;
        copy->repVec_ = repVec_;
        copy->subVec_ = subVec_;
        copy->nodeVec.resize(nodeVec.size(), nullptr);
        copy->nodeNum = nodeNum;
        copy->verVec_.resize(verVec_.size(), nullptr);

        // Copy nodes
        for (auto it = begin(), eit = end(); it != eit; ++it)
        {
            const VDGNode* origNode = (*it).second;
            VDGNode* newNode = new VDGNode(origNode->getId(), origNode->getVersion(),
                                           origNode->isLoadConsume(), origNode->isStoreYield());
            newNode->incrementMergedCount(origNode->getMergedCount() - 1);
            newNode->mergeStmtReliance(origNode->getStmtRelianceSet());
            copy->nodeVec[newNode->getId()] = newNode;
            copy->verVec_[origNode->getVersion()] = newNode;
        }

        // Rebuild verVec_ for sub versions pointing to rep nodes
        for (size_t v = 0; v < repVec_.size(); ++v)
        {
            if (repVec_[v] != 0)  // v is a sub version
            {
                Version repV = repVec_[v];
                if (repV < copy->verVec_.size() && copy->verVec_[repV] != nullptr)
                    copy->verVec_[v] = copy->verVec_[repV];
            }
        }

        // Copy edges
        for (auto it = begin(), eit = end(); it != eit; ++it)
        {
            const VDGNode* origSrc = (*it).second;
            for (auto ei = origSrc->OutEdgeBegin(), eei = origSrc->OutEdgeEnd(); ei != eei; ++ei)
            {
                const VDGEdge* origEdge = *ei;
                VDGNode* newSrc = copy->getNodeFast(origEdge->getSrcID());
                VDGNode* newDst = copy->getNodeFast(origEdge->getDstID());
                VDGEdge* newEdge = new VDGEdge(newSrc, newDst,
                                               origEdge->getVDGEdgeKind(),
                                               origEdge->isVirtualEdge());
                newSrc->addOutgoingEdgeWithKind(newEdge);
                newDst->addIncomingEdgeWithKind(newEdge);
            }
        }

        return copy;
    }

    /// Add edge between versions (auto-converts to rep versions via getNode)
    /// Returns true if a new solid edge is added or virtual edge becomes solid
    /// This is the only public edge API to ensure rep node semantics
    inline bool addEdge(Version srcV, Version dstV, VDGEdge::VDGEdgeK kind, bool isVirtual)
    {
        VDGNode* src = getNode(srcV);  // getNode returns rep node via verVec_
        VDGNode* dst = getNode(dstV);
        if (src == dst) return false;  // No self-loop
        return addEdgeInternal(src, dst, kind, isVirtual);
    }

    /// Delete node from graph by NodeID (frees memory)
    inline void deleteNode(NodeID nodeId)
    {
        VDGNode* node = getNodeFast(nodeId);
        assert(node && "node not found in VDG!");
        assert(!node->hasIncomingEdge() && !node->hasOutgoingEdge()
               && "node with edges cannot be deleted");
        superNodes[nodeId] = false;
        nodeVec[nodeId] = nullptr;
        --nodeNum;
        delete node;
    }

private:
    void logEdgeChange(const char* tag, const VDGEdge* edge);
    void logEdgeMembership(const char* tag, const VDGNode* node, const VDGEdge* edge);
    static bool updateEdgeVirtual(VDGEdge* edge, bool isVirtual);
    void reTargetDstOfEdge(VDGEdge* edge, VDGNode* newDst);
    void reTargetSrcOfEdge(VDGEdge* edge, VDGNode* newSrc);
    void removeVDGEdge(VDGEdge* edge);
    void removeNode(VDGNode* node);
    void moveEdgesToRep(VDGNode* node, VDGNode* rep);

    /// Internal edge addition between rep nodes (private to ensure rep node semantics)
    inline bool addEdgeInternal(VDGNode *src, VDGNode *dst, VDGEdge::VDGEdgeK kind, bool isVirtual)
    {
        assert(src != dst && "VDG edge should not be a self-loop");
        VDGEdge *edge = findEdge(src, dst);
        if (edge)
        {
            edge->addKind(kind);
            if (!isVirtual && edge->isVirtualEdge())
            {
                return updateEdgeVirtual(edge, false); 
            }
            return false;
        }
        edge = new VDGEdge(src, dst, kind, isVirtual);
        src->addOutgoingEdgeWithKind(edge);
        dst->addIncomingEdgeWithKind(edge);
        logEdgeChange("add", edge);
        return !isVirtual;
    }

    VDGEdge* findEdge(const VDGNode *src, const VDGNode *dst) const
    {
        VDGEdge edge(const_cast<VDGNode*>(src), const_cast<VDGNode*>(dst), VDGEdge::Depend, false);
        const VDGNode::VDGEdgeSetTy &edges = src->getOutEdges();
        VDGNode::VDGEdgeSetTy::const_iterator it = edges.find(&edge);
        return it == edges.end() ? nullptr : *it;
    }

    NodeID objId;                           ///< Object ID this VDG belongs to
    std::vector<VDGNode*> verVec_;          ///< version -> rep node (O(1), index = Version)
    std::vector<Version> repVec_;           ///< sub version -> rep version (0 = self-rep)
    std::vector<NodeBS> subVec_;            ///< rep version -> {all sub versions including self}
    std::vector<VDGNode*> nodeVec;          ///< O(1) node lookup by NodeID
    std::vector<bool> superNodes;           ///< superNodes[nodeId] = true if super node
    NodeID nextNodeId;                      ///< Next node ID to assign
    u32_t nodeNum;                          ///< Number of live nodes
    NodeVector updatedNodes_;               ///< Rep node IDs with pending updates
};

//===----------------------------------------------------------------------===//
// VDGSCCDetection: Standalone Tarjan SCC for VDG (solid edges only).
// Uses NodeBS with lazy per-rep allocation for sub-node tracking.
// Produces a topological order stack and per-rep sub-node sets.
//===----------------------------------------------------------------------===//
class VDGSCCDetection
{
public:
    typedef std::stack<NodeID> GNodeStack;

    explicit VDGSCCDetection(VDG* graph)
        : graph_(graph),
          counter_(0),
          capacity_(graph->getNextNodeId()),
          disc_(capacity_, 0),
          rep_(capacity_, UINT_MAX),
          inSCC_(capacity_, false),
          visited_(capacity_, false)
    {
    }

    /// Run SCC on all live super nodes
    void find()
    {
        for (auto it = graph_->begin(), eit = graph_->end(); it != eit; ++it)
        {
            NodeID id = (*it).first;
            if (!graph_->isSuperNode(id)) continue;
            if (!visited_[id])
                visit(id);
        }
    }

    /// Run SCC only from given candidate nodes
    void find(const NodeVector& candidates)
    {
        for (NodeID id : candidates)
        {
            if (!graph_->hasNodeFast(id)) continue;
            if (!graph_->isSuperNode(id)) continue;
            if (!visited_[id])
                visit(id);
        }
    }

    /// Topo order stack (top = first in topo order)
    GNodeStack& topoNodeStack() { return topoStack_; }
    const GNodeStack& topoNodeStack() const { return topoStack_; }

    /// Get rep node for a node
    NodeID repNode(NodeID n) const
    {
        return (rep_[n] != UINT_MAX) ? rep_[n] : n;
    }

    /// Get sub nodes for a rep
    const NodeBS& subNodes(NodeID repId) const
    {
        auto it = subNodes_.find(repId);
        assert(it != subNodes_.end() && "rep node should have a sub-node set!");
        return it->second;
    }

private:
    void visit(NodeID v)
    {
        ++counter_;
        disc_[v] = counter_;
        setRep(v, v);
        visited_[v] = true;

        // Iterate solid-edge successors only
        VDGNode* node = graph_->getNodeFast(v);
        for (auto ei = node->OutEdgeBegin(), eei = node->OutEdgeEnd(); ei != eei; ++ei)
        {
            VDGEdge* edge = *ei;
            if (edge->isVirtualEdge()) continue;
            NodeID w = edge->getDstID();
            if (!graph_->isSuperNode(w)) continue;

            if (!visited_[w])
                visit(w);
            if (!inSCC_[w])
            {
                NodeID r = (disc_[rep_[v]] < disc_[rep_[w]]) ? rep_[v] : rep_[w];
                setRep(v, r);
            }
        }

        if (rep_[v] == v)
        {
            inSCC_[v] = true;
            while (!sccStack_.empty())
            {
                NodeID w = sccStack_.top();
                if (disc_[w] <= disc_[v])
                    break;
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

    void setRep(NodeID n, NodeID r)
    {
        const NodeID oldRep = rep_[n];
        if (oldRep == r)
            return;

        if (oldRep != UINT_MAX)
        {
            auto oldIt = subNodes_.find(oldRep);
            if (oldIt != subNodes_.end())
            {
                oldIt->second.reset(n);
                if (oldIt->second.empty())
                    subNodes_.erase(oldIt);
            }
        }

        rep_[n] = r;
        subNodes_[r].set(n);
    }

    VDG* graph_;
    unsigned counter_;
    unsigned capacity_;
    std::vector<unsigned> disc_;       ///< Discovery counter per node
    std::vector<NodeID> rep_;          ///< Rep node ID per node
    std::vector<bool> inSCC_;          ///< Whether node is finalized in SCC
    std::vector<bool> visited_;        ///< Whether node has been visited
    Map<NodeID, NodeBS> subNodes_;         ///< Per-rep sub-node sets (lazy)
    GNodeStack sccStack_;              ///< SCC working stack
    GNodeStack topoStack_;             ///< Topo order result
};

/// VDGManager: Manages multiple VDGs (one per object) with pending update tracking
class VDGManager
{
public:
    typedef Map<NodeID, std::unique_ptr<VDG>> VDGMapTy;

    VDGManager() = default;
    ~VDGManager() = default;

    /// Get or create VDG for object
    inline VDG* getOrCreateVDG(NodeID obj)
    {
        auto it = vdgMap.find(obj);
        if (it != vdgMap.end())
            return it->second.get();
        vdgMap[obj] = std::make_unique<VDG>(obj);
        return vdgMap[obj].get();
    }

    /// Get VDG for object (assert exists)
    inline VDG* getVDG(NodeID obj)
    {
        auto it = vdgMap.find(obj);
        assert(it != vdgMap.end() && "VDG for object not found!");
        return it->second.get();
    }

    inline const VDG* getVDG(NodeID obj) const
    {
        auto it = vdgMap.find(obj);
        assert(it != vdgMap.end() && "VDG for object not found!");
        return it->second.get();
    }

    /// Try get VDG (returns nullptr if not exists)
    inline VDG* tryGetVDG(NodeID obj)
    {
        auto it = vdgMap.find(obj);
        return it != vdgMap.end() ? it->second.get() : nullptr;
    }

    inline const VDG* tryGetVDG(NodeID obj) const
    {
        auto it = vdgMap.find(obj);
        return it != vdgMap.end() ? it->second.get() : nullptr;
    }

    /// Check if VDG exists for object
    inline bool hasVDG(NodeID obj) const
    {
        return vdgMap.find(obj) != vdgMap.end();
    }

    /// Deep-copy a canonical object's VDG to a new object ID.
    /// Each object gets its own independent VDG that can evolve separately during solving.
    inline void copyVDGForObj(NodeID srcObj, NodeID dstObj)
    {
        assert(srcObj != dstObj && "VDGManager: cannot copy VDG to same object!");
        auto it = vdgMap.find(srcObj);
        assert(it != vdgMap.end() && "VDGManager: source VDG not found!");
        vdgMap[dstObj] = it->second->clone(dstObj);
    }

    /// Mark a version as updated, add obj to pending queue
    inline void markVersionUpdated(NodeID obj, Version v)
    {
        VDG* graph = getVDG(obj);
        graph->markVersionUpdated(v);
        pendingVDGs.push(obj);
    }

    /// Mark edge added and source version for propagation
    inline void markEdgeAdded(NodeID obj, Version srcV)
    {
        markVersionUpdated(obj, srcV);
    }

    /// Check if there are pending VDGs to process
    inline bool hasPendingVDGs() const
    {
        return !pendingVDGs.empty();
    }

    /// Pop next pending VDG object ID
    inline NodeID popPendingVDG()
    {
        return pendingVDGs.pop();
    }

    /// Get all VDGs (for iteration)
    inline VDGMapTy& getAllVDGs()
    {
        return vdgMap;
    }

    inline const VDGMapTy& getAllVDGs() const
    {
        return vdgMap;
    }

    /// Clear all VDGs
    inline void clear()
    {
        vdgMap.clear();
        pendingVDGs.clear();
    }

    //===--- Rep Version Helpers ---===//

    /// Get rep version for (obj, version) pair
    inline Version getRepVersion(NodeID obj, Version v) const
    {
        const VDG* graph = getVDG(obj);
        return graph->getRepVersion(v);
    }

    /// Get rep version, returns invalidVersion (0) if not found
    /// Used for remapping where non-existent versions should be removed
    inline Version getRepVersionOrInvalid(NodeID obj, Version v) const
    {
        const VDG* graph = tryGetVDG(obj);
        if (!graph || !graph->hasVersion(v)) return 0;  // invalidVersion
        return graph->getRepVersion(v);
    }

    /// Create versioned key with rep version lookup
    inline VersionedVar atRepKey(NodeID obj, Version version) const
    {
        assert(version != 0 && "VDGManager::atRepKey: trying to use an invalid version!");
        Version repV = getRepVersion(obj, version);
        return std::make_pair(obj, repV);
    }

    /// Combined hasVersion + atRepKey: returns true and sets outKey if version exists,
    /// avoiding redundant hash lookups in hot paths.
    inline bool tryAtRepKey(NodeID obj, Version version, VersionedVar &outKey) const
    {
        const VDG* graph = tryGetVDG(obj);
        if (!graph) return false;
        if (!graph->hasVersion(version)) return false;
        outKey = std::make_pair(obj, graph->getRepVersion(version));
        return true;
    }

    //===--- Statistics & Output ---===//
    
    /// Dump detailed VDG statistics (node/edge counts, distributions)
    void dumpStats() const;
    
    /// Write VDG graphs to dot files
    /// Supports per-object splitting (%o token), min/max node thresholds
    void writeToFile(const std::string& filename) const;

private:
    /// Map from object ID to its VDG
    VDGMapTy vdgMap;
    /// Queue of object IDs whose VDGs have pending updates
    FIFOWorkList<NodeID> pendingVDGs;
};

} // namespace SVF

namespace SVF
{
// Iterates node out-edges with optional virtual-edge filtering (no extra edge sets).
class VDGChildIter
{
public:
    using EdgeIter = VDGNode::const_iterator;
    using iterator_category = std::forward_iterator_tag;
    using value_type = VDGNode*;
    using difference_type = std::ptrdiff_t;
    using pointer = value_type*;
    using reference = value_type;

    VDGChildIter() : cur(), end(), skipVirtual(false) {}

    VDGChildIter(EdgeIter begin, EdgeIter end, bool skipVirtual)
        : cur(begin), end(end), skipVirtual(skipVirtual)
    {
        skipInvalid();
    }

    value_type operator*() const
    {
        assert(cur != end && "Dereferencing end iterator");
        return (*cur)->getDstNode();
    }

    VDGChildIter& operator++()
    {
        if (cur != end)
            ++cur;
        skipInvalid();
        return *this;
    }

    bool operator==(const VDGChildIter& rhs) const
    {
        return cur == rhs.cur;
    }

    bool operator!=(const VDGChildIter& rhs) const
    {
        return cur != rhs.cur;
    }

    EdgeIter getCurrent() const
    {
        return cur;
    }

private:
    EdgeIter cur;
    EdgeIter end;
    bool skipVirtual;

    void skipInvalid()
    {
        if (!skipVirtual)
            return;
        while (cur != end && (*cur)->isVirtualEdge())
            ++cur;
    }
};

template<> struct GenericGraphTraits<SVF::VDGNode*> : public GenericGraphTraits<SVF::GenericNode<SVF::VDGNode,SVF::VDGEdge>*  >
{
};

template<>
struct GenericGraphTraits<Inverse<SVF::VDGNode*> > : public GenericGraphTraits<Inverse<SVF::GenericNode<SVF::VDGNode,SVF::VDGEdge>*> >
{
};

template<>
struct GenericGraphTraits<SVF::VDG*>
{
    typedef SVF::VDG GenericGraphTy;
    typedef SVF::VDGNode NodeType;
    typedef SVF::VDGEdge EdgeType;

    using NodeRef = SVF::VDGNode*;
    using ChildIteratorType = SVF::VDGChildIter;

    static NodeType* getEntryNode(GenericGraphTy*)
    {
        return nullptr;
    }

    // Wrap VDG::const_iterator to dereference to VDGNode* (as required by GraphWriter)
    class nodes_iterator
    {
    public:
        using WrappedIter = SVF::VDG::const_iterator;
        using iterator_category = std::forward_iterator_tag;
        using value_type = SVF::VDGNode*;
        using difference_type = std::ptrdiff_t;
        using pointer = value_type*;
        using reference = value_type;

        nodes_iterator() = default;
        nodes_iterator(WrappedIter it) : it_(it) {}

        value_type operator*() const { return (*it_).second; }
        nodes_iterator& operator++() { ++it_; return *this; }
        nodes_iterator operator++(int) { auto tmp = *this; ++it_; return tmp; }
        bool operator==(const nodes_iterator& o) const { return it_ == o.it_; }
        bool operator!=(const nodes_iterator& o) const { return it_ != o.it_; }

    private:
        WrappedIter it_;
    };

    static nodes_iterator nodes_begin(GenericGraphTy *G)
    {
        return nodes_iterator(G->begin());
    }
    static nodes_iterator nodes_end(GenericGraphTy *G)
    {
        return nodes_iterator(G->end());
    }

    static unsigned graphSize(GenericGraphTy* G)
    {
        return G->getTotalNodeNum();
    }

    static inline unsigned getNodeID(NodeType* N)
    {
        return N->getId();
    }

    static NodeType* getNode(GenericGraphTy *G, SVF::NodeID id)
    {
        return G->getNodeFast(id);
    }

    static inline ChildIteratorType child_begin(const SVF::VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeBegin(), N->OutEdgeEnd(), false);
    }
    static inline ChildIteratorType child_end(const SVF::VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeEnd(), N->OutEdgeEnd(), false);
    }
    static inline ChildIteratorType direct_child_begin(const SVF::VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeBegin(), N->OutEdgeEnd(), true);
    }
    static inline ChildIteratorType direct_child_end(const SVF::VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeEnd(), N->OutEdgeEnd(), true);
    }
};
} // namespace SVF

#endif /* VDG_H_ */
