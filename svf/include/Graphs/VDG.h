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

//===----------------------------------------------------------------------===//
// Type Aliases for VDG
//===----------------------------------------------------------------------===//
typedef Map<Version, Version> VersionRepMap;       ///< sub version -> rep version
typedef Map<Version, VersionSet> VersionSubMap;    ///< rep version -> {all sub versions}
typedef Map<Version, VDGNode*> VersionToNodeMap;   ///< version -> VDGNode* (always rep after merge)

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

    VDGEdgeSetTy::iterator directOutEdgeBegin() override;
    VDGEdgeSetTy::iterator directOutEdgeEnd() override;
    VDGEdgeSetTy::iterator directInEdgeBegin() override;
    VDGEdgeSetTy::iterator directInEdgeEnd() override;
    VDGEdgeSetTy::const_iterator directOutEdgeBegin() const override;
    VDGEdgeSetTy::const_iterator directOutEdgeEnd() const override;
    VDGEdgeSetTy::const_iterator directInEdgeBegin() const override;
    VDGEdgeSetTy::const_iterator directInEdgeEnd() const override;

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
};

class VDG : public GenericGraph<VDGNode, VDGEdge>
{
public:
    /// Callback type for version propagation: (srcVersion, dstVersion) -> bool (changed)
    typedef std::function<bool(Version, Version)> PropagateCallback;
    /// Callback type for notifying statement reliance: (version) -> void
    typedef std::function<void(Version)> StmtRelianceCallback;

    explicit VDG(NodeID obj) : objId(obj), nextNodeId(0)
    {
    }

    ~VDG() override = default;

    static void setDetectVE(bool flag);
    static bool detectVE();

    /// Get the object ID this VDG belongs to
    inline NodeID getObjId() const { return objId; }

    void dump(const std::string& filename);
    void view();
    void mergeVersionsIntoRep(const VersionSet& versions, Version repVer);
    void pruneUnreachableToLoadConsume();
    void pruneUnreachableFromStoreYield();
    void reduceByStableDstReachability();
    void reduceByStableSrcReachability();
    void chainContraction();
    void transitiveRedundancyElimination();

    /// Mark a version as updated (stores rep node ID)
    inline void markVersionUpdated(Version v)
    {
        VDGNode* node = getNode(v);  // versionMap already returns rep node
        updatedNodes.insert(node->getId());
    }

    /// Clear all update markers after propagation
    inline void clearUpdateMarkers()
    {
        updatedNodes.clear();
    }

    /// Check if there are any pending updates
    inline bool hasPendingUpdates() const
    {
        return !updatedNodes.empty();
    }

    /// Get updated node IDs set
    inline const NodeSet& getUpdatedNodes() const
    {
        return updatedNodes;
    }

    /// SCC merge on solid edges and compute topological order
    /// @param candidates: if non-empty, only traverse from these node IDs; otherwise traverse all
    /// @return topological order of SCC rep node IDs
    NodeVector sccMergeSolidEdges(NodeSet candidates = NodeSet());

    //===--- Version Propagation API ---===//

    /// Propagate points-to along solid edges in topological order
    /// @param propagate: callback(srcVersion, dstVersion) returns true if pts changed
    /// @param onVersionChanged: callback(version) called when a version's pts changes
    void propagateInTopoOrder(PropagateCallback propagate, StmtRelianceCallback onVersionChanged);

    //===--- Node Operations ---===//

    VDGNode* getOrAddNode(Version ver, bool loadConsume = false, bool storeYield = false)
    {
        auto it = versionMap.find(ver);
        if (it != versionMap.end())
        {
            if (loadConsume) it->second->setLoadConsume(true);
            if (storeYield) it->second->setStoreYield(true);
            return it->second;
        }

        VDGNode *node = new VDGNode(nextNodeId++, ver, loadConsume, storeYield);
        addGNode(node->getId(), node);
        versionMap[ver] = node;
        
        // Initialize in subMap: each new version is its own rep with itself as sole sub
        subMap[ver].insert(ver);
        
        // Expand superNodes vector if needed and mark as super
        if (node->getId() >= superNodes.size())
            superNodes.resize(node->getId() + 1, false);
        superNodes[node->getId()] = true;
        
        return node;
    }

    /// Get node by version (always returns rep node after merge)
    inline VDGNode* getNode(Version ver)
    {
        auto it = versionMap.find(ver);
        assert(it != versionMap.end() && "version not found in graph!");
        return it->second;
    }

    inline const VDGNode* getNode(Version ver) const
    {
        auto it = versionMap.find(ver);
        assert(it != versionMap.end() && "version not found in graph!");
        return it->second;
    }

    /// Try get node (returns nullptr if not exists)
    inline VDGNode* tryGetNode(Version ver)
    {
        auto it = versionMap.find(ver);
        return it != versionMap.end() ? it->second : nullptr;
    }

    inline bool hasVersion(Version ver) const
    {
        return versionMap.find(ver) != versionMap.end();
    }

    inline const VersionToNodeMap& getVersionMap() const
    {
        return versionMap;
    }

    //===--- Rep/Sub Version Management ---===//

    /// Get rep version (returns self if already rep)
    inline Version getRepVersion(Version v) const
    {
        auto it = repMap.find(v);
        return it != repMap.end() ? it->second : v;
    }

    /// Check if version is a rep version
    inline bool isRepVersion(Version v) const
    {
        return repMap.find(v) == repMap.end();
    }

    /// Get all sub versions for a rep (including self)
    inline const VersionSet& getSubVersions(Version repV) const
    {
        auto it = subMap.find(repV);
        assert(it != subMap.end() && "not a rep version!");
        return it->second;
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

    /// Add edge between versions (auto-converts to rep versions via getNode)
    /// Returns true if a new solid edge is added or virtual edge becomes solid
    /// This is the only public edge API to ensure rep node semantics
    inline bool addEdge(Version srcV, Version dstV, VDGEdge::VDGEdgeK kind, bool isVirtual)
    {
        VDGNode* src = getNode(srcV);  // getNode returns rep node via versionMap
        VDGNode* dst = getNode(dstV);
        if (src == dst) return false;  // No self-loop
        return addEdgeInternal(src, dst, kind, isVirtual);
    }

    /// Delete node from graph by NodeID
    inline void deleteNode(NodeID nodeId)
    {
        VDGNode* node = getGNode(nodeId);
        assert(node && "node not found in VDG!");
        superNodes[nodeId] = false;
        removeGNode(node);
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
    VersionToNodeMap versionMap;            ///< version -> rep node (after merge, all point to rep)
    VersionRepMap repMap;                   ///< sub version -> rep version
    VersionSubMap subMap;                   ///< rep version -> {all sub versions including self}
    std::vector<bool> superNodes;           ///< superNodes[nodeId] = true if super node
    NodeID nextNodeId;                      ///< Next node ID to assign
    NodeSet updatedNodes;                   ///< Rep node IDs with pending updates
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

    /// Mark a version as updated, add obj to pending queue if not already there
    inline void markVersionUpdated(NodeID obj, Version v)
    {
        VDG* graph = getVDG(obj);        
        graph->markVersionUpdated(v);
        pendingVDGs.push(obj);
    }

    /// Mark edge added and source version for propagation
    /// Note: This is called when a new solid edge is added at runtime (e.g., indirect call)
    inline void markEdgeAdded(NodeID obj, Version srcV)
    {
        VDG* graph = getVDG(obj);
        graph->markVersionUpdated(srcV);
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
        return graph->getNode(v)->getVersion();
    }

    /// Create versioned key with rep version lookup
    inline VersionedVar atRepKey(NodeID obj, Version version) const
    {
        assert(version != 0 && "VDGManager::atRepKey: trying to use an invalid version!");
        Version repV = getRepVersion(obj, version);
        return std::make_pair(obj, repV);
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
struct GenericGraphTraits<Inverse<SVF::VDGNode*> > : public GenericGraphTraits<Inverse<SVF::GenericNode<SVF::VDGNode,SVF::VDGEdge>* > >
{
};

template<> struct GenericGraphTraits<SVF::VDG*> : public GenericGraphTraits<SVF::GenericGraph<SVF::VDGNode,SVF::VDGEdge>* >
{
    using NodeRef = SVF::VDGNode*;
    using ChildIteratorType = VDGChildIter;

    static inline ChildIteratorType child_begin(const VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeBegin(), N->OutEdgeEnd(), false);
    }
    static inline ChildIteratorType child_end(const VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeEnd(), N->OutEdgeEnd(), false);
    }
    static inline ChildIteratorType direct_child_begin(const VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeBegin(), N->OutEdgeEnd(), !SVF::VDG::detectVE());
    }
    static inline ChildIteratorType direct_child_end(const VDGNode* N)
    {
        return ChildIteratorType(N->OutEdgeEnd(), N->OutEdgeEnd(), !SVF::VDG::detectVE());
    }
};
} // namespace SVF

#endif /* VDG_H_ */
