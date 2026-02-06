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
#include <cassert>
#include <iterator>
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

    VDGNode(NodeID id, NodeID obj, Version ver, bool loadConsume = false, bool storeYield = false,
            GNodeK k = VDGNodeKd)
        : GenericVDGNodeTy(id, k),
          var(std::make_pair(obj, ver)),
          loadConsume(loadConsume),
          storeYield(storeYield)
    {
    }

    ~VDGNode() override = default;

    inline NodeID getObject() const
    {
        return var.first;
    }

    inline Version getVersion() const
    {
        return var.second;
    }

    inline const VersionedVar& getVersionedVar() const
    {
        return var;
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

    VersionedVar var;
    bool loadConsume;
    bool storeYield;
};

class VDG : public GenericGraph<VDGNode, VDGEdge>
{
public:
    typedef Map<VersionedVar, VDGNode*> VDGNodeMapTy;
    typedef Map<NodeID, NodeID> NodeToRepMap;
    typedef Map<NodeID, NodeBS> NodeToSubsMap;

    VDG() : nextNodeId(0)
    {
    }

    ~VDG() override = default;

    static void setDetectVE(bool flag);
    static bool detectVE();

    void dump(const std::string& filename);
    void view();
    void mergeNodesIntoRep(const NodeBS& nodes, VDGNode* rep);
    std::vector<NodeID> sccMergeSolidEdges();
    void pruneUnreachableToLoadConsume();
    void pruneUnreachableFromStoreYield();
    void reduceByStableDstReachability();
    void reduceByStableSrcReachability();
    void chainContraction();
    void transitiveRedundancyElimination();

    VDGNode* getOrAddNode(NodeID obj, Version ver, bool loadConsume = false, bool storeYield = false)
    {
        const VersionedVar key = std::make_pair(obj, ver);
        VDGNodeMapTy::iterator it = nodeMap.find(key);
        if (it != nodeMap.end())
        {
            if (loadConsume) it->second->setLoadConsume(true);
            if (storeYield) it->second->setStoreYield(true);
            return it->second;
        }

        VDGNode *node = new VDGNode(nextNodeId++, obj, ver, loadConsume, storeYield);
        addGNode(node->getId(), node);
        nodeMap[key] = node;
        return node;
    }

    VDGNode* getNode(const VersionedVar &var) const
    {
        VDGNodeMapTy::const_iterator it = nodeMap.find(var);
        return it == nodeMap.end() ? nullptr : it->second;
    }

    inline const VDGNodeMapTy& getNodeMap() const
    {
        return nodeMap;
    }

    // return true if a non-virtual edge is added or an existing virtual edge is updated to non-virtual
    bool addVDGEdge(VDGNode *src, VDGNode *dst, VDGEdge::VDGEdgeK kind, bool isVirtual)
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

    inline NodeID sccRepNode(NodeID id) const
    {
        NodeToRepMap::const_iterator it = nodeToRepMap.find(id);
        return it == nodeToRepMap.end() ? id : it->second;
    }

    inline NodeBS& sccSubNodes(NodeID id)
    {
        nodeToSubsMap[id].set(id);
        return nodeToSubsMap[id];
    }

    inline void setRep(NodeID node, NodeID rep)
    {
        nodeToRepMap[node] = rep;
    }

    inline void setSubs(NodeID node, const NodeBS& subs)
    {
        nodeToSubsMap[node] |= subs;
    }

    inline void resetSubs(NodeID node)
    {
        nodeToSubsMap.erase(node);
    }

    // with small side effect
    inline NodeBS& getSubs(NodeID node)
    {
        NodeBS &subs = nodeToSubsMap[node];
        subs.set(node);
        return subs;
    }

    inline NodeID getRep(NodeID node) const
    {
        NodeToRepMap::const_iterator it = nodeToRepMap.find(node);
        return it == nodeToRepMap.end() ? node : it->second;
    }

    inline bool isSuperNode(NodeID node) const
    {
        return getRep(node) == node;
    }

    inline void resetRep(NodeID node)
    {
        nodeToRepMap.erase(node);
    }

    // remove node excluding its edges
    inline void deleteNode(NodeID nodeId)
    {
        VDGNode* node = getGNode(nodeId);
        assert(node && "node not found in VDG!");
        nodeMap.erase(node->getVersionedVar());
        resetRep(nodeId);
        resetSubs(nodeId);
        removeGNode(node);
    }

private:
    static void logEdgeChange(const char* tag, const VDGEdge* edge);
    static void logEdgeMembership(const char* tag, const VDGNode* node, const VDGEdge* edge);
    static bool updateEdgeVirtual(VDGEdge* edge, bool isVirtual);
    void reTargetDstOfEdge(VDGEdge* edge, VDGNode* newDst);
    void reTargetSrcOfEdge(VDGEdge* edge, VDGNode* newSrc);
    void removeVDGEdge(VDGEdge* edge);
    void removeNode(VDGNode* node);
    void moveEdgesToRep(VDGNode* node, VDGNode* rep);

    VDGEdge* findEdge(const VDGNode *src, const VDGNode *dst) const
    {
        VDGEdge edge(const_cast<VDGNode*>(src), const_cast<VDGNode*>(dst), VDGEdge::Depend, false);
        const VDGNode::VDGEdgeSetTy &edges = src->getOutEdges();
        VDGNode::VDGEdgeSetTy::const_iterator it = edges.find(&edge);
        return it == edges.end() ? nullptr : *it;
    }

    VDGNodeMapTy nodeMap;
    NodeToRepMap nodeToRepMap;
    NodeToSubsMap nodeToSubsMap;
    NodeID nextNodeId;
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
