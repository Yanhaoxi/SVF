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
#include <string>

namespace SVF
{

class VDGNode;

typedef GenericEdge<VDGNode> GenericVDGEdgeTy;

class VDGEdge : public GenericVDGEdgeTy
{
public:
    // virtual => may / flow solid => must flow
    // kind => src to dst edge kind (from direct dependency/store flow/indirect call)
    enum VDGEdgeK
    {
        Depend = 1,
        StoreFlow = 2,
        IndCallFlow = 3
    };

    typedef GenericNode<VDGNode, VDGEdge>::GEdgeSetTy VDGEdgeSetTy;
    typedef struct equalGEdge
    {
        bool operator()(const VDGEdge* lhs, const VDGEdge* rhs) const
        {
            const GEdgeFlag lhsFlag = lhs->getEdgeKindWithoutMask() & VirtualEdgeFlag;
            const GEdgeFlag rhsFlag = rhs->getEdgeKindWithoutMask() & VirtualEdgeFlag;
            if (lhsFlag != rhsFlag)
                return lhsFlag < rhsFlag;
            if (lhs->getSrcID() != rhs->getSrcID())
                return lhs->getSrcID() < rhs->getSrcID();
            return lhs->getDstID() < rhs->getDstID();
        }
    } equalGEdge;

    VDGEdge(VDGNode *src, VDGNode *dst, VDGEdgeK kind, bool isVirtual = false)
        : GenericVDGEdgeTy(src, dst,
                           (static_cast<GEdgeFlag>(kind) & KindMask)
                           | (isVirtual ? VirtualEdgeFlag : 0))
    {
    }

    ~VDGEdge() override = default;

    inline VDGEdgeK getVDGEdgeKind() const
    {
        return static_cast<VDGEdgeK>(getEdgeKind() & KindMask);
    }

    inline bool isStoreEdge() const
    {
        return getVDGEdgeKind() == StoreFlow;
    }

    inline bool isVirtualEdge() const
    {
        return (getEdgeKindWithoutMask() & VirtualEdgeFlag) != 0;
    }

protected:
    static constexpr GEdgeFlag VirtualEdgeFlag = (1ULL << (EdgeKindMaskBits - 1));
    static constexpr GEdgeFlag KindMask = VirtualEdgeFlag - 1;
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

    bool addIncomingEdgeWithKind(VDGEdge* inEdge)
    {
        const bool isVirtual = inEdge->isVirtualEdge();
        bool added1 = GenericVDGNodeTy::addIncomingEdge(inEdge);
        bool added2 = (isVirtual ? virtualInEdges : solidInEdges).insert(inEdge).second;
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
    }

    bool addOutgoingEdgeWithKind(VDGEdge* outEdge)
    {
        const bool isVirtual = outEdge->isVirtualEdge();
        bool added1 = GenericVDGNodeTy::addOutgoingEdge(outEdge);
        bool added2 = (isVirtual ? virtualOutEdges : solidOutEdges).insert(outEdge).second;
        bool both_added = added1 & added2;
        assert(both_added && "edge not added, duplicated adding!!");
        return both_added;
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

    inline const VDGEdgeSetTy& getSolidOutEdges() const
    {
        return solidOutEdges;
    }

    inline const VDGEdgeSetTy& getVirtualOutEdges() const
    {
        return virtualOutEdges;
    }

private:
    VersionedVar var;
    bool loadConsume;
    bool storeYield;
    VDGEdgeSetTy solidInEdges;
    VDGEdgeSetTy solidOutEdges;
    VDGEdgeSetTy virtualInEdges;
    VDGEdgeSetTy virtualOutEdges;
};

class VDG : public GenericGraph<VDGNode, VDGEdge>
{
public:
    typedef Map<VersionedVar, VDGNode*> VDGNodeMapTy;

    VDG() : nextNodeId(0)
    {
    }

    ~VDG() override = default;

    static void setDetectVE(bool flag);
    static bool detectVE();

    void dump(const std::string& filename);
    void view();

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

    VDGEdge* addVDGEdge(VDGNode *src, VDGNode *dst, VDGEdge::VDGEdgeK kind, bool isVirtual)
    {
        if (VDGEdge *edge = findEdge(src, dst, kind, isVirtual))
            return edge;

        VDGEdge *edge = new VDGEdge(src, dst, kind, isVirtual);
        src->addOutgoingEdgeWithKind(edge);
        dst->addIncomingEdgeWithKind(edge);
        return edge;
    }

private:
    VDGEdge* findEdge(const VDGNode *src, const VDGNode *dst, VDGEdge::VDGEdgeK kind, bool isVirtual) const
    {
        VDGEdge edge(const_cast<VDGNode*>(src), const_cast<VDGNode*>(dst), kind, isVirtual);
        const VDGNode::VDGEdgeSetTy &edges = isVirtual
            ? src->getVirtualOutEdges()
            : src->getSolidOutEdges();
        VDGNode::VDGEdgeSetTy::const_iterator it = edges.find(&edge);
        return it == edges.end() ? nullptr : *it;
    }

    VDGNodeMapTy nodeMap;
    NodeID nextNodeId;
};

} // namespace SVF

namespace SVF
{
template<> struct GenericGraphTraits<SVF::VDGNode*> : public GenericGraphTraits<SVF::GenericNode<SVF::VDGNode,SVF::VDGEdge>*  >
{
};

template<>
struct GenericGraphTraits<Inverse<SVF::VDGNode*> > : public GenericGraphTraits<Inverse<SVF::GenericNode<SVF::VDGNode,SVF::VDGEdge>* > >
{
};

template<> struct GenericGraphTraits<SVF::VDG*> : public GenericGraphTraits<SVF::GenericGraph<SVF::VDGNode,SVF::VDGEdge>* >
{
    typedef SVF::VDGNode* NodeRef;
};
} // namespace SVF

#endif /* VDG_H_ */
