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
#include <string>

namespace SVF
{

class VDGNode;

typedef GenericEdge<VDGNode> GenericVDGEdgeTy;

class VDGEdge : public GenericVDGEdgeTy
{
public:
    enum VDGEdgeK
    {
        Reliance = 1,
        Store = 2
    };

    typedef GenericNode<VDGNode, VDGEdge>::GEdgeSetTy VDGEdgeSetTy;

    VDGEdge(VDGNode *src, VDGNode *dst, VDGEdgeK kind)
        : GenericVDGEdgeTy(src, dst, kind)
    {
    }

    ~VDGEdge() override = default;

    inline VDGEdgeK getVDGEdgeKind() const
    {
        return static_cast<VDGEdgeK>(getEdgeKind());
    }

    inline bool isStoreEdge() const
    {
        return getVDGEdgeKind() == Store;
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

    bool addIncomingEdgeWithKind(VDGEdge* inEdge, VDGEdge::VDGEdgeK kind)
    {
        bool added1 = GenericVDGNodeTy::addIncomingEdge(inEdge);
        bool added2 = (kind == VDGEdge::Store ? storeInEdges : relianceInEdges).insert(inEdge).second;
        return added1 && added2;
    }

    bool addOutgoingEdgeWithKind(VDGEdge* outEdge, VDGEdge::VDGEdgeK kind)
    {
        bool added1 = GenericVDGNodeTy::addOutgoingEdge(outEdge);
        bool added2 = (kind == VDGEdge::Store ? storeOutEdges : relianceOutEdges).insert(outEdge).second;
        return added1 && added2;
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
    VersionedVar var;
    bool loadConsume;
    bool storeYield;
    VDGEdgeSetTy relianceInEdges;
    VDGEdgeSetTy relianceOutEdges;
    VDGEdgeSetTy storeInEdges;
    VDGEdgeSetTy storeOutEdges;
};

class VDG : public GenericGraph<VDGNode, VDGEdge>
{
public:
    typedef Map<VersionedVar, VDGNode*> VDGNodeMapTy;

    VDG() : nextNodeId(0)
    {
    }

    ~VDG() override = default;

    static void setDetectSE(bool flag);
    static bool detectSE();

    void dump(const std::string& filename) const;
    void view() const;

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

    VDGEdge* addVDGEdge(VDGNode *src, VDGNode *dst, VDGEdge::VDGEdgeK kind)
    {
        if (VDGEdge *edge = findEdge(src, dst, kind))
            return edge;

        VDGEdge *edge = new VDGEdge(src, dst, kind);
        src->addOutgoingEdgeWithKind(edge, kind);
        dst->addIncomingEdgeWithKind(edge, kind);
        return edge;
    }

private:
    VDGEdge* findEdge(const VDGNode *src, const VDGNode *dst, VDGEdge::VDGEdgeK kind) const
    {
        for (VDGEdge *edge : src->getOutEdges())
        {
            if (edge->getDstNode() == dst && edge->getVDGEdgeKind() == kind)
                return edge;
        }
        return nullptr;
    }

    VDGNodeMapTy nodeMap;
    NodeID nextNodeId;
};

} // namespace SVF

#endif /* VDG_H_ */
