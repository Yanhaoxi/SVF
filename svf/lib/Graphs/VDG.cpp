//===- VDG.cpp -- Version Dependency Graph ---------------------------------//
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
 * VDG.cpp
 *
 *  Created on: Jan 31, 2026
 *      Author: Codex
 */

#include "Graphs/VDG.h"
#include "Graphs/GraphPrinter.h"
#include "Util/WorkList.h"
#include "Graphs/SCC.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include <sstream>
#include <vector>

using namespace SVF;

VDGNode::iterator VDGNode::directOutEdgeBegin()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeBegin();
    return solidOutEdges.begin();
}

VDGNode::iterator VDGNode::directOutEdgeEnd()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeEnd();
    return solidOutEdges.end();
}

VDGNode::iterator VDGNode::directInEdgeBegin()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeBegin();
    return solidInEdges.begin();
}

VDGNode::iterator VDGNode::directInEdgeEnd()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeEnd();
    return solidInEdges.end();
}

VDGNode::const_iterator VDGNode::directOutEdgeBegin() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeBegin();
    return solidOutEdges.begin();
}

VDGNode::const_iterator VDGNode::directOutEdgeEnd() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeEnd();
    return solidOutEdges.end();
}

VDGNode::const_iterator VDGNode::directInEdgeBegin() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeBegin();
    return solidInEdges.begin();
}

VDGNode::const_iterator VDGNode::directInEdgeEnd() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeEnd();
    return solidInEdges.end();
}

void VDG::setDetectVE(bool flag)
{
    Options::DetectVE.setValue(flag);
}

bool VDG::detectVE()
{
    return Options::DetectVE();
}

void VDG::dump(const std::string& filename)
{
    std::string name = filename;
    if (name.size() >= 4 && name.substr(name.size() - 4) == ".dot")
        name = name.substr(0, name.size() - 4);
    GraphPrinter::WriteGraphToFile(SVFUtil::outs(), name, this);
}

void VDG::view()
{
    SVF::ViewGraph(this, "Version Dependency Graph");
}

void VDG::reTargetDstOfEdge(VDGEdge* edge, VDGNode* newDst)
{
    VDGNode* src = edge->getSrcNode();
    VDGEdge::VDGEdgeK kind = edge->getVDGEdgeKind();
    bool isVirtual = edge->isVirtualEdge();
    removeVDGEdge(edge);
    addVDGEdge(src, newDst, kind, isVirtual);
}

void VDG::reTargetSrcOfEdge(VDGEdge* edge, VDGNode* newSrc)
{
    VDGNode* dst = edge->getDstNode();
    VDGEdge::VDGEdgeK kind = edge->getVDGEdgeKind();
    bool isVirtual = edge->isVirtualEdge();
    removeVDGEdge(edge);
    addVDGEdge(newSrc, dst, kind, isVirtual);
}

void VDG::removeVDGEdge(VDGEdge* edge)
{
    VDGNode* src = edge->getSrcNode();
    VDGNode* dst = edge->getDstNode();
    src->removeOutgoingEdgeWithKind(edge);
    dst->removeIncomingEdgeWithKind(edge);
    delete edge;
}

void VDG::moveEdgesToRepNode(VDGNode* node, VDGNode* rep)
{
    std::vector<VDGEdge*> inSccEdges;
    std::vector<VDGEdge*> inNonSccEdges;
    for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
    {
        VDGEdge* edge = *it;
        if (sccRepNode(edge->getSrcID()) != rep->getId())
            inNonSccEdges.push_back(edge);
        else
            inSccEdges.push_back(edge);
    }
    for (VDGEdge* edge : inNonSccEdges)
    {
        reTargetDstOfEdge(edge, rep);
    }
    for (VDGEdge* edge : inSccEdges)
    {
        removeVDGEdge(edge);
    }

    std::vector<VDGEdge*> outSccEdges;
    std::vector<VDGEdge*> outNonSccEdges;
    for (VDGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it != eit; ++it)
    {
        VDGEdge* edge = *it;
        if (sccRepNode(edge->getDstID()) != rep->getId())
            outNonSccEdges.push_back(edge);
        else
            outSccEdges.push_back(edge);
    }
    for (VDGEdge* edge : outNonSccEdges)
    {
        reTargetSrcOfEdge(edge, rep);
    }
    for (VDGEdge* edge : outSccEdges)
    {
        removeVDGEdge(edge);
    }
}
// must scc merge 
void VDG::sccMergeSolidEdges()
{
    const bool oldDetect = detectVE();
    setDetectVE(false);

    SCCDetection<VDG*> scc(this);
    scc.find();

    setDetectVE(oldDetect);

    std::vector<NodeID> reps;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID id = it->first;
        if (scc.repNode(id) == id)
            reps.push_back(id);
    }

    for (NodeID repId : reps)
    {
        const NodeBS &subs = scc.subNodes(repId);
        if (subs.count() <= 1) continue;

        VDGNode* rep = getGNode(repId);
        nodeToSubsMap[repId].set(repId);

        for (const NodeID subId : subs)
        {
            if (subId == repId) continue;
            VDGNode* sub = getGNode(subId);
            rep->setLoadConsume(sub->isLoadConsume());
            rep->setStoreYield(sub->isStoreYield());
            setRep(subId, repId);
            nodeToSubsMap[repId].set(subId);
        }

        for (const NodeID subId : subs)
        {
            if (subId == repId) continue;
            VDGNode* sub = getGNode(subId);
            moveEdgesToRepNode(sub, rep);
        }
    }
}

// non-reachable nodes to load-consume nodes are removed
void VDG::pruneUnreachableToLoadConsume()
{
    NodeBS reachable;
    std::vector<NodeID> worklist;

    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID id = it->first;
        VDGNode* node = it->second;
        if (node->isLoadConsume())
        {
            reachable.set(id);
            worklist.push_back(id);
        }
    }

    while (!worklist.empty())
    {
        const NodeID id = worklist.back();
        worklist.pop_back();
        VDGNode* node = getGNode(id);
        for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
        {
            const NodeID srcId = (*it)->getSrcID();
            if (!reachable.test(srcId))
            {
                reachable.set(srcId);
                worklist.push_back(srcId);
            }
        }
    }

    std::vector<VDGNode*> toRemove;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        if (!reachable.test(it->first))
            toRemove.push_back(it->second);
    }

    for (VDGNode* node : toRemove)
    {
        std::vector<VDGEdge*> edges;
        for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
            edges.push_back(*it);
        for (VDGEdge* edge : edges)
            removeVDGEdge(edge);

        edges.clear();
        for (VDGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it != eit; ++it)
            edges.push_back(*it);
        for (VDGEdge* edge : edges)
            removeVDGEdge(edge);

        nodeMap.erase(node->getVersionedVar());
        nodeToRepMap.erase(node->getId());
        nodeToSubsMap.erase(node->getId());
        for (auto &entry : nodeToSubsMap)
            entry.second.reset(node->getId());
        removeGNode(node);
    }
}



namespace SVF
{

template<>
struct DOTGraphTraits<VDG*> : public DefaultDOTGraphTraits
{
    typedef VDGNode NodeType;

    DOTGraphTraits(bool isSimple = false)
        : DefaultDOTGraphTraits(isSimple)
    {
    }

    static std::string getGraphName(VDG*)
    {
        return "VDG";
    }

    static bool isNodeHidden(NodeType *node, VDG *graph)
    {
        return graph && !graph->isSuperNode(node->getId());
    }

    static std::string getNodeLabel(NodeType *node, VDG*)
    {
        std::stringstream raw;
        raw << "o=" << node->getObject() << "\\nv=" << node->getVersion();
        return raw.str();
    }

    static std::string getNodeAttributes(NodeType *node, VDG*)
    {
        const bool loadConsume = node->isLoadConsume();
        const bool storeYield = node->isStoreYield();

        std::string attrs;
        attrs += loadConsume ? "shape=box" : "shape=ellipse";
        attrs += ", style=filled";
        attrs += storeYield ? ", fillcolor=mistyrose" : ", fillcolor=white";
        return attrs;
    }

    template<class EdgeIter>
    static std::string getEdgeAttributes(NodeType*, EdgeIter EI, VDG*)
    {
        VDGEdge* edge = *(EI.getCurrent());
        if (edge && edge->isVirtualEdge())
            return "style=dashed";
        return "";
    }
};

} // namespace SVF
