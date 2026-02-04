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
#include <cassert>
#include <functional>
#include <unordered_map>
#include <unordered_set>
#include <sstream>
#include <vector>

using namespace SVF;

// #define VDG_EDGE_DEBUG 1
#ifndef VDG_EDGE_DEBUG
#define VDG_EDGE_DEBUG 0
#endif

VDGNode::iterator VDGNode::directOutEdgeBegin()
{
    return GenericVDGNodeTy::OutEdgeBegin();
}

VDGNode::iterator VDGNode::directOutEdgeEnd()
{
    return GenericVDGNodeTy::OutEdgeEnd();
}

VDGNode::iterator VDGNode::directInEdgeBegin()
{
    return GenericVDGNodeTy::InEdgeBegin();
}

VDGNode::iterator VDGNode::directInEdgeEnd()
{
    return GenericVDGNodeTy::InEdgeEnd();
}

VDGNode::const_iterator VDGNode::directOutEdgeBegin() const
{
    return GenericVDGNodeTy::OutEdgeBegin();
}

VDGNode::const_iterator VDGNode::directOutEdgeEnd() const
{
    return GenericVDGNodeTy::OutEdgeEnd();
}

VDGNode::const_iterator VDGNode::directInEdgeBegin() const
{
    return GenericVDGNodeTy::InEdgeBegin();
}

VDGNode::const_iterator VDGNode::directInEdgeEnd() const
{
    return GenericVDGNodeTy::InEdgeEnd();
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

inline void VDG::logEdgeChange(const char* tag, const VDGEdge* edge)
{
#if VDG_EDGE_DEBUG
    if (edge == nullptr)
        return;
    const VDGNode* src = edge->getSrcNode();
    const VDGNode* dst = edge->getDstNode();
    SVFUtil::outs() << "[VDG] " << tag
                    << " (" << src->getObject() << "," << src->getVersion() << ")"
                    << " -> (" << dst->getObject() << "," << dst->getVersion() << ")"
                    << " kind=" << static_cast<unsigned>(edge->getVDGEdgeKind())
                    << " virtual=" << edge->isVirtualEdge() << "\n";
#else
    (void)tag;
    (void)edge;
#endif
}

inline void VDG::logEdgeMembership(const char* tag, const VDGNode* node, const VDGEdge* edge)
{
#if VDG_EDGE_DEBUG
    if (node == nullptr || edge == nullptr)
        return;
    const bool inInEdges = node->getInEdges().find(const_cast<VDGEdge*>(edge)) != node->getInEdges().end();
    
    const bool inOutEdges = node->getOutEdges().find(const_cast<VDGEdge*>(edge)) != node->getOutEdges().end();
    SVFUtil::outs() << "[VDG] " << tag
                    << " node(" << node->getObject() << "," << node->getVersion()
                    << ",id=" << node->getId() << ")"
                    << " edge(" << edge->getSrcID() << "->" << edge->getDstID() << ")"
                    << " in=" << inInEdges << " out=" << inOutEdges << "\n";
#else
    (void)tag;
    (void)node;
    (void)edge;
#endif
}

void VDG::updateEdgeVirtual(VDGEdge* edge, bool isVirtual)
{
    if (edge == nullptr || edge->isVirtualEdge() == isVirtual)
        return;
    edge->setVirtual(isVirtual);
}

void VDG::reTargetDstOfEdge(VDGEdge* edge, VDGNode* newDst)
{
    VDGNode* src = edge->getSrcNode();
    if (src == newDst)
    {
        removeVDGEdge(edge);
        return;
    }
    VDGEdge::VDGEdgeK kind = edge->getVDGEdgeKind();
    bool isVirtual = edge->isVirtualEdge();
    removeVDGEdge(edge);
    addVDGEdge(src, newDst, kind, isVirtual);
}

void VDG::reTargetSrcOfEdge(VDGEdge* edge, VDGNode* newSrc)
{
    VDGNode* dst = edge->getDstNode();
    if (dst == newSrc)
    {
        removeVDGEdge(edge);
        return;
    }
    VDGEdge::VDGEdgeK kind = edge->getVDGEdgeKind();
    bool isVirtual = edge->isVirtualEdge();
    removeVDGEdge(edge);
    addVDGEdge(newSrc, dst, kind, isVirtual);
}

void VDG::removeVDGEdge(VDGEdge* edge)
{
    assert(edge && "VDG edge to be removed is null!");
    VDGNode* src = edge->getSrcNode();
    VDGNode* dst = edge->getDstNode();
    VDGEdge* found = findEdge(src, dst);
    assert(found != nullptr && "can not find the edge to be removed");
    logEdgeChange("del", found);
    src->removeOutgoingEdgeWithKind(found);
    dst->removeIncomingEdgeWithKind(found);
    delete found;
}

void VDG::removeNode(VDGNode* node)
{
    assert(node && "VDG node to be removed is null!");
    const NodeID repId = node->getId();
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

    NodeBS subs = getSubs(repId);
    // assume sub has no edges
    for (const NodeID subId : subs)
        deleteNode(subId);
}

void VDG::moveEdgesToRep(VDGNode* node, VDGNode* rep)
{
    NodeID repId = getRep(rep->getId());
    rep = getGNode(repId);
    assert(rep && "rep node not found in VDG!");
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

void VDG::mergeNodesIntoRep(const NodeBS& nodes, VDGNode* rep)
{
    const NodeID repId = getRep(rep->getId());
    rep = getGNode(repId);
    assert(rep && "rep node not found in VDG!");
    // rep's subs
    NodeBS mergedSubs = getSubs(repId);
    // other nodes' subs/properties/edges
    for (const NodeID id : nodes)
    {
        if (id == repId) continue;
        VDGNode* sub = getGNode(id);
        assert(sub && "To merge node not found in VDG!");
        mergedSubs |= getSubs(id);
        resetSubs(id);
        rep->setLoadConsume(sub->isLoadConsume());
        rep->setStoreYield(sub->isStoreYield());
        moveEdgesToRep(sub, rep);
    }
    // new subs
    setSubs(repId, mergedSubs);
    // new rep
    for (const NodeID id : mergedSubs)
    {
        if (id == repId) continue;
        setRep(id, repId);
    }
}
// must scc merge 
// rep is not sub of any other node
// one node has only one rep
// consider solid edges only
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
        mergeNodesIntoRep(subs, rep);
    }
}

// non-reachable nodes to load-consume nodes are removed
// consider all edges
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

    std::vector<NodeID> repsToRemove;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID repId = it->first;
        if (!isSuperNode(repId) || reachable.test(repId))
            continue;
        repsToRemove.push_back(repId);
    }

    for (const NodeID repId : repsToRemove)
    {
        VDGNode* node = getGNode(repId);
        assert(node && "rep node not found in VDG!");
        removeNode(node);
    }
}

// non-reachable nodes from store-yield nodes are removed (keep load-consume nodes)
// consider all edges
void VDG::pruneUnreachableFromStoreYield()
{
    NodeBS reachable;
    std::vector<NodeID> worklist;

    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID id = it->first;
        VDGNode* node = it->second;
        if (node->isStoreYield())
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
        for (VDGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it != eit; ++it)
        {
            const NodeID dstId = (*it)->getDstID();
            if (!reachable.test(dstId))
            {
                reachable.set(dstId);
                worklist.push_back(dstId);
            }
        }
    }

    std::vector<NodeID> repsToRemove;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID repId = it->first;
        if (!isSuperNode(repId) || reachable.test(repId))
            continue;
        VDGNode* node = it->second;
        if (node->isLoadConsume())
            continue;
        repsToRemove.push_back(repId);
    }

    for (const NodeID repId : repsToRemove)
    {
        VDGNode* node = getGNode(repId);
        assert(node && "rep node not found in VDG!");
        removeNode(node);
    }
}

// constraint system: 
// Must(x)={s| x --solid_edge--> y, s in Must(y)} U {x| x is load-consume}
// May(x)={s| x --edge--> y, s in May(y)} U {x| x is load-consume}
// merge x into y: Must(y)=May(y)=May(x)=Must(x)
// merge x into dst: Must(x)=May(x)={dst}

void VDG::reduceByStableReachability()
{
    const u32_t total = getTotalNodeNum();
    std::vector<NodeBS> must(total);
    std::vector<NodeBS> may(total);
    std::vector<bool> inWorklist(total, false);
    std::vector<NodeID> worklist;

    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID id = it->first;
        VDGNode* node = it->second;
        if (!isSuperNode(id))
            continue;
        if (node->isLoadConsume())
        {
            must[id].set(id);
            may[id].set(id);
            worklist.push_back(id);
            inWorklist[id] = true;
        }
    }

    while (!worklist.empty())
    {
        const NodeID id = worklist.back();
        worklist.pop_back();
        inWorklist[id] = false;
        VDGNode* node = getGNode(id);
        if (!node)
            continue;
        for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
        {
            VDGEdge* edge = *it;
            const NodeID srcId = edge->getSrcID();
            if (!isSuperNode(srcId))
                continue;
            bool changed = false;
            if (!edge->isVirtualEdge())
            {
                NodeBS &srcMust = must[srcId];
                const unsigned oldMust = srcMust.count();
                srcMust |= must[id];
                if (srcMust.count() != oldMust)
                    changed = true;
            }

            NodeBS &srcMay = may[srcId];
            const unsigned oldMay = srcMay.count();
            srcMay |= may[id];
            if (srcMay.count() != oldMay)
                changed = true;

            if (changed && !inWorklist[srcId])
            {
                worklist.push_back(srcId);
                inWorklist[srcId] = true;
            }
        }
    }

    auto hashNodeBS = [](const NodeBS& bs) -> size_t
    {
        size_t h = 0;
        for (const NodeID id : bs)
        {
            h ^= std::hash<NodeID>{}(id) + 0x9e3779b9u + (h << 6) + (h >> 2);
        }
        h ^= std::hash<unsigned>{}(bs.count()) + 0x9e3779b9u + (h << 6) + (h >> 2);
        return h;
    };

    std::unordered_map<size_t, std::vector<NodeID>> buckets;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID id = it->first;
        if (!isSuperNode(id))
            continue;
        if (must[id] != may[id])
            continue;
        buckets[hashNodeBS(must[id])].push_back(id);
    }

    struct StableGroup
    {
        NodeBS stable;
        std::vector<NodeID> nodes;
    };

    for (auto &bucket : buckets)
    {
        std::vector<StableGroup> groups;
        for (const NodeID id : bucket.second)
        {
            const NodeBS &stable = must[id];
            bool placed = false;
            for (StableGroup &group : groups)
            {
                if (stable == group.stable)
                {
                    group.nodes.push_back(id);
                    placed = true;
                    break;
                }
            }
            if (!placed)
            {
                StableGroup group;
                group.stable = stable;
                group.nodes.push_back(id);
                groups.push_back(std::move(group));
            }
        }

        for (StableGroup &group : groups)
        {
            NodeBS nodesToMerge;
            for (const NodeID id : group.nodes)
                nodesToMerge.set(id);

            if (nodesToMerge.count() <= 1)
                continue;

            const unsigned stableCount = group.stable.count();
            if (stableCount == 1)
            {
                const NodeID dstId = *(group.stable.begin());
                VDGNode* dst = getGNode(dstId);
                assert(dst && "dst node not found in VDG!");
                mergeNodesIntoRep(nodesToMerge, dst);
                continue;
            }

            NodeID repId = group.nodes[0];
            VDGNode* rep = getGNode(repId);
            assert(rep && "rep node not found in VDG!");
            mergeNodesIntoRep(nodesToMerge, rep);
        }
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
