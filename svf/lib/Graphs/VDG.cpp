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
#include "Util/GeneralType.h"
#include "Util/WorkList.h"
#include "Graphs/SCC.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include <cassert>
#include <functional>
#include <limits>
#include <queue>
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

void VDG::logEdgeChange(const char* tag, const VDGEdge* edge)
{
#if VDG_EDGE_DEBUG
    if (edge == nullptr)
        return;
    const VDGNode* src = edge->getSrcNode();
    const VDGNode* dst = edge->getDstNode();
    SVFUtil::outs() << "[VDG] " << tag
                    << " (obj=" << objId << ",v=" << src->getVersion() << ")"
                    << " -> (obj=" << objId << ",v=" << dst->getVersion() << ")"
                    << " kind=" << static_cast<unsigned>(edge->getVDGEdgeKind())
                    << " virtual=" << edge->isVirtualEdge() << "\n";
#else
    (void)tag;
    (void)edge;
#endif
}

void VDG::logEdgeMembership(const char* tag, const VDGNode* node, const VDGEdge* edge)
{
#if VDG_EDGE_DEBUG
    if (node == nullptr || edge == nullptr)
        return;
    const bool inInEdges = node->getInEdges().find(const_cast<VDGEdge*>(edge)) != node->getInEdges().end();
    
    const bool inOutEdges = node->getOutEdges().find(const_cast<VDGEdge*>(edge)) != node->getOutEdges().end();
    SVFUtil::outs() << "[VDG] " << tag
                    << " node(obj=" << objId << ",v=" << node->getVersion()
                    << ",id=" << node->getId() << ")"
                    << " edge(" << edge->getSrcID() << "->" << edge->getDstID() << ")"
                    << " in=" << inInEdges << " out=" << inOutEdges << "\n";
#else
    (void)tag;
    (void)node;
    (void)edge;
#endif
}

bool VDG::updateEdgeVirtual(VDGEdge* edge, bool isVirtual)
{
    assert(edge && "VDG edge to be updated is null!");
    const bool wasVirtual = edge->isVirtualEdge();
    // non change
    if (wasVirtual == isVirtual)
        return false;
    // change
    edge->setVirtual(isVirtual);
    // virtual -> solid
    return wasVirtual && !isVirtual;
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
    addEdgeInternal(src, newDst, kind, isVirtual);
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
    addEdgeInternal(newSrc, dst, kind, isVirtual);
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
    assert(isSuperNode(node->getId()) && "Only rep nodes should be removed via removeNode!");
    
    // Remove all edges
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

    // Sub nodes are already deleted during merge, just delete this rep node
    deleteNode(node->getId());
}

void VDG::moveEdgesToRep(VDGNode* node, VDGNode* rep)
{
    // rep should already be a super node
    assert(isSuperNode(rep->getId()) && "rep should be a super node!");
    
    std::vector<VDGEdge*> inSccEdges;
    std::vector<VDGEdge*> inNonSccEdges;
    for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
    {
        VDGEdge* edge = *it;
        VDGNode* srcNode = edge->getSrcNode();
        // Use versionMap to get rep node directly, compare pointers
        if (getNode(srcNode->getVersion()) != rep)
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
        VDGNode* dstNode = edge->getDstNode();
        // Use versionMap to get rep node directly, compare pointers
        if (getNode(dstNode->getVersion()) != rep)
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

// versions are all the repversions to be merged into repVer
void VDG::mergeVersionsIntoRep(const VersionSet& versions, Version repVer)
{
    VDGNode* rep = getNode(repVer);
    
    // Collect all subs including rep's existing subs
    VersionSet allSubs;
    assert(subMap.find(repVer) != subMap.end() && "rep version should have an entry in subMap!");
    allSubs = subMap[repVer];
    
    // Merge each version into rep
    for (Version v : versions)
    {
        if (v == repVer) continue;
        
        VDGNode* subNode = getNode(v);
        NodeID subNodeId = subNode->getId();
        
        // Get v's subs (including v itself)
        auto it = subMap.find(v);
        assert(it != subMap.end() && "sub version should have an entry in subMap before merging!");
        const VersionSet& vSubs = it->second;
        
        // Merge properties
        rep->setLoadConsume(subNode->isLoadConsume());
        rep->setStoreYield(subNode->isStoreYield());
        rep->incrementMergedCount(subNode->getMergedCount());
        
        // Move edges from sub to rep
        moveEdgesToRep(subNode, rep);
        
        // Update versionMap and repMap for v and all its subs (vSubs includes v)
        for (Version sub : vSubs)
        {
            versionMap[sub] = rep;
            repMap[sub] = repVer;
        }
        
        // Add v's subs to allSubs and remove v from subMap
        allSubs.insert(vSubs.begin(), vSubs.end());
        subMap.erase(it);  // Remove v from subMap (no longer a rep)
        
        // Delete sub node immediately (no longer needed)
        superNodes[subNodeId] = false;
        removeGNode(subNode);  // This deletes the node from graph
    }
    
    // Update subMap for rep
    subMap[repVer] = allSubs;
}

// SCC merge on solid edges and compute topological order
// rep is not sub of any other node, one node has only one rep
// consider solid edges only
// return topo order of SCC reps (solid-edge SCC DAG)
// @param candidates: if non-empty, only traverse from these node IDs; otherwise traverse all
NodeVector VDG::sccMergeSolidEdges(NodeSet candidates)
{
    const bool oldDetect = detectVE();
    setDetectVE(false);  // Only consider solid edges

    SCCDetection<VDG*> scc(this);
    if (candidates.empty())
    {
        scc.find();  // Full graph traversal
    }
    else
    {
        scc.find(candidates);  // Only from candidate nodes
    }

    setDetectVE(oldDetect);

    // Get topological order from SCC detection
    SCCDetection<VDG*>::GNodeStack topoStack = scc.topoNodeStack();
    NodeVector topoOrder;
    topoOrder.reserve(topoStack.size());
    while (!topoStack.empty())
    {
        const NodeID repId = topoStack.top();
        topoStack.pop();
        topoOrder.push_back(repId);
    }

    // Merge SCC nodes
    for (const NodeID repNodeId : topoOrder)
    {
        const NodeBS &subs = scc.subNodes(repNodeId);
        if (subs.count() <= 1) continue;
        
        // Convert NodeIDs to versions for merging
        VersionSet versionsToMerge;
        VDGNode* repNode = getGNode(repNodeId);
        Version repVer = repNode->getVersion();
        for (NodeID nodeId : subs)
        {
            VDGNode* node = getGNode(nodeId);
            versionsToMerge.insert(node->getVersion());
        }
        mergeVersionsIntoRep(versionsToMerge, repVer);
    }

    return topoOrder;
}

void VDG::propagateInTopoOrder(PropagateCallback propagate, StmtRelianceCallback onVersionChanged)
{
    assert(hasPendingUpdates() && "propagateInTopoOrder called with no pending updates!");

    // Compute topological order (also does SCC merge)
    NodeVector topoOrder = sccMergeSolidEdges(getUpdatedNodes());
    
    // updatedNodes now serves as the working set (will be extended with transitive successors)

    // Propagate in topological order
    for (NodeID nodeId : topoOrder)
    {
        // topoOrder contains only SCC rep nodes after merge
        assert(hasGNode(nodeId) && isSuperNode(nodeId) && "topoOrder should only contain rep nodes!");

        // Skip if this node doesn't need propagation
        if (updatedNodes.find(nodeId) == updatedNodes.end())
            continue;

        VDGNode* srcNode = getGNode(nodeId);
        const Version srcV = srcNode->getVersion();

        // Propagate to all solid-edge successors
        for (auto it = srcNode->OutEdgeBegin(); it != srcNode->OutEdgeEnd(); ++it)
        {
            const VDGEdge* edge = *it;
            if (edge->isVirtualEdge())
                continue;

            VDGNode* dstNode = getGNode(edge->getDstID());
            const Version dstV = dstNode->getVersion();

            // Call the propagate callback
            if (propagate(srcV, dstV))
            {
                // Points-to changed, mark for further propagation
                updatedNodes.insert(edge->getDstID());
                onVersionChanged(dstV);
            }
        }
    }

    // Clear update markers after propagation
    clearUpdateMarkers();
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
        removeNode(getGNode(repId));
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
        removeNode(getGNode(repId));
    }
}

namespace
{
    void reduceByStableReachabilityInternal(VDG &graph,
                                            bool forward,
                                            bool seedLoadConsume,
                                            const std::function<void(NodeID)> &pruneNode)
    {
        const u32_t total = graph.getTotalNodeNum();
        std::vector<NodeBS> must(total);
        std::vector<NodeBS> may(total);
        std::vector<bool> inWorklist(total, false);
        NodeVector worklist;

        for (VDG::const_iterator it = graph.begin(), eit = graph.end(); it != eit; ++it)
        {
            const NodeID id = it->first;
            VDGNode* node = it->second;
            if (!graph.isSuperNode(id))
                continue;
            const bool isSeed = seedLoadConsume ? node->isLoadConsume() : node->isStoreYield();
            if (isSeed)
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
            VDGNode* node = graph.getGNode(id);
            if (!node)
                continue;

            auto propagateToNeighbor = [&](VDGEdge* edge, NodeID neighborId)
            {
                if (!graph.isSuperNode(neighborId))
                    return;
                bool changed = false;
                if (!edge->isVirtualEdge())
                {
                    NodeBS &neighborMust = must[neighborId];
                    const unsigned oldMust = neighborMust.count();
                    neighborMust |= must[id];
                    if (neighborMust.count() != oldMust)
                        changed = true;
                }

                NodeBS &neighborMay = may[neighborId];
                const unsigned oldMay = neighborMay.count();
                neighborMay |= may[id];
                if (neighborMay.count() != oldMay)
                    changed = true;

                if (changed && !inWorklist[neighborId])
                {
                    worklist.push_back(neighborId);
                    inWorklist[neighborId] = true;
                }
            };

            if (forward)
            {
                for (VDGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it != eit; ++it)
                {
                    VDGEdge* edge = *it;
                    propagateToNeighbor(edge, edge->getDstID());
                }
            }
            else
            {
                for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
                {
                    VDGEdge* edge = *it;
                    propagateToNeighbor(edge, edge->getSrcID());
                }
            }
        }

        // Prune nodes with empty stable set (Must==May=={})
        {
            std::vector<NodeID> toPrune;
            for (VDG::const_iterator it = graph.begin(), eit = graph.end(); it != eit; ++it)
            {
                const NodeID id = it->first;
                if (!graph.isSuperNode(id))
                    continue;
                if (may[id].empty()){
                    assert(must[id].empty() && "must set should also be empty if may set is empty");
                    toPrune.push_back(id);
                }
            }
            for (const NodeID id : toPrune)
            {
                pruneNode(id);
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
        for (VDG::const_iterator it = graph.begin(), eit = graph.end(); it != eit; ++it)
        {
            const NodeID id = it->first;
            if (!graph.isSuperNode(id))
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
                
                // Convert NodeIDs to versions for merging
                VersionSet versionsToMerge;
                for (NodeID nodeId : nodesToMerge)
                {
                    VDGNode* node = graph.getGNode(nodeId);
                    versionsToMerge.insert(node->getVersion());
                }

                if (stableCount == 1)
                {
                    const NodeID stableId = *(group.stable.begin());
                    VDGNode* stableNode = graph.getGNode(stableId);
                    graph.mergeVersionsIntoRep(versionsToMerge, stableNode->getVersion());
                    continue;
                }

                NodeID repId = group.nodes[0];
                VDGNode* repNode = graph.getGNode(repId);
                graph.mergeVersionsIntoRep(versionsToMerge, repNode->getVersion());
            }
        }
    }
} // namespace

// constraint system: 
// Must(x)={s| x --solid_edge--> y, s in Must(y)} U {x| x is load-consume}
// May(x)={s| x --edge--> y, s in May(y)} U {x| x is load-consume}
// merge x into y: Must(y)=May(y)=May(x)=Must(x)
// merge x into dst: Must(x)=May(x)={dst}
// prune x: Must(x)=May(x)={}

void VDG::reduceByStableDstReachability()
{
    reduceByStableReachabilityInternal(*this,
                                       /*forward=*/false,
                                       /*seedLoadConsume=*/true,
                                       [this](NodeID id)
                                       {
                                            removeNode(getGNode(id));
                                       });
}

// constraint system (dual of Dst):
// Must(x)={s| y --solid_edge--> x, s in Must(y)} U {x| x is store-yield}
// May(x)={s| y --edge--> x, s in May(y)} U {x| x is store-yield}
// merge x into y: Must(y)=May(y)=May(x)=Must(x)
// merge x into src: Must(x)=May(x)={src}
// prune x: Must(x)=May(x)={}

void VDG::reduceByStableSrcReachability()
{
    reduceByStableReachabilityInternal(*this,
                                       /*forward=*/true,
                                       /*seedLoadConsume=*/false,
                                       [this](NodeID id)
                                       {
                                            removeNode(getGNode(id));
                                       });
}

// Chain contraction:
// x is not load-consume node, x has only one out-edge(solid) to successor y => merge x into y
// y is not store-yield node, y has only one in-edge(solid) from predecessor x => merge y into x

void VDG::chainContraction()
{
    const u32_t total = getTotalNodeNum();
    std::vector<bool> inWorklist(total, false);
    std::vector<NodeID> worklist;

    auto enqueue = [&](NodeID id)
    {
        if (id >= total)
            return;
        if (!inWorklist[id])
        {
            inWorklist[id] = true;
            worklist.push_back(id);
        }
    };

    auto enqueueInitial = [&]()
    {
        for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
            enqueue(it->first);
    };

    auto enqueueInNeighbors = [&](VDGNode* node)
    {
        assert(node && "enqueueInNeighbors called with null node!");
        enqueue(node->getId());
        for (VDGNode::const_iterator it = node->InEdgeBegin(), eit = node->InEdgeEnd(); it != eit; ++it)
            enqueue((*it)->getSrcID());
    };

    auto enqueueOutNeighbors = [&](VDGNode* node)
    {
        assert(node && "enqueueOutNeighbors called with null node!");
        enqueue(node->getId());
        for (VDGNode::const_iterator it = node->OutEdgeBegin(), eit = node->OutEdgeEnd(); it != eit; ++it)
            enqueue((*it)->getDstID());
    };

    // x->y is only out-edge(solid) for x , x is not load-consume => merge x to y
    auto tryMergeForward = [&](NodeID xId) -> bool
    {
        VDGNode* x = getGNode(xId);
        if (x->isLoadConsume())
            return false;

        if (x->getOutEdges().size() != 1)
            return false;

        VDGEdge* edge = *(x->OutEdgeBegin());
        if (edge->isVirtualEdge())
            return false;

        VDGNode* solidSucc = edge->getDstNode();

        VersionSet toMerge;
        toMerge.insert(x->getVersion());
        mergeVersionsIntoRep(toMerge, solidSucc->getVersion());
        enqueueInNeighbors(solidSucc);
        return true;
    };

    // x->y is only in-edge(solid) for y , y is not store-yield => merge y to x
    auto tryMergeBackward = [&](NodeID yId) -> bool
    {
        VDGNode* y = getGNode(yId);
        if (y->isStoreYield())
            return false;

        if (y->getInEdges().size() != 1)
            return false;

        VDGEdge* edge = *(y->InEdgeBegin());
        if (edge->isVirtualEdge())
            return false;

        VDGNode* solidPred = edge->getSrcNode();

        VersionSet toMerge;
        toMerge.insert(y->getVersion());
        mergeVersionsIntoRep(toMerge, solidPred->getVersion());
        enqueueOutNeighbors(solidPred);
        return true;
    };

    worklist.clear();
    enqueueInitial();
    while (!worklist.empty())
    {
        const NodeID id = worklist.back();
        worklist.pop_back();
        inWorklist[id] = false;

        if (id >= total)
            continue;
        if (!hasGNode(id))
            continue;
        if (!isSuperNode(id))
            continue;

        if (!tryMergeForward(id))
            (void)tryMergeBackward(id);
    }
}


//Todo:
//c in reach(a)={x|a->b,x in reach(b),b!=c},then a->c is redundant
void VDG::transitiveRedundancyElimination()
{
    std::vector<NodeID> topoOrder = sccMergeSolidEdges();
    auto computeReachability = [](VDG &graph,
                                  const std::vector<NodeID> &topoOrder,
                                  std::vector<NodeBS> &reach)
    {
        const u32_t total = graph.getTotalNodeNum();
        reach.assign(total, NodeBS());
        // Need reverse topo order so successors are processed before predecessors.
        for (auto it = topoOrder.rbegin(); it != topoOrder.rend(); ++it)
        {
            const NodeID id = *it;
            if (!graph.isSuperNode(id))
                continue;
            VDGNode* node = graph.getGNode(id);
            reach[id].set(id);
            for (VDGNode::const_iterator ei = node->OutEdgeBegin(), eei = node->OutEdgeEnd(); ei != eei; ++ei)
            {
                const VDGEdge* edge = *ei;
                if (edge->isVirtualEdge())
                    continue;
                const NodeID dstId = edge->getDstID();
                reach[id] |= reach[dstId];
            }
        }
    };

    std::vector<NodeBS> reachSolid;
    computeReachability(*this, topoOrder, reachSolid);

    std::vector<VDGEdge*> toRemove;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const NodeID srcId = it->first;
        VDGNode* node = it->second;
        if (!isSuperNode(srcId))
            continue;

        std::vector<NodeID> solidSuccs;
        for (VDGNode::const_iterator ei = node->OutEdgeBegin(), eei = node->OutEdgeEnd(); ei != eei; ++ei)
        {
            VDGEdge* edge = *ei;
            if (edge->isVirtualEdge())
                continue;
            solidSuccs.push_back(edge->getDstID());
        }
        if (solidSuccs.size() <= 1)
            continue;

        for (VDGNode::const_iterator ei = node->OutEdgeBegin(), eei = node->OutEdgeEnd(); ei != eei; ++ei)
        {
            VDGEdge* edge = *ei;
            if (edge->isVirtualEdge())
                continue;
            const NodeID dstId = edge->getDstID();
            // check redundancy
            bool redundant = false;
            for (const NodeID succId : solidSuccs)
            {
                if (succId == dstId)
                    continue;
                if (reachSolid[succId].test(dstId))
                {
                    redundant = true;
                    break;
                }
            }

            if (redundant){
                toRemove.push_back(edge);
                solidSuccs.erase(std::remove(solidSuccs.begin(), solidSuccs.end(), dstId), solidSuccs.end());
            }
        }
    }

    for (VDGEdge* edge : toRemove)
        removeVDGEdge(edge);
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

    static std::string getGraphName(VDG* graph)
    {
        std::stringstream ss;
        ss << "VDG (obj=" << graph->getObjId() << ")";
        return ss.str();
    }

    static bool isNodeHidden(NodeType *node, VDG *graph)
    {
        return graph && !graph->isSuperNode(node->getId());
    }

    static std::string getNodeLabel(NodeType *node, VDG* graph)
    {
        std::stringstream raw;
        raw << "o=" << graph->getObjId() << "\\nv=" << node->getVersion();
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

//===----------------------------------------------------------------------===//
// VDGManager Implementation
//===----------------------------------------------------------------------===//

void VDGManager::dumpStats() const
{
    if (vdgMap.empty())
        return;

    size_t totalVDGs = 0;
    size_t totalNodes = 0;
    size_t totalSuperNodes = 0;
    size_t totalEdges = 0;
    size_t totalSolidEdges = 0;
    size_t totalVirtualEdges = 0;
    size_t minNodes = std::numeric_limits<size_t>::max();
    size_t maxNodes = 0;
    OrderedMap<size_t, size_t> nodesToObjCount;

    for (const auto& entry : vdgMap)
    {
        if (!entry.second)
            continue;
        const VDG* graph = entry.second.get();
        ++totalVDGs;

        size_t supernodeCount = 0;
        size_t nodeCount = 0;
        // Use graph iterator to avoid counting same node multiple times (versionMap can have multiple versions pointing to same rep node)
        for (auto it = graph->begin(); it != graph->end(); ++it)
        {
            const VDGNode* node = it->second;
            ++nodeCount;
            if (!graph->isSuperNode(node->getId()))
                continue;
            ++supernodeCount;
            for (auto eit = node->OutEdgeBegin(); eit != node->OutEdgeEnd(); ++eit)
            {
                if (graph->isSuperNode((*eit)->getDstID()))
                {
                    ++totalEdges;
                    if ((*eit)->isVirtualEdge())
                        ++totalVirtualEdges;
                    else
                        ++totalSolidEdges;
                }
            }
        }

        totalNodes += nodeCount;
        totalSuperNodes += supernodeCount;
        nodesToObjCount[supernodeCount] += 1;
        minNodes = std::min(minNodes, supernodeCount);
        maxNodes = std::max(maxNodes, supernodeCount);
    }

    if (totalVDGs == 0)
        return;

    SVFUtil::outs() << "# VDG stats\n";
    SVFUtil::outs() << "  graphs: " << totalVDGs << "\n";
    SVFUtil::outs() << "  total_nodes: " << totalNodes << "\n";
    SVFUtil::outs() << "  total_supernodes: " << totalSuperNodes << "\n";
    SVFUtil::outs() << "  total_edges: " << totalEdges << "\n";
    SVFUtil::outs() << "  solid_edges: " << totalSolidEdges << "\n";
    SVFUtil::outs() << "  virtual_edges: " << totalVirtualEdges << "\n";
    SVFUtil::outs() << "  min_supernodes: " << minNodes << "\n";
    SVFUtil::outs() << "  max_supernodes: " << maxNodes << "\n";
    SVFUtil::outs() << "  avg_supernodes: " << (static_cast<double>(totalSuperNodes) / totalVDGs) << "\n";
    SVFUtil::outs() << "  supernodes->objs:\n";
    for (const auto& kv : nodesToObjCount)
        SVFUtil::outs() << "    " << kv.first << " : " << kv.second << "\n";
}

void VDGManager::writeToFile(const std::string& filename) const
{
    if (filename.empty() || vdgMap.empty())
        return;

    const std::string perObjectToken = "%o";
    const bool splitByObject = Options::VDGSplitByObject()
        || filename.find(perObjectToken) != std::string::npos;
    const size_t minNodesPerGraph = Options::VDGMinNodes();
    const size_t maxNodesPerGraph = Options::VDGMaxNodes();

    auto ensureTemplateHasToken = [&](const std::string &tmpl) -> std::string
    {
        if (tmpl.find(perObjectToken) != std::string::npos) return tmpl;
        if (tmpl.size() >= 4 && tmpl.substr(tmpl.size() - 4) == ".dot")
            return tmpl.substr(0, tmpl.size() - 4) + "_" + perObjectToken + ".dot";
        return tmpl + "_" + perObjectToken;
    };

    auto replaceToken = [&](const std::string &tmpl, const NodeID o) -> std::string
    {
        std::string out = tmpl;
        const std::string obj = std::to_string(o);
        size_t pos = 0;
        while ((pos = out.find(perObjectToken, pos)) != std::string::npos)
        {
            out.replace(pos, perObjectToken.size(), obj);
            pos += obj.size();
        }
        return out;
    };

    auto withinThreshold = [&](size_t count) -> bool
    {
        if (count < minNodesPerGraph) return false;
        if (maxNodesPerGraph > 0 && count > maxNodesPerGraph) return false;
        return true;
    };

    auto superNodeCount = [](const VDG &graph) -> size_t
    {
        return graph.getSuperNodeCount();
    };

    // Collect and sort object IDs for deterministic output
    std::vector<NodeID> objects;
    objects.reserve(vdgMap.size());
    for (const auto& entry : vdgMap)
        objects.push_back(entry.first);
    std::sort(objects.begin(), objects.end());

    // Generate filename for each object
    std::string tmpl = filename;
    if (splitByObject)
    {
        // Ensure template has %o token for per-object filenames
        tmpl = ensureTemplateHasToken(filename);
    }
    else
    {
        // When not explicitly split by object, still generate per-object files with _obj suffix
        if (tmpl.size() >= 4 && tmpl.substr(tmpl.size() - 4) == ".dot")
            tmpl = tmpl.substr(0, tmpl.size() - 4) + "_obj" + perObjectToken + ".dot";
        else
            tmpl = tmpl + "_obj" + perObjectToken + ".dot";
    }

    // Write each VDG to its own file (avoids node ID conflicts)
    for (const NodeID o : objects)
    {
        const auto& graphPtr = vdgMap.at(o);
        if (!graphPtr)
            continue;
        if (!withinThreshold(superNodeCount(*graphPtr)))
            continue;
        graphPtr->dump(replaceToken(tmpl, o));
    }
}
