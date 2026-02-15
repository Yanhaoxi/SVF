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
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include <cassert>
#include <fstream>
#include <functional>
#include <limits>
#include <unordered_map>
#include <sstream>
#include <vector>

using namespace SVF;

// #define VDG_EDGE_DEBUG 1
#ifndef VDG_EDGE_DEBUG
#define VDG_EDGE_DEBUG 0
#endif

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
    bool isVirtual = edge->isVirtualEdge();
    removeVDGEdge(edge);
    addEdgeInternal(src, newDst, isVirtual);
}

void VDG::reTargetSrcOfEdge(VDGEdge* edge, VDGNode* newSrc)
{
    VDGNode* dst = edge->getDstNode();
    if (dst == newSrc)
    {
        removeVDGEdge(edge);
        return;
    }
    bool isVirtual = edge->isVirtualEdge();
    removeVDGEdge(edge);
    addEdgeInternal(newSrc, dst, isVirtual);
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
    
    // Clean up verVec_/repVec_/subVec_ for this rep and all its sub versions
    // to prevent dangling pointers after the node is freed
    Version repVer = node->getVersion();
    assert(repVer < subVec_.size() && !subVec_[repVer].empty() && "rep version should have an entry in subVec_!");
    for (unsigned sub : subVec_[repVer])
    {
        if (sub < verVec_.size()) verVec_[sub] = nullptr;
        if (sub < repVec_.size()) repVec_[sub] = 0;
    }
    subVec_[repVer].clear();
    
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
        // Use verVec_ to get rep node directly, compare pointers
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

// versions is a sparse vector of version IDs to be merged into repVer
void VDG::mergeVersionsIntoRep(const NodeVector& versions, Version repVer)
{
    VDGNode* rep = getNode(repVer);
    
    // Collect all subs including rep's existing subs (move to avoid copy)
    assert(repVer < subVec_.size() && !subVec_[repVer].empty() && "rep version should have an entry in subVec_!");
    NodeBS allSubs = std::move(subVec_[repVer]);
    
    // Merge each version into rep
    for (Version v : versions)
    {
        if (v == repVer) continue;
        
        VDGNode* subNode = getNode(v);
        NodeID subNodeId = subNode->getId();
        
        // Get v's subs (including v itself)
        assert(v < subVec_.size() && !subVec_[v].empty() && "sub version should have an entry in subVec_ before merging!");
        const NodeBS& vSubs = subVec_[v];
        
        // Merge properties
        rep->setLoadConsume(subNode->isLoadConsume());
        rep->setStoreYield(subNode->isStoreYield());
        rep->mergeStmtReliance(subNode->getStmtRelianceSet());
        
        // Move edges from sub to rep
        moveEdgesToRep(subNode, rep);
        
        // Update verVec_ and repVec_ for v and all its subs (vSubs includes v)
        for (unsigned sub : vSubs)
        {
            if (sub < verVec_.size()) verVec_[sub] = rep;
            if (sub < repVec_.size()) repVec_[sub] = repVer;
        }
        
        // Add v's subs to allSubs and remove v from subVec_
        allSubs |= vSubs;
        subVec_[v].clear();  // Remove v from subVec_ (no longer a rep)
        
        // Delete sub node immediately (no longer needed)
        superNodes[subNodeId] = false;
        nodeVec[subNodeId] = nullptr;
        --nodeNum;
        delete subNode;
    }
    
    // Update subVec_ for rep (move to avoid copy)
    subVec_[repVer] = std::move(allSubs);
}

// SCC merge on solid edges and compute topological order
// rep is not sub of any other node, one node has only one rep
// consider solid edges only
// return topo order of SCC reps (solid-edge SCC DAG)
// @param candidates: if non-empty, only traverse from these node IDs; otherwise traverse all
NodeVector VDG::sccMergeSolidEdges(const NodeVector& candidates)
{
    VDGSCCDetection scc(this);
    if (candidates.empty())
    {
        scc.find();  // Full graph traversal
    }
    else
    {
        scc.find(candidates);  // Only from candidate nodes
    }

    // Get topological order from SCC detection
    VDGSCCDetection::GNodeStack topoStack = scc.topoNodeStack();
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
        
        // Convert NodeIDs to versions for merging (sparse vector)
        NodeVector versionsToMerge;
        versionsToMerge.reserve(subs.count());
        VDGNode* repNode = getNodeFast(repNodeId);
        Version repVer = repNode->getVersion();
        for (unsigned nodeId : subs)
        {
            VDGNode* node = getNodeFast(nodeId);
            versionsToMerge.push_back(node->getVersion());
        }
        mergeVersionsIntoRep(versionsToMerge, repVer);
    }

    return topoOrder;
}

void VDG::propagateInTopoOrder(PropagateCallback propagate, StmtRelianceCallback onVersionChanged)
{
    assert(hasPendingUpdates() && "propagateInTopoOrder called with no pending updates!");

    // Compute topological order (also does SCC merge)
    const NodeVector& seedUpdated = getUpdatedNodes();
    NodeVector topoOrder = sccMergeSolidEdges(seedUpdated);
    NodeSet updatedSet(seedUpdated.begin(), seedUpdated.end());

    // After SCC merge, union pts from all sub-versions into their rep version.
    // This ensures that when versions are merged at runtime (during solving),
    // the pts data stored under sub-version keys is not lost.
    // For merges that happened during pre-solving simplification, the sub-versions
    // have no pts data yet, so unionPts is a no-op.
    for (NodeID nodeId : topoOrder)
    {
        if (!hasNodeFast(nodeId)) continue;
        VDGNode* repNode = getNodeFast(nodeId);
        const Version repV = repNode->getVersion();
        const NodeBS& subs = getSubVersions(repV);
        if (subs.count() <= 1) continue;  // No subs to merge pts from
        for (unsigned sub : subs)
        {
            if (sub == repV) continue;
            if (propagate(sub, repV))
            {
                // pts changed: mark rep for propagation
                updatedSet.insert(nodeId);
            }
        }
    }

    // Propagate in topological order
    for (NodeID nodeId : topoOrder)
    {
        // topoOrder contains only SCC rep nodes after merge
        assert(hasNodeFast(nodeId) && isSuperNode(nodeId) && "topoOrder should only contain rep nodes!");

        // Skip if this node doesn't need propagation
        if (updatedSet.find(nodeId) == updatedSet.end())
            continue;

        VDGNode* srcNode = getNodeFast(nodeId);
        const Version srcV = srcNode->getVersion();
        onVersionChanged(srcV);

        // Propagate to all solid-edge successors
        for (auto it = srcNode->OutEdgeBegin(); it != srcNode->OutEdgeEnd(); ++it)
        {
            const VDGEdge* edge = *it;
            if (edge->isVirtualEdge())
                continue;

            VDGNode* dstNode = getNodeFast(edge->getDstID());
            const Version dstV = dstNode->getVersion();

            // Call the propagate callback
            if (propagate(srcV, dstV))
            {
                // Points-to changed, mark for further propagation
                const NodeID dstId = edge->getDstID();
                updatedSet.insert(dstId);
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
    const u32_t cap = getNextNodeId();
    DenseBitVector reachable(cap);
    std::vector<NodeID> worklist;

    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const auto kv = *it;
        const NodeID id = kv.first;
        VDGNode* node = kv.second;
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
        VDGNode* node = getNodeFast(id);
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
        const NodeID repId = (*it).first;
        if (!isSuperNode(repId) || reachable.test(repId))
            continue;
        repsToRemove.push_back(repId);
    }

    for (const NodeID repId : repsToRemove)
    {
        removeNode(getNodeFast(repId));
    }
}

// non-reachable nodes from store-yield nodes are removed (keep load-consume nodes)
// consider all edges
void VDG::pruneUnreachableFromStoreYield()
{
    const u32_t cap = getNextNodeId();
    DenseBitVector reachable(cap);
    std::vector<NodeID> worklist;

    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const auto kv = *it;
        const NodeID id = kv.first;
        VDGNode* node = kv.second;
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
        VDGNode* node = getNodeFast(id);
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
        const auto kv = *it;
        const NodeID repId = kv.first;
        if (!isSuperNode(repId) || reachable.test(repId))
            continue;
        VDGNode* node = kv.second;
        if (node->isLoadConsume())
            continue;
        repsToRemove.push_back(repId);
    }

    for (const NodeID repId : repsToRemove)
    {
        removeNode(getNodeFast(repId));
    }
}

// Chain contraction:
// x is not load-consume node, x has only one out-edge(solid) to successor y => merge x into y
// y is not store-yield node, y has only one in-edge(solid) from predecessor x => merge y into x

void VDG::chainContraction()
{
    const u32_t total = getNextNodeId();
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
            enqueue((*it).first);
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
        VDGNode* x = getNodeFast(xId);
        if (x->isLoadConsume())
            return false;

        if (x->getOutEdges().size() != 1)
            return false;

        VDGEdge* edge = *(x->OutEdgeBegin());
        if (edge->isVirtualEdge())
            return false;

        VDGNode* solidSucc = edge->getDstNode();

        NodeVector toMerge = { x->getVersion() };
        mergeVersionsIntoRep(toMerge, solidSucc->getVersion());
        enqueueInNeighbors(solidSucc);
        return true;
    };

    // x->y is only in-edge(solid) for y , y is not store-yield => merge y to x
    auto tryMergeBackward = [&](NodeID yId) -> bool
    {
        VDGNode* y = getNodeFast(yId);
        if (y->isStoreYield())
            return false;

        if (y->getInEdges().size() != 1)
            return false;

        VDGEdge* edge = *(y->InEdgeBegin());
        if (edge->isVirtualEdge())
            return false;

        VDGNode* solidPred = edge->getSrcNode();

        NodeVector toMerge = { y->getVersion() };
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
        if (!hasNodeFast(id))
            continue;
        if (!isSuperNode(id))
            continue;

        if (!tryMergeForward(id))
            (void)tryMergeBackward(id);
    }
}


//c in reach(a)={x|a->b,x in reach(b),b!=c},then a->c is redundant
void VDG::transitiveRedundancyElimination()
{
    std::vector<NodeID> topoOrder = sccMergeSolidEdges();
    auto computeReachability = [](VDG &graph,
                                  const std::vector<NodeID> &topoOrder,
                                  std::vector<DenseBitVector> &reach)
    {
        const u32_t cap = graph.getNextNodeId();
        reach.assign(cap, DenseBitVector(cap));
        // Need reverse topo order so successors are processed before predecessors.
        for (auto it = topoOrder.rbegin(); it != topoOrder.rend(); ++it)
        {
            const NodeID id = *it;
            if (!graph.isSuperNode(id))
                continue;
            VDGNode* node = graph.getNodeFast(id);
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

    std::vector<DenseBitVector> reachSolid;
    computeReachability(*this, topoOrder, reachSolid);

    std::vector<VDGEdge*> toRemove;
    for (VDG::const_iterator it = begin(), eit = end(); it != eit; ++it)
    {
        const auto kv = *it;
        const NodeID srcId = kv.first;
        VDGNode* node = kv.second;
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
        // Use graph iterator to avoid counting same node multiple times (verVec_ can have multiple versions pointing to same rep node)
        for (auto it = graph->begin(); it != graph->end(); ++it)
        {
            const VDGNode* node = (*it).second;
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

    auto withinThreshold = [&](size_t count) -> bool
    {
        if (count < minNodesPerGraph) return false;
        if (maxNodesPerGraph > 0 && count > maxNodesPerGraph) return false;
        return true;
    };

    // Collect and sort object IDs for deterministic output
    std::vector<NodeID> objects;
    objects.reserve(vdgMap.size());
    for (const auto& entry : vdgMap)
        objects.push_back(entry.first);
    std::sort(objects.begin(), objects.end());

    if (splitByObject)
    {
        // Per-object files: use %o token in filename template
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

        const std::string tmpl = ensureTemplateHasToken(filename);
        for (const NodeID o : objects)
        {
            const auto& graphPtr = vdgMap.at(o);
            if (!graphPtr) continue;
            if (!withinThreshold(graphPtr->getSuperNodeCount())) continue;
            graphPtr->dump(replaceToken(tmpl, o));
        }
    }
    else
    {
        // Single merged DOT file: all VDGs as subgraph clusters
        // Node names use "o{obj}v{ver}" to avoid collisions across objects
        std::string dotPath = filename;
        if (dotPath.size() < 4 || dotPath.substr(dotPath.size() - 4) != ".dot")
            dotPath += ".dot";

        std::ofstream out(dotPath);
        if (!out.is_open())
        {
            SVFUtil::errs() << "VDGManager::writeToFile: cannot open " << dotPath << "\n";
            return;
        }

        out << "digraph VDG {\n";

        for (const NodeID o : objects)
        {
            const auto& graphPtr = vdgMap.at(o);
            if (!graphPtr) continue;
            if (!withinThreshold(graphPtr->getSuperNodeCount())) continue;
            const VDG &graph = *graphPtr;

            out << "  subgraph cluster_obj" << o << " {\n";
            out << "    label=\"obj=" << o << "\";\n";
            out << "    style=dashed;\n";

            // Nodes
            for (auto it = graph.begin(); it != graph.end(); ++it)
            {
                const VDGNode *node = (*it).second;
                if (!graph.isSuperNode(node->getId())) continue;

                out << "    o" << o << "v" << node->getVersion()
                    << " [label=\"o=" << o << "\\nv=" << node->getVersion() << "\""
                    << ", shape=" << (node->isLoadConsume() ? "box" : "ellipse")
                    << ", style=filled"
                    << ", fillcolor=" << (node->isStoreYield() ? "mistyrose" : "white")
                    << "];\n";
            }

            // Edges
            for (auto it = graph.begin(); it != graph.end(); ++it)
            {
                const VDGNode *node = (*it).second;
                if (!graph.isSuperNode(node->getId())) continue;

                for (auto eit = node->OutEdgeBegin(); eit != node->OutEdgeEnd(); ++eit)
                {
                    const VDGEdge *edge = *eit;
                    if (!graph.isSuperNode(edge->getDstID())) continue;
                    const VDGNode *dst = edge->getDstNode();

                    out << "    o" << o << "v" << node->getVersion()
                        << " -> o" << o << "v" << dst->getVersion();
                    if (edge->isVirtualEdge())
                        out << " [style=dashed]";
                    out << ";\n";
                }
            }

            out << "  }\n";
        }

        out << "}\n";
        out.close();

        SVFUtil::outs() << "VDG merged graph written to " << dotPath << "\n";
    }
}
