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
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include <algorithm>
#include <cassert>
#include <fstream>
#include <limits>
#include <string>
#include <utility>
#include <vector>

using namespace SVF;

bool VDG::solvePhaseStarted_ = false;

namespace
{

inline bool hasDotSuffix(const std::string& path)
{
    return path.size() >= 4 && path.substr(path.size() - 4) == ".dot";
}

inline std::string normalizeDotPath(const std::string& filename)
{
    if (filename.empty())
        return filename;
    return hasDotSuffix(filename) ? filename : (filename + ".dot");
}

inline size_t countNodes(const VDG& graph)
{
    return graph.getTotalNodeNum();
}

inline bool writeSingleVDGDot(const VDG& graph, const std::string& filename)
{
    const std::string dotPath = normalizeDotPath(filename);
    if (dotPath.empty())
        return false;

    std::ofstream out(dotPath);
    if (!out.is_open())
        return false;

    out << "digraph VDG_obj" << graph.getObjId() << " {\n";

    graph.forEachSuperNode([&](Version v, VDGNode* node)
    {
        out << "  v" << v
            << " [label=\"o=" << graph.getObjId() << "\\nv=" << v << "\""
            << ", shape=" << (node->isLoadConsume() ? "box" : "ellipse")
            << ", style=filled"
            << ", fillcolor=" << (node->isStoreYield() ? "mistyrose" : "white")
            << "];\n";
    });

    graph.forEachSuperNode([&](Version src, VDGNode* node)
    {
        for (Version dst : node->getSolidOut())
        {
            if (!graph.hasVersion(dst) || !graph.isSuperVersion(dst))
                continue;
            out << "  v" << src << " -> v" << dst << ";\n";
        }

        for (Version dst : node->getVirtualOut())
        {
            if (!graph.hasVersion(dst) || !graph.isSuperVersion(dst))
                continue;
            out << "  v" << src << " -> v" << dst << " [style=dashed];\n";
        }
    });

    out << "}\n";
    return true;
}

} // namespace


bool VDG::addEdge(Version srcV, Version dstV, bool isVirtual)
{
    if (!hasVersion(srcV) || !hasVersion(dstV))
        return false;

    const Version srcRep = getRepVersion(srcV);
    const Version dstRep = getRepVersion(dstV);
    if (srcRep == dstRep)
        return false;

    return addEdgeInternal(srcRep, dstRep, isVirtual);
}


bool VDG::addEdgeInternal(Version srcRep, Version dstRep, bool isVirtual)
{
    assert(srcRep != dstRep && "addEdgeInternal: self-loop not allowed");

    VDGNode* src = getNode(srcRep);
    VDGNode* dst = getNode(dstRep);

    if (isVirtual)
    {
        // Solid edge subsumes virtual edge.
        if (src->solidOut_.contains(dstRep))
            return false;

        if (!src->virtualOut_.insert(dstRep))
            return false;

        const bool insertedIn = dst->virtualIn_.insert(srcRep);
        assert(insertedIn && "VDG virtual in/out edge sets must stay symmetric");
        (void)insertedIn;
        return true;
    }

    if (src->solidOut_.contains(dstRep))
        return false;

    // Upgrade virtual edge to solid edge if present.
    if (src->virtualOut_.erase(dstRep))
    {
        const bool erasedIn = dst->virtualIn_.erase(srcRep);
        assert(erasedIn && "VDG virtual in/out edge sets must stay symmetric");
        (void)erasedIn;
    }

    const bool insertedOut = src->solidOut_.insert(dstRep);
    const bool insertedIn = dst->solidIn_.insert(srcRep);
    assert(insertedOut && insertedIn && "VDG solid in/out edge sets must stay symmetric");
    (void)insertedOut;
    (void)insertedIn;
    return true;
}

bool VDG::removeEdge(Version srcV, Version dstV, bool isVirtual)
{
    if (!hasVersion(srcV) || !hasVersion(dstV))
        return false;

    const Version srcRep = getRepVersion(srcV);
    const Version dstRep = getRepVersion(dstV);

    VDGNode* src = getNode(srcRep);
    VDGNode* dst = getNode(dstRep);

    const bool erasedOut = isVirtual ? src->virtualOut_.erase(dstRep)
                                     : src->solidOut_.erase(dstRep);
    const bool erasedIn = isVirtual ? dst->virtualIn_.erase(srcRep)
                                    : dst->solidIn_.erase(srcRep);

    assert(erasedOut == erasedIn && "VDG edge removal must keep in/out sets symmetric");
    return erasedOut;
}


void VDG::removeAllVirtualEdges()
{
    // Solve phase only propagates on solid edges; virtual edges are build-time
    // helpers and can be dropped eagerly to release memory.
    forEachSuperNode([](Version, VDGNode* node)
    {
        node->virtualOut_.clear();
        node->virtualIn_.clear();
    });
}

void VDG::moveEdgesToRep(Version sub, Version rep)
{
    assert(sub != rep && "moveEdgesToRep: sub and rep must differ");

    VDGNode* subNode = getNode(sub);

    NodeVector solidIn(subNode->solidIn_.begin(), subNode->solidIn_.end());
    NodeVector virtualIn(subNode->virtualIn_.begin(), subNode->virtualIn_.end());
    NodeVector solidOut(subNode->solidOut_.begin(), subNode->solidOut_.end());
    NodeVector virtualOut(subNode->virtualOut_.begin(), subNode->virtualOut_.end());

    for (Version src : solidIn)
    {
        VDGNode* srcNode = getNode(src);
        const bool erasedSrc = srcNode->solidOut_.erase(sub);
        const bool erasedSub = subNode->solidIn_.erase(src);
        assert(erasedSrc && erasedSub && "solid in/out sets must stay symmetric");

        if (src != rep)
            (void)addEdgeInternal(src, rep, false);
    }

    for (Version src : virtualIn)
    {
        VDGNode* srcNode = getNode(src);
        const bool erasedSrc = srcNode->virtualOut_.erase(sub);
        const bool erasedSub = subNode->virtualIn_.erase(src);
        assert(erasedSrc && erasedSub && "virtual in/out sets must stay symmetric");

        if (src != rep)
            (void)addEdgeInternal(src, rep, true);
    }

    for (Version dst : solidOut)
    {
        VDGNode* dstNode = getNode(dst);
        const bool erasedDst = dstNode->solidIn_.erase(sub);
        const bool erasedSub = subNode->solidOut_.erase(dst);
        assert(erasedDst && erasedSub && "solid in/out sets must stay symmetric");

        if (dst != rep)
            (void)addEdgeInternal(rep, dst, false);
    }

    for (Version dst : virtualOut)
    {
        VDGNode* dstNode = getNode(dst);
        const bool erasedDst = dstNode->virtualIn_.erase(sub);
        const bool erasedSub = subNode->virtualOut_.erase(dst);
        assert(erasedDst && erasedSub && "virtual in/out sets must stay symmetric");

        if (dst != rep)
            (void)addEdgeInternal(rep, dst, true);
    }

    assert(subNode->solidIn_.empty() && subNode->virtualIn_.empty()
           && subNode->solidOut_.empty() && subNode->virtualOut_.empty()
           && "sub node must have no incident edge after moveEdgesToRep");
}

void VDG::deleteNode(Version repV)
{
    assert(hasVersion(repV) && isSuperVersion(repV) && "deleteNode: repV must be a valid super version");
    VDGNode* node = getNode(repV);
    NodeBS subs = std::move(subVec_[repV]);
    assert(subs.count() > 0 && "rep should have at least itself as sub version!");

    for (unsigned subU : subs)
    {
        const Version sub = static_cast<Version>(subU);
        assert(sub < capacity() && "sub version out of range in deleteNode");
        verVec_[sub] = nullptr;
        repVec_[sub] = 0;
        superVersions_[sub] = false;
    }

    subVec_[repV].clear();
    delete node;

    assert(nodeNum_ > 0 && "nodeNum underflow in VDG::deleteNode");
    --nodeNum_;
}

void VDG::removeNodeAndEdges(Version repV)
{
    if (!hasVersion(repV) || !isSuperVersion(repV))
        return;

    VDGNode* node = getNode(repV);

    NodeVector solidIn(node->solidIn_.begin(), node->solidIn_.end());
    NodeVector virtualIn(node->virtualIn_.begin(), node->virtualIn_.end());
    NodeVector solidOut(node->solidOut_.begin(), node->solidOut_.end());
    NodeVector virtualOut(node->virtualOut_.begin(), node->virtualOut_.end());

    for (Version src : solidIn)
        (void)removeEdge(src, repV, false);
    for (Version src : virtualIn)
        (void)removeEdge(src, repV, true);
    for (Version dst : solidOut)
        (void)removeEdge(repV, dst, false);
    for (Version dst : virtualOut)
        (void)removeEdge(repV, dst, true);

    deleteNode(repV);
}

void VDG::mergeVersionsIntoRep(const NodeVector& versions, Version repVer)
{
    if (!hasVersion(repVer))
        return;

    repVer = getRepVersion(repVer);
    if (!isSuperVersion(repVer))
        return;

    VDGNode* repNode = getNode(repVer);

    NodeBS allSubs = std::move(subVec_[repVer]);
    if (allSubs.empty())
        allSubs.set(repVer);

    NodeBS repsToMerge;
    for (Version v : versions)
    {
        if (!hasVersion(v))
            continue;
        const Version subRep = getRepVersion(v);
        if (subRep == repVer)
            continue;
        if (!isSuperVersion(subRep))
            continue;
        repsToMerge.set(subRep);
    }

    for (Version subRep : repsToMerge)
    {
        VDGNode* subNode = getNode(subRep);

        repNode->setLoadConsume(subNode->isLoadConsume());
        repNode->setStoreYield(subNode->isStoreYield());
        // Keep stmt-to-node binding semantics stable across all phases.
        repNode->mergeStmtReliance(subNode->getStmtRelianceSet());

        moveEdgesToRep(subRep, repVer);

        NodeBS movedSubs = std::move(subVec_[subRep]);
        if (movedSubs.empty())
            movedSubs.set(subRep);

        if (isSolvePhaseStarted())
            pendingMergedSubs_.push_back(subRep);

        for (unsigned subU : movedSubs)
        {
            const Version sub = static_cast<Version>(subU);
            verVec_[sub] = repNode;
            repVec_[sub] = repVer;
            superVersions_[sub] = false;
            allSubs.set(sub);
        }

        subVec_[subRep].clear();
        superVersions_[subRep] = false;

        delete subNode;
        assert(nodeNum_ > 0 && "nodeNum underflow in VDG::mergeVersionsIntoRep");
        --nodeNum_;
    }

    verVec_[repVer] = repNode;
    repVec_[repVer] = repVer;
    superVersions_[repVer] = true;
    allSubs.set(repVer);
    subVec_[repVer] = std::move(allSubs);
}

NodeVector VDG::sccMergeSolidEdges(const NodeVector& candidates)
{
    VDGSCCDetection scc(this);
    if (candidates.empty())
        scc.find();
    else
        scc.find(candidates);

    auto topoStack = scc.topoNodeStack();
    NodeVector topoOrder;
    topoOrder.reserve(topoStack.size());
    while (!topoStack.empty())
    {
        topoOrder.push_back(topoStack.top());
        topoStack.pop();
    }

    for (Version repV : topoOrder)
    {
        if (!hasVersion(repV) || !isSuperVersion(repV))
            continue;

        const NodeBS& subs = scc.subNodes(repV);
        if (subs.count() <= 1)
            continue;

        NodeVector versions;
        versions.reserve(subs.count());
        for (unsigned subU : subs)
            versions.push_back(static_cast<Version>(subU));

        mergeVersionsIntoRep(versions, repV);
    }

    return topoOrder;
}

void VDG::reverseReachMergeByAnchors()
{
    // Anchors are load-consume nodes and virtual-edge sources.
    NodeVector anchors;
    forEachSuperNode([&](Version v, VDGNode* node)
    {
        if (node->isLoadConsume() || !node->getVirtualOut().empty())
            anchors.push_back(v);
    });

    if (anchors.size() <= 1)
        return;

    std::sort(anchors.begin(), anchors.end());
    anchors.erase(std::unique(anchors.begin(), anchors.end()), anchors.end());
    if (anchors.size() <= 1)
        return;

    // Restrict SCC merging/traversal to anchor-relevant region.
    NodeVector topoOrder = sccMergeSolidEdges(anchors);
    if (topoOrder.size() <= 1)
        return;

    NodeBS anchorReps;
    for (Version v : anchors)
    {
        if (!hasVersion(v))
            continue;
        const Version rep = getRepVersion(v);
        if (!hasVersion(rep) || !isSuperVersion(rep))
            continue;
        anchorReps.set(rep);
    }

    if (anchorReps.count() <= 1)
        return;

    // Compute anchor-reachability by reverse topological DP:
    // reach[v] = anchors reachable from v via (solid|virtual) outgoing edges.
    Map<Version, NodeBS> reach;
    for (auto it = topoOrder.rbegin(); it != topoOrder.rend(); ++it)
    {
        const Version v = *it;
        if (!hasVersion(v) || !isSuperVersion(v))
            continue;

        NodeBS &rv = reach[v];
        if (anchorReps.test(v))
            rv.set(v);

        VDGNode* node = getNode(v);
        for (Version dst : node->getSolidOut())
        {
            if (!hasVersion(dst) || !isSuperVersion(dst))
                continue;
            const auto dIt = reach.find(dst);
            if (dIt != reach.end())
                rv |= dIt->second;
        }
        for (Version dst : node->getVirtualOut())
        {
            if (!hasVersion(dst) || !isSuperVersion(dst))
                continue;
            const auto dIt = reach.find(dst);
            if (dIt != reach.end())
                rv |= dIt->second;
        }
    }

    auto hashNodeBS = [](const NodeBS &bs) -> size_t
    {
        size_t h = 1469598103934665603ull;
        for (unsigned bit : bs)
        {
            h ^= static_cast<size_t>(bit) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
            h *= 1099511628211ull;
        }
        return h;
    };

    Map<size_t, NodeVector> hashLeaders;
    Map<Version, NodeVector> mergeGroups;

    for (Version v : topoOrder)
    {
        if (!hasVersion(v) || !isSuperVersion(v))
            continue;

        const auto vIt = reach.find(v);
        if (vIt == reach.end() || vIt->second.empty())
            continue;

        const NodeBS &vReach = vIt->second;
        const size_t h = hashNodeBS(vReach);
        NodeVector &leaders = hashLeaders[h];

        Version leader = 0;
        for (Version cand : leaders)
        {
            if (!hasVersion(cand) || !isSuperVersion(cand))
                continue;

            const auto cIt = reach.find(cand);
            if (cIt == reach.end())
                continue;
            if (cIt->second == vReach)
            {
                leader = cand;
                break;
            }
        }

        if (leader == 0)
            leaders.push_back(v);
        else
            mergeGroups[leader].push_back(v);
    }

    for (Map<Version, NodeVector>::value_type &kv : mergeGroups)
    {
        const Version leader = kv.first;
        if (!hasVersion(leader) || !isSuperVersion(leader))
            continue;

        NodeVector toMerge;
        for (Version v : kv.second)
        {
            if (!hasVersion(v) || !isSuperVersion(v))
                continue;
            if (getRepVersion(v) == getRepVersion(leader))
                continue;
            toMerge.push_back(v);
        }

        if (!toMerge.empty())
            mergeVersionsIntoRep(toMerge, leader);
    }
}

void VDG::propagateInTopoOrder(PropagateCallback propagate, StmtRelianceCallback onChanged)
{
    assert(hasPendingUpdates() && "propagateInTopoOrder called with no pending updates");
    NodeBS initialUpdated;
    NodeVector seeds;
    seeds.reserve(updatedNodes_.size());

    for (Version v : updatedNodes_)
    {
        if (!hasVersion(v))
            continue;

        const Version rep = getRepVersion(v);

        if (!initialUpdated.test(rep))
        {
            initialUpdated.set(rep);
            seeds.push_back(rep);
        }
    }

    if (seeds.empty())
    {
        clearUpdates();
        return;
    }

    NodeVector topoOrder = sccMergeSolidEdges(seeds);

    NodeBS updatedSet;
    for (Version v : seeds)
    {
        if (!hasVersion(v))
            continue;
        const Version rep = getRepVersion(v);
        if (isSuperVersion(rep))
            updatedSet.set(rep);
    }

    // Solve-stage lightweight strategy: only sync newly-merged sub reps.
    for (const Version subRep : pendingMergedSubs_)
    {
        if (!hasVersion(subRep))
            continue;
        const Version repV = getRepVersion(subRep);
        if (!hasVersion(repV) || !isSuperVersion(repV))
            continue;
        if (subRep == repV)
            continue;

        if (propagate(subRep, repV))
            updatedSet.set(repV);
    }
    
    pendingMergedSubs_.clear();
    for (Version repV : topoOrder)
    {
        if (!hasVersion(repV) || !isSuperVersion(repV))
            continue;
        if (!updatedSet.test(repV))
            continue;

        onChanged(repV);

        for (Version dst : solidOutOf(repV))
        {
            if (!hasVersion(dst) || !isSuperVersion(dst))
                continue;

            if (propagate(repV, dst))
                updatedSet.set(dst);
        }
    }

    clearUpdates();
}

void VDG::pruneUnreachableToLoadConsume()
{
    NodeBS reachable;
    NodeVector worklist;

    forEachSuperNode([&](Version v, VDGNode* node)
    {
        if (!node->isLoadConsume())
            return;
        reachable.set(v);
        worklist.push_back(v);
    });

    while (!worklist.empty())
    {
        const Version v = worklist.back();
        worklist.pop_back();

        VDGNode* node = getNode(v);

        for (Version src : node->getSolidIn())
        {
            if (!isSuperVersion(src) || reachable.test(src))
                continue;
            reachable.set(src);
            worklist.push_back(src);
        }

        for (Version src : node->getVirtualIn())
        {
            if (!isSuperVersion(src) || reachable.test(src))
                continue;
            reachable.set(src);
            worklist.push_back(src);
        }
    }

    NodeVector repsToRemove;
    forEachSuperNode([&](Version repV, VDGNode*)
    {
        if (!reachable.test(repV))
            repsToRemove.push_back(repV);
    });

    for (Version repV : repsToRemove)
        removeNodeAndEdges(repV);
}

void VDG::pruneUnreachableFromStoreYield()
{
    NodeBS reachable;
    NodeVector worklist;

    forEachSuperNode([&](Version v, VDGNode* node)
    {
        if (!node->isStoreYield())
            return;
        reachable.set(v);
        worklist.push_back(v);
    });

    while (!worklist.empty())
    {
        const Version v = worklist.back();
        worklist.pop_back();

        VDGNode* node = getNode(v);

        for (Version dst : node->getSolidOut())
        {
            if (!isSuperVersion(dst) || reachable.test(dst))
                continue;
            reachable.set(dst);
            worklist.push_back(dst);
        }

        for (Version dst : node->getVirtualOut())
        {
            if (!isSuperVersion(dst) || reachable.test(dst))
                continue;
            reachable.set(dst);
            worklist.push_back(dst);
        }
    }

    NodeVector repsToRemove;
    forEachSuperNode([&](Version repV, VDGNode* node)
    {
        if (reachable.test(repV))
            return;
        if (node->isLoadConsume())
            return;
        repsToRemove.push_back(repV);
    });

    for (Version repV : repsToRemove)
        removeNodeAndEdges(repV);
}

namespace
{
void reduceByStableReachabilityInternal(VDG& graph,
                                        bool forward,
                                        bool seedLoadConsume,
                                        const std::function<void(Version)>& pruneVersion)
{
    const u32_t cap = static_cast<u32_t>(graph.capacity());
    std::vector<NodeBS> must(cap);
    std::vector<NodeBS> may(cap);
    NodeBS inWorklist;
    NodeVector worklist;

    graph.forEachSuperNode([&](Version v, VDGNode* node)
    {
        const bool isSeed = seedLoadConsume ? node->isLoadConsume() : node->isStoreYield();
        if (!isSeed)
            return;

        must[v].set(v);
        may[v].set(v);
        inWorklist.set(v);
        worklist.push_back(v);
    });

    auto propagateToNeighbor = [&](Version src, Version neighbor, bool isSolid)
    {
        if (!graph.hasVersion(neighbor) || !graph.isSuperVersion(neighbor))
            return;

        bool changed = false;
        if (isSolid)
        {
            NodeBS& neighborMust = must[neighbor];
            const bool mustChanged = (neighborMust |= must[src]);
            if (mustChanged)
                changed = true;
        }

        NodeBS& neighborMay = may[neighbor];
        const bool mayChanged = (neighborMay |= may[src]);
        if (mayChanged)
            changed = true;

        if (changed && !inWorklist.test(neighbor))
        {
            inWorklist.set(neighbor);
            worklist.push_back(neighbor);
        }
    };

    while (!worklist.empty())
    {
        const Version v = worklist.back();
        worklist.pop_back();
        inWorklist.reset(v);

        if (!graph.hasVersion(v) || !graph.isSuperVersion(v))
            continue;

        VDGNode* node = graph.getNode(v);
        if (forward)
        {
            for (Version dst : node->getSolidOut())
                propagateToNeighbor(v, dst, true);
            for (Version dst : node->getVirtualOut())
                propagateToNeighbor(v, dst, false);
        }
        else
        {
            for (Version src : node->getSolidIn())
                propagateToNeighbor(v, src, true);
            for (Version src : node->getVirtualIn())
                propagateToNeighbor(v, src, false);
        }
    }

    NodeVector toPrune;
    graph.forEachSuperNode([&](Version v, VDGNode*)
    {
        if (may[v].empty())
        {
            assert(must[v].empty() && "must should also be empty when may is empty");
            toPrune.push_back(v);
        }
    });

    for (Version v : toPrune)
        pruneVersion(v);

    auto hashNodeBS = [](const NodeBS& bs) -> size_t
    {
        size_t h = 1469598103934665603ull;
        for (unsigned bit : bs)
        {
            h ^= static_cast<size_t>(bit) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
            h *= 1099511628211ull;
        }
        h ^= static_cast<size_t>(bs.count()) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
        return h;
    };

    Map<size_t, NodeVector> buckets;
    graph.forEachSuperNode([&](Version v, VDGNode*)
    {
        if (must[v] != may[v])
            return;
        buckets[hashNodeBS(must[v])].push_back(v);
    });

    struct StableGroup
    {
        NodeBS stable;
        NodeVector nodes;
    };

    for (Map<size_t, NodeVector>::value_type& bucket : buckets)
    {
        std::vector<StableGroup> groups;
        for (Version v : bucket.second)
        {
            if (!graph.hasVersion(v) || !graph.isSuperVersion(v))
                continue;

            const NodeBS& stable = must[v];
            bool placed = false;
            for (StableGroup& group : groups)
            {
                if (group.stable != stable)
                    continue;
                group.nodes.push_back(v);
                placed = true;
                break;
            }

            if (!placed)
            {
                StableGroup group;
                group.stable = stable;
                group.nodes.push_back(v);
                groups.push_back(std::move(group));
            }
        }

        for (StableGroup& group : groups)
        {
            NodeVector toMerge;
            toMerge.reserve(group.nodes.size());
            for (Version v : group.nodes)
            {
                if (graph.hasVersion(v) && graph.isSuperVersion(v))
                    toMerge.push_back(v);
            }

            if (toMerge.size() <= 1)
                continue;

            if (group.stable.count() == 1)
            {
                const Version stableV = static_cast<Version>(*group.stable.begin());
                if (!graph.hasVersion(stableV))
                    continue;

                const Version stableRep = graph.getRepVersion(stableV);
                if (!graph.hasVersion(stableRep) || !graph.isSuperVersion(stableRep))
                    continue;

                graph.mergeVersionsIntoRep(toMerge, stableRep);
                continue;
            }

            graph.mergeVersionsIntoRep(toMerge, toMerge.front());
        }
    }
}
} // namespace

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
                                       [this](Version v)
                                       {
                                           removeNodeAndEdges(v);
                                       });
}

void VDG::reduceByStableDstReachability()
{
    reduceByStableReachabilityInternal(*this,
                                       /*forward=*/false,
                                       /*seedLoadConsume=*/true,
                                       [this](Version v)
                                       {
                                           removeNodeAndEdges(v);
                                       });
}

void VDG::chainContraction(const NodeVector* seeds)
{
    NodeBS inWorklist;
    NodeVector worklist;

    auto enqueue = [&](Version v)
    {
        if (!hasVersion(v) || !isSuperVersion(v))
            return;
        if (inWorklist.test(v))
            return;
        inWorklist.set(v);
        worklist.push_back(v);
    };

    auto enqueueInNeighbors = [&](Version v)
    {
        if (!hasVersion(v) || !isSuperVersion(v))
            return;
        VDGNode* node = getNode(v);

        // enqueue(v);
        for (Version src : node->getSolidIn()) enqueue(src);
        // for (Version src : node->getVirtualIn()) enqueue(src);
    };

    auto enqueueOutNeighbors = [&](Version v)
    {
        if (!hasVersion(v) || !isSuperVersion(v))
            return;
        VDGNode* node = getNode(v);

        // enqueue(v);
        for (Version dst : node->getSolidOut()) enqueue(dst);
        // for (Version dst : node->getVirtualOut()) enqueue(dst);
    };

    auto tryMergeForward = [&](Version x) -> bool
    {
        VDGNode* xNode = getNode(x);
        if (xNode->isLoadConsume())
            return false;

        Version y = 0;
        bool isVirtual = false;
        if (!xNode->getSingleOutEdge(y, isVirtual) || isVirtual)
            return false;

        // 由于(x,y)合并只改变他们前驱交集的属性（出边集合）和自己的属性
        VDGNode* yNode = getNode(y);
        if(xNode->inSolidDegree()>=yNode->inSolidDegree())
            enqueueInNeighbors(y);
        else
            enqueueInNeighbors(x);

        NodeVector toMerge = {x};
        mergeVersionsIntoRep(toMerge, y);
        // enqueueInNeighbors(y);
        enqueue(y);
        return true;
    };

    auto tryMergeBackward = [&](Version y) -> bool
    {
        VDGNode* yNode = getNode(y);
        if (yNode->isStoreYield())
            return false;

        Version x = 0;
        bool isVirtual = false;
        if (!yNode->getSingleInEdge(x, isVirtual) || isVirtual)
            return false;

        VDGNode* xNode = getNode(x);
        if(xNode->outSolidDegree()>=yNode->outSolidDegree())
            enqueueOutNeighbors(y);
        else
            enqueueOutNeighbors(x);

        NodeVector toMerge = {y};
        mergeVersionsIntoRep(toMerge, x);
        // enqueueOutNeighbors(x);
        enqueue(x);
        return true;
    };

    if (seeds && !seeds->empty())
    {
        for (Version v : *seeds)
            enqueue(v);
    }
    else
    {
        forEachSuperNode([&](Version v, VDGNode*) { enqueue(v); });
    }

    while (!worklist.empty())
    {
        const Version v = worklist.back();
        worklist.pop_back();
        inWorklist.reset(v);

        if (!hasVersion(v) || !isSuperVersion(v))
            continue;

        if (!tryMergeForward(v))
            (void)tryMergeBackward(v);
    }
}

void VDG::transitiveRedundancyElimination()
{
    NodeVector topoOrder = sccMergeSolidEdges();

    const u32_t cap = static_cast<u32_t>(capacity());
    std::vector<DenseBitVector> reach(cap, DenseBitVector(cap));

    // Reverse topological order: successors first, then predecessors.
    for (auto it = topoOrder.rbegin(); it != topoOrder.rend(); ++it)
    {
        const Version v = *it;
        if (!hasVersion(v) || !isSuperVersion(v))
            continue;

        reach[v].set(v);
        for (Version dst : solidOutOf(v))
        {
            if (!hasVersion(dst) || !isSuperVersion(dst))
                continue;
            reach[v] |= reach[dst];
        }
    }

    std::vector<std::pair<Version, Version>> toRemove;

    forEachSuperNode([&](Version src, VDGNode* node)
    {
        NodeVector succs(node->getSolidOut().begin(), node->getSolidOut().end());
        if (succs.size() <= 1)
            return;

        for (Version dst : succs)
        {
            bool redundant = false;
            for (Version mid : succs)
            {
                if (mid == dst)
                    continue;
                if (mid < reach.size() && reach[mid].test(dst))
                {
                    redundant = true;
                    break;
                }
            }
            if (redundant)
                toRemove.emplace_back(src, dst);
        }
    });

    for (const auto& edge : toRemove)
        (void)removeEdge(edge.first, edge.second, false);
}

void VDG::enterSolve()
{
    // Transition from build/simplify to solve.
    removeAllVirtualEdges();
    clearUpdates();
    setSolvePhaseStarted(true);
    pendingMergedSubs_.clear();
}

void VDG::dump(const std::string& filename)
{
    if (!writeSingleVDGDot(*this, filename))
        SVFUtil::errs() << "VDG::dump: cannot open " << normalizeDotPath(filename) << "\n";
}

void VDG::view()
{
    const std::string path = "vdg_obj" + std::to_string(getObjId()) + "_view.dot";
    dump(path);
    SVFUtil::outs() << "VDG::view wrote " << path << "\n";
}

void VDGManager::enterSolveAll()
{
    VDG::setSolvePhaseStarted(true);
    for (auto& entry : vdgMap)
    {
        if (entry.second)
            entry.second->enterSolve();
    }
    pendingVDGs.clear();
    pendingEdgeUpdatesByObj.clear();
}

void VDGManager::dumpStats() const
{
    if (vdgMap.empty())
        return;

    size_t totalVDGs = 0;
    size_t totalSuperNodes = 0;
    size_t totalEdges = 0;
    size_t totalSolidEdges = 0;
    size_t totalVirtualEdges = 0;
    size_t minNodes = std::numeric_limits<size_t>::max();
    size_t maxNodes = 0;
    OrderedMap<size_t, size_t> nodesToObjCount;

    for (const auto& entry : vdgMap)
    {
        const VDG* graph = entry.second.get();
        if (!graph)
            continue;

        ++totalVDGs;

        const size_t nodeCount = countNodes(*graph);

        graph->forEachSuperNode([&](Version, VDGNode* node)
        {
            for (Version dst : node->getSolidOut())
            {
                if (graph->hasVersion(dst) && graph->isSuperVersion(dst))
                {
                    ++totalEdges;
                    ++totalSolidEdges;
                }
            }
            for (Version dst : node->getVirtualOut())
            {
                if (graph->hasVersion(dst) && graph->isSuperVersion(dst))
                {
                    ++totalEdges;
                    ++totalVirtualEdges;
                }
            }
        });

        totalSuperNodes += nodeCount;
        nodesToObjCount[nodeCount] += 1;
        minNodes = std::min(minNodes, nodeCount);
        maxNodes = std::max(maxNodes, nodeCount);
    }

    if (totalVDGs == 0)
        return;

    SVFUtil::outs() << "# VDG stats\n";
    SVFUtil::outs() << "  graphs: " << totalVDGs << "\n";
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

    auto withinThreshold = [&](const VDG& graph) -> bool
    {
        const size_t nodeCount = countNodes(graph);
        if (nodeCount < minNodesPerGraph)
            return false;
        if (maxNodesPerGraph > 0 && nodeCount > maxNodesPerGraph)
            return false;
        return true;
    };

    std::vector<NodeID> objects;
    objects.reserve(vdgMap.size());
    for (const auto& entry : vdgMap)
        objects.push_back(entry.first);
    std::sort(objects.begin(), objects.end());

    if (splitByObject)
    {
        auto ensureTemplateHasToken = [&](const std::string& tmpl) -> std::string
        {
            if (tmpl.find(perObjectToken) != std::string::npos)
                return tmpl;
            if (hasDotSuffix(tmpl))
                return tmpl.substr(0, tmpl.size() - 4) + "_" + perObjectToken + ".dot";
            return tmpl + "_" + perObjectToken;
        };

        auto replaceToken = [&](const std::string& tmpl, NodeID obj) -> std::string
        {
            std::string out = tmpl;
            const std::string objStr = std::to_string(obj);
            size_t pos = 0;
            while ((pos = out.find(perObjectToken, pos)) != std::string::npos)
            {
                out.replace(pos, perObjectToken.size(), objStr);
                pos += objStr.size();
            }
            return out;
        };

        const std::string tmpl = ensureTemplateHasToken(filename);
        for (NodeID obj : objects)
        {
            const auto& graphPtr = vdgMap.at(obj);
            if (!graphPtr || !withinThreshold(*graphPtr))
                continue;
            graphPtr->dump(replaceToken(tmpl, obj));
        }
        return;
    }

    const std::string dotPath = normalizeDotPath(filename);
    std::ofstream out(dotPath);
    if (!out.is_open())
    {
        SVFUtil::errs() << "VDGManager::writeToFile: cannot open " << dotPath << "\n";
        return;
    }

    out << "digraph VDG {\n";

    for (NodeID obj : objects)
    {
        const auto& graphPtr = vdgMap.at(obj);
        if (!graphPtr || !withinThreshold(*graphPtr))
            continue;

        const VDG& graph = *graphPtr;

        out << "  subgraph cluster_obj" << obj << " {\n";
        out << "    label=\"obj=" << obj << "\";\n";
        out << "    style=dashed;\n";

        graph.forEachSuperNode([&](Version v, VDGNode* node)
        {
            out << "    o" << obj << "v" << v
                << " [label=\"o=" << obj << "\\nv=" << v << "\""
                << ", shape=" << (node->isLoadConsume() ? "box" : "ellipse")
                << ", style=filled"
                << ", fillcolor=" << (node->isStoreYield() ? "mistyrose" : "white")
                << "];\n";
        });

        graph.forEachSuperNode([&](Version src, VDGNode* node)
        {
            for (Version dst : node->getSolidOut())
            {
                if (!graph.hasVersion(dst) || !graph.isSuperVersion(dst))
                    continue;
                out << "    o" << obj << "v" << src
                    << " -> o" << obj << "v" << dst << ";\n";
            }

            for (Version dst : node->getVirtualOut())
            {
                if (!graph.hasVersion(dst) || !graph.isSuperVersion(dst))
                    continue;
                out << "    o" << obj << "v" << src
                    << " -> o" << obj << "v" << dst
                    << " [style=dashed];\n";
            }
        });

        out << "  }\n";
    }

    out << "}\n";
    out.close();

    SVFUtil::outs() << "VDG merged graph written to " << dotPath << "\n";
}
