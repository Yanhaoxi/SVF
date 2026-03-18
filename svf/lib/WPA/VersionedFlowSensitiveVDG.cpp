//===- VersionedFlowSensitiveVDG.cpp -- VDG build/simplify pipeline for VFS ---//

#include "Util/GeneralType.h"
#include "WPA/Andersen.h"
#include "WPA/VersionedFlowSensitive.h"
#include "Util/Options.h"
#include "MemoryModel/PointsTo.h"
#include <algorithm>
#include <cassert>
#include <cctype>
#include <cstddef>
#include <limits>
#include <memory>
#include <queue>
#include <utility>

using namespace SVF;

namespace
{
    using VDGSimplifyPass = void (*)(VDG &);

    void registerVDGSimplifyPass(std::vector<VDGSimplifyPass> &passes, VDGSimplifyPass pass)
    {
        passes.push_back(pass);
    }

    void vdgSimplifySCCMerge(VDG &graph)
    {
        (void)graph.sccMergeSolidEdges();
    }

    void vdgSimplifyReverseReachMerge(VDG &graph)
    {
        graph.reverseReachMergeByAnchors();
    }

    void vdgSimplifyStableReachability(VDG &graph)
    {
        graph.reduceByStableSrcReachability();
        graph.reduceByStableDstReachability();
    }

    void vdgSimplifyPrune(VDG &graph)
    {
        graph.pruneUnreachableToLoadConsume();
        graph.pruneUnreachableFromStoreYield();
    }

    void vdgSimplifyChainContraction(VDG &graph)
    {
        graph.chainContraction();
    }

    void vdgSimplifyTransRedundancy(VDG &graph)
    {
        graph.transitiveRedundancyElimination();
    }

    bool registerVDGSimplifyPassByKey(std::vector<VDGSimplifyPass> &passes, char key)
    {
        switch (key)
        {
        case 'S':
            registerVDGSimplifyPass(passes, vdgSimplifySCCMerge);
            return true;
        case 'A':
            registerVDGSimplifyPass(passes, vdgSimplifyReverseReachMerge);
            return true;
        case 'M':
            registerVDGSimplifyPass(passes, vdgSimplifyStableReachability);
            return true;
        case 'P':
            registerVDGSimplifyPass(passes, vdgSimplifyPrune);
            return true;
        case 'T':
            registerVDGSimplifyPass(passes, vdgSimplifyTransRedundancy);
            return true;
        case 'C':
            registerVDGSimplifyPass(passes, vdgSimplifyChainContraction);
            return true;
        default:
            return false;
        }
    }

    void buildVDGSimplifyPassPipeline(std::vector<VDGSimplifyPass> &passes, const std::string &order)
    {
        passes.clear();

        for (char raw : order)
        {
            const unsigned char c = static_cast<unsigned char>(raw);
            if (std::isspace(c) || raw == ',' || raw == ';' || raw == ':' || raw == '-' || raw == '_')
                continue;

            const char key = static_cast<char>(std::toupper(c));
            if (!registerVDGSimplifyPassByKey(passes, key))
                SVFUtil::errs() << "VFS: unknown VDG pass key '" << raw
                                << "' in -vdg-pass-order=" << order << "\n";
        }

        if (!passes.empty())
            return;

        const std::string fallback = "SPC";
        for (char key : fallback)
            (void)registerVDGSimplifyPassByKey(passes, key);
        SVFUtil::errs() << "VFS: empty VDG pass pipeline, fallback to -vdg-pass-order="
                        << fallback << "\n";
    }
}

void VersionedFlowSensitive::prelabel(void)
{
    double start = stat->getClk(true);
    objStartingNodes.clear();
    prelabeledObjects.clear();
    for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        NodeID l = it->first;
        const SVFGNode *ln = it->second;

        if (const StoreSVFGNode *stn = SVFUtil::dyn_cast<StoreSVFGNode>(ln))
        {
            // l: *p = q.
            // If p points to o (Andersen's), l yields a new version for o.
            NodeID p = stn->getPAGDstNodeID();
            for (NodeID o : ander->getPts(p))
            {
                prelabeledObjects.insert(o);
                objStartingNodes[o].push_back(l);
            }

            if (ander->getPts(p).count() != 0) ++numPrelabeledNodes;
        }
        else if (delta(l))
        {
            // The outgoing edges are not only what will later be propagated. SVFGOPT may
            // move around nodes such that there can be an MRSVFGNode with no incoming or
            // outgoing edges which will be added at runtime. In essence, we can no
            // longer rely on the outgoing edges of a delta node when SVFGOPT is enabled.
            const MRSVFGNode *mr = SVFUtil::dyn_cast<MRSVFGNode>(ln);
            if (mr != nullptr)
            {
                for (const NodeID o : mr->getPointsTo())
                {
                    prelabeledObjects.insert(o);
                    objStartingNodes[o].push_back(l);
                }

                if (mr->getPointsTo().count() != 0) ++numPrelabeledNodes;
            }
        }
    }

    for (Map<NodeID, NodeVector>::value_type &ov : objStartingNodes)
    {
        NodeVector &starts = ov.second;
        if (starts.empty())
            continue;
        std::sort(starts.begin(), starts.end());
        starts.erase(std::unique(starts.begin(), starts.end()), starts.end());
    }

    double end = stat->getClk(true);
    prelabelingTime = (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::buildVDG(void)
{
    const double labelStart = stat->getClk(true);

    vdgManager.clear();
    pendingStoreObjsByLoc.clear();
    consume.clear();
    yield.clear();

    std::vector<VDGSimplifyPass> passes;
    buildVDGSimplifyPassPipeline(passes, Options::VDGPassOrder());
    const bool enableProfile = Options::VDGStat();

    struct BuildVDGProfileTotals
    {
        u64_t objects = 0;
        u64_t emptyStartObjects = 0;
        u64_t step1WavePops = 0;
        u64_t step1OutEdges = 0;
        u64_t step1MatchedIndirectEdges = 0;
        u64_t step1DeltaSourceHits = 0;
        u64_t step1DeltaCandidates = 0;
        u64_t step1DeltaAccepted = 0;
        u64_t plannedSolidEdges = 0;
        u64_t plannedVirtualEdges = 0;
        u64_t materializeNodeCalls = 0;
        u64_t materializeEdgeCalls = 0;
        u64_t shrinkNodeCalls = 0;
        u64_t shrinkEdgeCalls = 0;
        double perObjTicks = 0.0;
        double step1Ticks = 0.0;
        double step2NodeTicks = 0.0;
        double step2EdgeTicks = 0.0;
        double step2SimplifyTicks = 0.0;
        double step3PrepTicks = 0.0;
        double step3RebuildTicks = 0.0;
        double step3PublishTicks = 0.0;
    } profile;

    std::vector<double> simplifyPassTicks(passes.size(), 0.0);
    std::vector<u64_t> simplifyPassRuns(passes.size(), 0);
    std::vector<u64_t> simplifyPassNodeSum(passes.size(), 0);
    std::vector<u64_t> simplifyPassNodeMax(passes.size(), 0);
    std::vector<u64_t> simplifyPassEdgeSum(passes.size(), 0);
    std::vector<u64_t> simplifyPassEdgeMax(passes.size(), 0);

    // Cache possible delta destinations per delta-source statement (srcId).
    // This is object-independent and should be built once per srcId.
    Map<NodeID, NodeVector> deltaDstCache;
    auto getDeltaDstsForSrc = [this, &deltaDstCache](NodeID srcId) -> const NodeVector&
    {
        const auto cached = deltaDstCache.find(srcId);
        if (cached != deltaDstCache.end())
            return cached->second;

        NodeVector dsts;
        const SVFGNode *srcNode = svfg->getSVFGNode(srcId);
        if (srcNode != nullptr)
        {
            if (const ActualINSVFGNode *actualIn = SVFUtil::dyn_cast<ActualINSVFGNode>(srcNode))
            {
                const CallICFGNode *cs = actualIn->getCallSite();
                if (cs && cs->isIndirectCall())
                {
                    CallGraph *cg = ander->getCallGraph();
                    if (cg->hasCallGraphEdge(cs))
                    {
                        for (CallGraph::CallGraphEdgeSet::const_iterator it = cg->getCallEdgeBegin(cs),
                             eit = cg->getCallEdgeEnd(cs); it != eit; ++it)
                        {
                            const FunObjVar *callee = (*it)->getDstNode()->getFunction();
                            if (!svfg->hasFormalINSVFGNodes(callee)) continue;
                            const SVFG::FormalINSVFGNodeSet &formalIns = svfg->getFormalINSVFGNodes(callee);
                            for (const NodeID dstId : formalIns)
                            {
                                if (!delta(dstId))
                                    continue;
                                dsts.push_back(dstId);
                            }
                        }
                    }
                }
            }
            else if (const FormalOUTSVFGNode *formalOut = SVFUtil::dyn_cast<FormalOUTSVFGNode>(srcNode))
            {
                const FunExitICFGNode *exitNode = formalOut->getFunExitNode();
                const FunObjVar *fun = exitNode ? exitNode->getFun() : nullptr;
                if (fun != nullptr)
                {
                    CallGraphEdge::CallInstSet callsites;
                    ander->getCallGraph()->getIndCallSitesInvokingCallee(fun, callsites);
                    for (const CallICFGNode *cs : callsites)
                    {
                        if (!svfg->hasActualOUTSVFGNodes(cs)) continue;
                        const SVFG::ActualOUTSVFGNodeSet &actualOuts = svfg->getActualOUTSVFGNodes(cs);
                        for (const NodeID dstId : actualOuts)
                        {
                            if (!delta(dstId))
                                continue;
                            dsts.push_back(dstId);
                        }
                    }
                }
            }
        }

        if (!dsts.empty())
        {
            std::sort(dsts.begin(), dsts.end());
            dsts.erase(std::unique(dsts.begin(), dsts.end()), dsts.end());
        }

        const auto inserted = deltaDstCache.emplace(srcId, std::move(dsts));
        return inserted.first->second;
    };

    const size_t totalSVFGNodes = svfg->getTotalNodeNum();
    std::vector<bool> visited(totalSVFGNodes, false);
    NodeVector touchedVisited;
    touchedVisited.reserve(totalSVFGNodes / 6 + 1);

    auto resetVisitedMarks = [&visited, &touchedVisited]()
    {
        for (const NodeID n : touchedVisited)
            visited[n] = false;
        touchedVisited.clear();
    };

    auto markVisited = [&visited, &touchedVisited](const NodeID n) -> bool
    {
        if (n >= visited.size() || visited[n])
            return false;
        visited[n] = true;
        touchedVisited.push_back(n);
        return true;
    };

    for (const NodeID o : prelabeledObjects)
    {
        const double objStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        if (enableProfile)
            ++profile.objects;

        resetVisitedMarks();

        static const NodeVector emptyStartingNodes;
        const Map<NodeID, NodeVector>::const_iterator startsIt = objStartingNodes.find(o);
        const NodeVector &osStartingNodes
            = startsIt == objStartingNodes.end() ? emptyStartingNodes : startsIt->second;
        if (enableProfile && osStartingNodes.empty())
            ++profile.emptyStartObjects;

        VDG *graph = vdgManager.getOrCreateVDG(o);

        LocToVersionMap objectConsume;
        LocToVersionMap objectYield;
        std::vector<std::pair<Version, NodeID>> osStmtReliance;
        std::vector<std::pair<Version, Version>> solidEdges;
        std::vector<std::pair<Version, Version>> virtualEdges;

        Version nextVersion = invalidVersion;

        auto addPlannedEdge = [&solidEdges, &virtualEdges](Version src, Version dst, bool isVirtual)
        {
            if (src == invalidVersion || dst == invalidVersion || src == dst)
                return;
            if (isVirtual)
                virtualEdges.emplace_back(src, dst);
            else
                solidEdges.emplace_back(src, dst);
        };

        auto getOrCreateConsumeVersion = [this, &objectConsume, &osStmtReliance, &nextVersion](const NodeID stmtId) -> Version
        {
            const auto found = objectConsume.find(stmtId);
            if (found != objectConsume.end())
                return found->second;

            const Version v = ++nextVersion;
            objectConsume[stmtId] = v;
            if (isLoad(stmtId))
                osStmtReliance.emplace_back(v, stmtId);
            return v;
        };

        auto getOrCreateStoreYieldVersion = [this,
                                             &objectYield,
                                             &getOrCreateConsumeVersion,
                                             &nextVersion,
                                             &addPlannedEdge](const NodeID storeId) -> Version
        {
            const auto found = objectYield.find(storeId);
            if (found != objectYield.end())
                return found->second;

            const Version consumeV = getOrCreateConsumeVersion(storeId);
            const Version yieldV = ++nextVersion;
            objectYield[storeId] = yieldV;

            const StoreSVFGNode *store = SVFUtil::dyn_cast<StoreSVFGNode>(svfg->getSVFGNode(storeId));
            if (store != nullptr)
            {
                // const PointsTo &dstVPts = getPts(store->getPAGDstNodeID());
                // const size_t dstCount = dstVPts.count();
                // const bool addSolidStoreEdge =
                //     dstCount >= 2 || (dstCount == 1 && *dstVPts.begin() != o);

                // addPlannedEdge(consumeV, yieldV, !addSolidStoreEdge);
                addPlannedEdge(consumeV, yieldV, true);
                // if (!addSolidStoreEdge)
                //     pendingStoreObjsByLoc[storeId].push_back(o);
            }

            return yieldV;
        };

        // --- step 1: traverse object footprint and collect versions/edges only ---
        const double step1StartTicks = enableProfile ? stat->getClk(true) : 0.0;
        std::queue<const SVFGNode *> waveQueue;
        // 预处理起始节点
        for (const NodeID startId : osStartingNodes)
        {
            const SVFGNode *startNode = svfg->getSVFGNode(startId);
            if (startNode == nullptr)
                continue;

            (void)getOrCreateConsumeVersion(startId);
            if (isStore(startId))
                (void)getOrCreateStoreYieldVersion(startId);

            if (markVisited(startId))
                waveQueue.push(startNode);
        }
        // 沿着 SVFG 收集信息
        while (!waveQueue.empty())
        {
            const SVFGNode *src = waveQueue.front();
            waveQueue.pop();
            if (enableProfile)
                ++profile.step1WavePops;

            const NodeID srcId = src->getId();
            const Version srcConsumeV = getOrCreateConsumeVersion(srcId);
            const Version srcV = isStore(srcId) ? getOrCreateStoreYieldVersion(srcId) : srcConsumeV;

            for (const SVFGEdge *edge : src->getOutEdges())
            {
                if (enableProfile)
                    ++profile.step1OutEdges;
                const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge);
                if (!ie)
                    continue;
                if (!ie->getPointsTo().test(o))
                    continue;
                if (enableProfile)
                    ++profile.step1MatchedIndirectEdges;

                const SVFGNode *dst = ie->getDstNode();
                const NodeID dstId = dst->getId();
                const Version dstConsumeV = getOrCreateConsumeVersion(dstId);
                if (isStore(dstId))
                    (void)getOrCreateStoreYieldVersion(dstId);

                addPlannedEdge(srcV, dstConsumeV, false);

                // Keep old SCC semantics: record edge/node, but do not expand from store/delta.
                if (delta(dstId) || isStore(dstId))
                    continue;

                if (markVisited(dstId))
                    waveQueue.push(dst);
            }
            if (deltaSource(srcId))
            {
                if (enableProfile)
                    ++profile.step1DeltaSourceHits;
                const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(src);
                if (!srcMR || !srcMR->getPointsTo().test(o))
                    continue;

                const NodeVector &deltaDsts = getDeltaDstsForSrc(srcId);
                for (const NodeID dstId : deltaDsts)
                {
                    if (enableProfile)
                        ++profile.step1DeltaCandidates;
                    const SVFGNode *dstNode = svfg->getSVFGNode(dstId);
                    const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dstNode);
                    if (!dstMR || !dstMR->getPointsTo().test(o))
                        continue;
                    if (enableProfile)
                        ++profile.step1DeltaAccepted;

                    assert(delta(dstId) && "VFS::buildVDG: delta-source cache should only target delta nodes!");

                    const Version dstConsumeV = getOrCreateConsumeVersion(dstId);
                    if (isStore(dstId))
                        (void)getOrCreateStoreYieldVersion(dstId);
                    addPlannedEdge(srcV, dstConsumeV, true);

                    // Keep old SCC semantics: do not expand from store/delta.
                    if (delta(dstId) || isStore(dstId))
                        continue;

                    if (dstNode != nullptr && markVisited(dstId))
                        waveQueue.push(dstNode);
                }
            }
        }
        if (enableProfile)
            profile.step1Ticks += stat->getClk(true) - step1StartTicks;
        if (enableProfile)
        {
            profile.plannedSolidEdges += static_cast<u64_t>(solidEdges.size());
            profile.plannedVirtualEdges += static_cast<u64_t>(virtualEdges.size());
        }

        // --- step 2: materialize dense nodes/edges, then simplify + bind labels ---
        if (nextVersion != invalidVersion)
            graph->ensureVersionCapacity(nextVersion);

        const double step2NodeStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        // label node
        for (const LocToVersionMap::value_type &lv : objectConsume)
        {
            graph->getOrAddNode(lv.second, isLoad(lv.first), false);
            if (enableProfile)
                ++profile.materializeNodeCalls;
        }
        for (const LocToVersionMap::value_type &lv : objectYield)
        {
            graph->getOrAddNode(lv.second, false, true);
            if (enableProfile)
                ++profile.materializeNodeCalls;
        }
        if (enableProfile)
            profile.step2NodeTicks += stat->getClk(true) - step2NodeStartTicks;

        const double step2EdgeStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        // add edges
        for (const std::pair<Version, Version> &edge : solidEdges)
        {
            graph->addEdge(edge.first, edge.second, false);
            if (enableProfile)
                ++profile.materializeEdgeCalls;
        }
        for (const std::pair<Version, Version> &edge : virtualEdges)
        {
            graph->addEdge(edge.first, edge.second, true);
            if (enableProfile)
                ++profile.materializeEdgeCalls;
        }
        if (enableProfile)
            profile.step2EdgeTicks += stat->getClk(true) - step2EdgeStartTicks;

        const double step2SimplifyStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
        {
            const double passStartTicks = enableProfile ? stat->getClk(true) : 0.0;
            passes[passIdx](*graph);
            if (enableProfile)
            {
                simplifyPassTicks[passIdx] += stat->getClk(true) - passStartTicks;
                ++simplifyPassRuns[passIdx];

                const u64_t nodeCount = static_cast<u64_t>(graph->getTotalNodeNum());
                u64_t edgeCount = 0;
                graph->forEachSuperNode([&edgeCount](Version, VDGNode *node)
                {
                    edgeCount += static_cast<u64_t>(node->getSolidOut().size() + node->getVirtualOut().size());
                });

                simplifyPassNodeSum[passIdx] += nodeCount;
                simplifyPassEdgeSum[passIdx] += edgeCount;
                if (nodeCount > simplifyPassNodeMax[passIdx])
                    simplifyPassNodeMax[passIdx] = nodeCount;
                if (edgeCount > simplifyPassEdgeMax[passIdx])
                    simplifyPassEdgeMax[passIdx] = edgeCount;
            }
        }
        if (enableProfile)
            profile.step2SimplifyTicks += stat->getClk(true) - step2SimplifyStartTicks;

        // --- step 3: shrink inside object pipeline, then map labels ---
        const double step3PrepStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        VDG *oldGraph = graph;
        NodeVector oldReps;
        oldReps.reserve(oldGraph->getTotalNodeNum());
        oldGraph->forEachSuperNode([&oldReps](Version oldV, VDGNode *)
        {
            oldReps.push_back(oldV);
        });

        const size_t oldCap = oldGraph->capacity();
        std::vector<Version> oldToNew(oldCap, invalidVersion);
        Version nextNewV = invalidVersion;
        for (const Version oldV : oldReps)
            oldToNew[oldV] = ++nextNewV;

        auto mapToShrunkRep = [oldGraph, &oldToNew](Version oldV) -> Version
        {
            if (oldV == invalidVersion || !oldGraph->hasVersion(oldV))
                return invalidVersion;
            const Version oldRepV = oldGraph->getRepVersion(oldV);
            if (oldRepV == invalidVersion || !oldGraph->hasVersion(oldRepV))
                return invalidVersion;
            if (static_cast<size_t>(oldRepV) >= oldToNew.size())
                return invalidVersion;
            return oldToNew[oldRepV];
        };

        std::vector<std::pair<NodeID, Version>> remappedConsumes;
        remappedConsumes.reserve(objectConsume.size());
        for (const LocToVersionMap::value_type &lv : objectConsume)
        {
            const Version newV = mapToShrunkRep(lv.second);
            if (newV != invalidVersion)
                remappedConsumes.emplace_back(lv.first, newV);
        }

        std::vector<std::pair<NodeID, Version>> remappedYields;
        remappedYields.reserve(objectYield.size());
        for (const LocToVersionMap::value_type &lv : objectYield)
        {
            const Version newV = mapToShrunkRep(lv.second);
            if (newV != invalidVersion)
                remappedYields.emplace_back(lv.first, newV);
        }

        std::vector<std::pair<Version, NodeID>> remappedStmtReliance;
        remappedStmtReliance.reserve(osStmtReliance.size());
        for (const std::pair<Version, NodeID> &vs : osStmtReliance)
        {
            const Version newV = mapToShrunkRep(vs.first);
            if (newV != invalidVersion)
                remappedStmtReliance.emplace_back(newV, vs.second);
        }
        if (enableProfile)
            profile.step3PrepTicks += stat->getClk(true) - step3PrepStartTicks;

        const double step3RebuildStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        std::unique_ptr<VDG> newGraph = std::make_unique<VDG>(o);
        if (nextNewV != invalidVersion)
            newGraph->ensureVersionCapacity(nextNewV);

        // Materialize shrunk nodes.
        for (const Version oldV : oldReps)
        {
            const Version newV = oldToNew[oldV];
            VDGNode *oldNode = oldGraph->getNode(oldV);
            newGraph->getOrAddNode(newV, oldNode->isLoadConsume(), oldNode->isStoreYield());
            if (enableProfile)
                ++profile.shrinkNodeCalls;
        }

        // Rebuild edges in the shrunk graph.
        for (const Version oldSrc : oldReps)
        {
            const Version newSrc = oldToNew[oldSrc];
            VDGNode *oldNode = oldGraph->getNode(oldSrc);

            for (const Version oldDst : oldNode->getSolidOut())
            {
                if (static_cast<size_t>(oldDst) >= oldToNew.size())
                    continue;
                const Version newDst = oldToNew[oldDst];
                if (newDst != invalidVersion)
                {
                    (void)newGraph->addEdge(newSrc, newDst, false);
                    if (enableProfile)
                        ++profile.shrinkEdgeCalls;
                }
            }

            for (const Version oldDst : oldNode->getVirtualOut())
            {
                if (static_cast<size_t>(oldDst) >= oldToNew.size())
                    continue;
                const Version newDst = oldToNew[oldDst];
                if (newDst != invalidVersion)
                {
                    (void)newGraph->addEdge(newSrc, newDst, true);
                    if (enableProfile)
                        ++profile.shrinkEdgeCalls;
                }
            }
        }
        if (enableProfile)
            profile.step3RebuildTicks += stat->getClk(true) - step3RebuildStartTicks;

        // Publish shrunk graph for this object.
        const double step3PublishStartTicks = enableProfile ? stat->getClk(true) : 0.0;
        VDGManager::VDGMapTy &allVDGs = vdgManager.getAllVDGs();
        VDGManager::VDGMapTy::iterator vdgIt = allVDGs.find(o);
        assert(vdgIt != allVDGs.end() && "VDG must exist for current object");
        vdgIt->second = std::move(newGraph);
        graph = vdgIt->second.get();

        // Rebuild pending singleton-upgrade list only for store c->y edges
        // that survive simplify/shrink as virtual edges in the final graph.
        LocToVersionMap remappedConsumeByLoc;
        remappedConsumeByLoc.reserve(remappedConsumes.size());
        for (const std::pair<NodeID, Version> &lv : remappedConsumes)
            remappedConsumeByLoc[lv.first] = lv.second;

        for (const std::pair<NodeID, Version> &lv : remappedYields)
        {
            const NodeID storeId = lv.first;
            const Version y = lv.second;
            const auto cIt = remappedConsumeByLoc.find(storeId);
            if (cIt == remappedConsumeByLoc.end())
                continue;

            const Version c = cIt->second;
            if (c == invalidVersion || y == invalidVersion || c == y)
                continue;
            if (!graph->hasVersion(c) || !graph->hasVersion(y))
                continue;

            const VDGNode *cNode = graph->getNode(c);
            if (cNode->getVirtualOut().contains(y) && !cNode->getSolidOut().contains(y))
                pendingStoreObjsByLoc[storeId].push_back(o);
        }

        // Map consume/yield/reliance after shrink.
        for (const std::pair<NodeID, Version> &lv : remappedConsumes)
            setConsume(lv.first, o, lv.second);

        for (const std::pair<NodeID, Version> &lv : remappedYields)
            setYield(lv.first, o, lv.second);

        for (const std::pair<Version, NodeID> &vs : remappedStmtReliance)
            graph->bindStmtRelianceStmt(vs.first, vs.second);
        if (enableProfile)
        {
            const double objEndTicks = stat->getClk(true);
            profile.step3PublishTicks += objEndTicks - step3PublishStartTicks;
            profile.perObjTicks += objEndTicks - objStartTicks;
        }
    }

    const double totalEndTicks = stat->getClk(true);
    vdgBuildTime = (totalEndTicks - labelStart) / TIMEINTERVAL;

    if (enableProfile)
    {
        auto passNameOf = [](VDGSimplifyPass pass) -> const char *
        {
            if (pass == vdgSimplifySCCMerge) return "scc_merge";
            if (pass == vdgSimplifyReverseReachMerge) return "reverse_reach_merge";
            if (pass == vdgSimplifyStableReachability) return "stable_reachability";
            if (pass == vdgSimplifyPrune) return "prune";
            if (pass == vdgSimplifyTransRedundancy) return "transitive_redundancy";
            if (pass == vdgSimplifyChainContraction) return "chain_contraction";
            return "unknown";
        };

        SVFUtil::outs()
            << "buildVDG.profile.summary\tobjects:" << profile.objects
            << " emptyStart:" << profile.emptyStartObjects
            << " totalTime:" << (totalEndTicks - labelStart) / TIMEINTERVAL
            << " objPipelineTime:" << profile.perObjTicks / TIMEINTERVAL
            << "\n";

        SVFUtil::outs()
            << "buildVDG.profile.step1\twavePops:" << profile.step1WavePops
            << " outEdges:" << profile.step1OutEdges
            << " matchedIndirect:" << profile.step1MatchedIndirectEdges
            << " deltaSrcHits:" << profile.step1DeltaSourceHits
            << " deltaCandidates:" << profile.step1DeltaCandidates
            << " deltaAccepted:" << profile.step1DeltaAccepted
            << " plannedSolid:" << profile.plannedSolidEdges
            << " plannedVirtual:" << profile.plannedVirtualEdges
            << " time:" << profile.step1Ticks / TIMEINTERVAL
            << "\n";

        SVFUtil::outs()
            << "buildVDG.profile.step2\tgetOrAddNodeCalls:" << profile.materializeNodeCalls
            << " addEdgeCalls:" << profile.materializeEdgeCalls
            << " nodeTime:" << profile.step2NodeTicks / TIMEINTERVAL
            << " edgeTime:" << profile.step2EdgeTicks / TIMEINTERVAL
            << " simplifyTime:" << profile.step2SimplifyTicks / TIMEINTERVAL
            << "\n";

        for (size_t i = 0; i < passes.size(); ++i)
        {
            const u64_t runs = simplifyPassRuns[i];
            const double avgNodeCount = runs == 0
                ? 0.0
                : static_cast<double>(simplifyPassNodeSum[i]) / static_cast<double>(runs);
            const double avgEdgeCount = runs == 0
                ? 0.0
                : static_cast<double>(simplifyPassEdgeSum[i]) / static_cast<double>(runs);
            SVFUtil::outs()
                << "buildVDG.profile.pass\tidx:" << i
                << " name:" << passNameOf(passes[i])
                << " runs:" << runs
                << " time:" << simplifyPassTicks[i] / TIMEINTERVAL
                << " nodeAvg:" << avgNodeCount
                << " nodeMax:" << simplifyPassNodeMax[i]
                << " edgeAvg:" << avgEdgeCount
                << " edgeMax:" << simplifyPassEdgeMax[i]
                << "\n";
        }

        SVFUtil::outs()
            << "buildVDG.profile.step3\tnewNodeCalls:" << profile.shrinkNodeCalls
            << " addEdgeCalls:" << profile.shrinkEdgeCalls
            << " prepTime:" << profile.step3PrepTicks / TIMEINTERVAL
            << " rebuildTime:" << profile.step3RebuildTicks / TIMEINTERVAL
            << " publishTime:" << profile.step3PublishTicks / TIMEINTERVAL
            << "\n";
    }
}
