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

    void vdgSimplifyStoreVirtualBFSMerge(VDG &graph)
    {
        graph.bfsMergeByStoreYieldAndVirtualIn();
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
        case 'B':
            registerVDGSimplifyPass(passes, vdgSimplifyStoreVirtualBFSMerge);
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

    // Object-local version DSU for equivalence merges.
    // parent[v] == 0 means v is a root.
    struct VersionDSU
    {
        std::vector<Version> parent;
        std::vector<u32_t> rank;

        void reset(const Version maxVersion)
        {
            parent.assign(static_cast<size_t>(maxVersion) + 1, 0);
            rank.assign(static_cast<size_t>(maxVersion) + 1, 0);
        }

        inline bool valid(const Version v) const
        {
            return v != VersionedFlowSensitive::invalidVersion && static_cast<size_t>(v) < parent.size();
        }

        Version find(const Version v)
        {
            if (!valid(v))
                return VersionedFlowSensitive::invalidVersion;

            const Version p = parent[v];
            if (p == 0)
                return v;

            parent[v] = find(p);
            return parent[v];
        }

        bool unite(const Version lhs, const Version rhs)
        {
            Version rl = find(lhs);
            Version rr = find(rhs);
            if (rl == VersionedFlowSensitive::invalidVersion
                || rr == VersionedFlowSensitive::invalidVersion
                || rl == rr)
                return false;

            if (rank[rl] < rank[rr])
                std::swap(rl, rr);

            parent[rr] = rl;
            if (rank[rl] == rank[rr])
                ++rank[rl];
            return true;
        }
    };
}

void VersionedFlowSensitive::prelabel(void)
{
    // 由 Load 节点出发
    double start = stat->getClk(true);
    objStartingNodes.clear();
    prelabeledObjects.clear();
    for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        NodeID l = it->first;
        const SVFGNode *ln = it->second;

        if (const LoadSVFGNode *ldn = SVFUtil::dyn_cast<LoadSVFGNode>(ln))
        {
            // l: p = *q.
            // If q points to o (Andersen's), l yields a new version for o.
            NodeID q = ldn->getPAGSrcNodeID();
            for (NodeID o : ander->getPts(q))
            {
                prelabeledObjects.insert(o);
                objStartingNodes[o].push_back(l);
            }
        }
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

    struct BuildVDGHotProfile
    {
        u64_t objects = 0;
        double step1Ticks = 0.0;
        double step2Ticks = 0.0;
        double step3Ticks = 0.0;
        double step4Ticks = 0.0;
        u64_t compressObjects = 0;
        u64_t preDenseVersionTotal = 0;
        u64_t preDenseVersionMax = 0;
        u64_t denseVersionTotal = 0;
        u64_t denseVersionMax = 0;
    } profile;

    std::vector<u64_t> passRuns(passes.size(), 0);
    std::vector<u64_t> passVDGNodeTotal(passes.size(), 0);
    std::vector<u64_t> passVDGNodeMax(passes.size(), 0);
    const size_t totalSVFGNodes = svfg->getTotalNodeNum();

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

    Map<NodeID, NodeVector> deltaSrcCacheByDst;
    for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
    {
        const NodeID srcId = it->first;
        if (!deltaSource(srcId))
            continue;

        const NodeVector &deltaDsts = getDeltaDstsForSrc(srcId);
        for (const NodeID dstId : deltaDsts)
            deltaSrcCacheByDst[dstId].push_back(srcId);
    }
    for (Map<NodeID, NodeVector>::value_type &entry : deltaSrcCacheByDst)
    {
        NodeVector &srcs = entry.second;
        if (srcs.empty())
            continue;
        std::sort(srcs.begin(), srcs.end());
        srcs.erase(std::unique(srcs.begin(), srcs.end()), srcs.end());
    }
    // Release src->dst cache immediately after reverse index is built.
    Map<NodeID, NodeVector>().swap(deltaDstCache);

    std::vector<bool> discovered(totalSVFGNodes, false);
    NodeVector touchedDiscovered;
    touchedDiscovered.reserve(totalSVFGNodes / 6 + 1);

    auto resetDiscoveredMarks = [&discovered, &touchedDiscovered]()
    {
        for (const NodeID n : touchedDiscovered)
            discovered[n] = false;
        touchedDiscovered.clear();
    };

    auto markDiscovered = [&discovered, &touchedDiscovered](const NodeID n) -> bool
    {
        if (n >= discovered.size() || discovered[n])
            return false;
        discovered[n] = true;
        touchedDiscovered.push_back(n);
        return true;
    };

    // Object-local dense version maps (stmtId -> version), reused across objects.
    std::vector<Version> consumeVersionByLoc(totalSVFGNodes, invalidVersion);
    std::vector<Version> yieldVersionByLoc(totalSVFGNodes, invalidVersion);
    NodeVector touchedConsumeLocs;
    NodeVector touchedYieldLocs;
    touchedConsumeLocs.reserve(totalSVFGNodes / 6 + 1);
    touchedYieldLocs.reserve(totalSVFGNodes / 12 + 1);

    auto resetObjectDenseVersionMaps = [
                                         &consumeVersionByLoc,
                                         &yieldVersionByLoc,
                                         &touchedConsumeLocs,
                                         &touchedYieldLocs
                                        ]()
    {
        for (const NodeID stmtId : touchedConsumeLocs)
            consumeVersionByLoc[stmtId] = invalidVersion;
        touchedConsumeLocs.clear();

        for (const NodeID stmtId : touchedYieldLocs)
            yieldVersionByLoc[stmtId] = invalidVersion;
        touchedYieldLocs.clear();
    };

    const NodeVector emptyStartingNodes;
    for (const NodeID o : prelabeledObjects)
    {
        if (enableProfile)
            ++profile.objects;
        resetDiscoveredMarks();
        resetObjectDenseVersionMaps();

        const Map<NodeID, NodeVector>::const_iterator startsIt = objStartingNodes.find(o);
        const NodeVector &osStartingNodes
            = startsIt == objStartingNodes.end() ? emptyStartingNodes : startsIt->second;

        VDG *graph = vdgManager.getOrCreateVDG(o);

        std::vector<std::pair<Version, NodeID>> osStmtReliance; // 绑定在该 version 上的 load 语句
        std::vector<std::pair<Version, Version>> Edges; // solid cflow 依赖边
        std::vector<std::pair<Version, Version>> VEdges; // virtual 依赖边
        std::vector<std::pair<Version, Version>> Equiv; // 等价版本

        Version nextVersion = invalidVersion;

        // 更新 consume 版本 记录 load 语句依赖
        auto getOrCreateConsumeVersion = [
                                           this,
                                           &consumeVersionByLoc,
                                           &touchedConsumeLocs,
                                           &osStmtReliance,
                                           &nextVersion
                                          ](const NodeID stmtId) -> Version
        {
            assert(static_cast<size_t>(stmtId) < consumeVersionByLoc.size() && "stmtId out of dense consume map range");
            Version &slot = consumeVersionByLoc[stmtId];
            if (slot != invalidVersion)
                return slot;

            slot = ++nextVersion;
            touchedConsumeLocs.push_back(stmtId);
            if (isLoad(stmtId))
                osStmtReliance.emplace_back(slot, stmtId);
            return slot;
        };

        // 更新 yield 版本
        auto getOrCreateStoreYieldVersion = [
                                             &yieldVersionByLoc,
                                             &touchedYieldLocs,
                                             &nextVersion
                                            ](const NodeID storeId) -> Version
        {
            assert(static_cast<size_t>(storeId) < yieldVersionByLoc.size() && "storeId out of dense yield map range");
            Version &slot = yieldVersionByLoc[storeId];
            if (slot != invalidVersion)
                return slot;

            slot = ++nextVersion;
            touchedYieldLocs.push_back(storeId);
            return slot;
        };

        // --- step 1: traverse object footprint and collect versions/edges only ---
        const double step1StartTicks = enableProfile ? stat->getClk(true) : 0.0;
        std::queue<const SVFGNode *> waveQueue;

        // 预处理起始 Load 节点
        for (const NodeID startId : osStartingNodes)
        {
            const SVFGNode *startNode = svfg->getSVFGNode(startId);
            if (startNode == nullptr)
                continue;
            assert(SVFUtil::isa<LoadSVFGNode>(startNode) && "starting nodes should be loads");
            (void)getOrCreateConsumeVersion(startId);
            if (markDiscovered(startId))
                waveQueue.push(startNode);
        }

        // Reverse walk from load anchors along incoming indirect edges.
        // For each matched edge src --o--> dst, add src(version)->dst(consume-version).
        // Meanwhile, gather equivalence among versions when possible (single non-delta/store pred).
        while (!waveQueue.empty())
        {
            const SVFGNode *dst = waveQueue.front();
            waveQueue.pop();

            const NodeID dstId = dst->getId();
            const Version dstConsumeV = getOrCreateConsumeVersion(dstId);
            const bool dstIsDelta = delta(dstId);

            unsigned inedge = 0;
            Version singlePredV = invalidVersion;
            for (const SVFGEdge *edge : dst->getInEdges())
            {
                const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge);
                if (!ie)
                    continue;
                if (!ie->getPointsTo().test(o))
                    continue;
                inedge++;

                const SVFGNode *src = ie->getSrcNode();
                const NodeID srcId = src->getId();
                const Version srcConsumeV = getOrCreateConsumeVersion(srcId);
                const Version srcV = isStore(srcId) ? getOrCreateStoreYieldVersion(srcId) : srcConsumeV;
                if (dstIsDelta)
                {
                    Edges.emplace_back(srcV, dstConsumeV);
                }
                else if (inedge == 1)
                {
                    // For non-delta dst, defer emitting the first edge until we know
                    // whether this is truly single-predecessor (only Equiv needed).
                    singlePredV = srcV;
                    assert(singlePredV != invalidVersion && "single pred version should be valid");
                }
                else
                {
                    // The second predecessor confirms this dst is not single-pred:
                    // flush deferred first edge, then append current edge.
                    if (inedge == 2)
                    {
                        assert(singlePredV != invalidVersion && "deferred first pred should be valid");
                        Edges.emplace_back(singlePredV, dstConsumeV);
                    }
                    Edges.emplace_back(srcV, dstConsumeV);
                }

                if (markDiscovered(srcId))
                    waveQueue.push(src);
            }

            // 后向收缩 (delta 有虚入边所以不做收缩)
            if (!dstIsDelta)
            {
                if(inedge == 1){
                    Equiv.emplace_back(dstConsumeV, singlePredV);
                }
                continue;
            }

            const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dst);
            if (!dstMR || !dstMR->getPointsTo().test(o))
                continue;

            const Map<NodeID, NodeVector>::const_iterator deltaSrcIt = deltaSrcCacheByDst.find(dstId);
            if (deltaSrcIt == deltaSrcCacheByDst.end())
                continue;

            for (const NodeID srcId : deltaSrcIt->second)
            {
                const SVFGNode *srcNode = svfg->getSVFGNode(srcId);
                const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
                if (!srcMR || !srcMR->getPointsTo().test(o))
                    continue;

                const Version srcConsumeV = getOrCreateConsumeVersion(srcId);
                const Version srcV = isStore(srcId) ? getOrCreateStoreYieldVersion(srcId) : srcConsumeV;
                VEdges.emplace_back(srcV, dstConsumeV);

                if (srcNode != nullptr && markDiscovered(srcId))
                    waveQueue.push(srcNode);
            }
        }
        if (enableProfile)
            profile.step1Ticks += stat->getClk(true) - step1StartTicks;

        const Version nextVersionBeforeDense = nextVersion;

        // step 2: 基于 DSU 合并等价版本 (单前驱非 delta 版本)，并重映射版本号到连续空间
        const double step2StartTicks = enableProfile ? stat->getClk(true) : 0.0;
        VersionDSU equivDsu;
        equivDsu.reset(nextVersion);
        for (const std::pair<Version, Version> &eq : Equiv)
            (void)equivDsu.unite(eq.first, eq.second);

        // Build root -> dense-version map (1..N) after DSU is frozen.
        // Versions are already dense in [1..nextVersion], so vector remap is
        // cheaper than per-lookup hash maps in this hot path.
        std::vector<Version> rootToDense(static_cast<size_t>(nextVersion) + 1, invalidVersion);
        std::vector<Version> versionToDense(static_cast<size_t>(nextVersion) + 1, invalidVersion);
        Version nextDenseVersion = invalidVersion;
        for (Version v = invalidVersion + 1; v <= nextVersion; ++v)
        {
            const Version root = equivDsu.find(v);
            if (root == VersionedFlowSensitive::invalidVersion)
                continue;

            Version &denseSlot = rootToDense[root];
            if (denseSlot == invalidVersion)
            {
                denseSlot = ++nextDenseVersion;
            }
            versionToDense[v] = denseSlot;
        }

        auto toDenseVersion = [&versionToDense](const Version oldV) -> Version
        {
            if (oldV == invalidVersion)
                return invalidVersion;
            const size_t idx = static_cast<size_t>(oldV);
            if (idx >= versionToDense.size())
                return invalidVersion;
            return versionToDense[idx];
        };

        // Rewrite all versioned artifacts to dense ids before materialization.
        for (const NodeID stmtId : touchedConsumeLocs)
            consumeVersionByLoc[stmtId] = toDenseVersion(consumeVersionByLoc[stmtId]);
        for (const NodeID stmtId : touchedYieldLocs)
            yieldVersionByLoc[stmtId] = toDenseVersion(yieldVersionByLoc[stmtId]);
        for (std::pair<Version, NodeID> &vs : osStmtReliance)
            vs.first = toDenseVersion(vs.first);

        size_t edgeWrite = 0;
        for (const std::pair<Version, Version> &edge : Edges)
        {
            const Version src = toDenseVersion(edge.first);
            const Version dst = toDenseVersion(edge.second);
            if (src == invalidVersion || dst == invalidVersion || src == dst)
                continue;
            Edges[edgeWrite++] = std::make_pair(src, dst);
        }
        Edges.resize(edgeWrite);

        size_t vedgeWrite = 0;
        for (const std::pair<Version, Version> &edge : VEdges)
        {
            const Version src = toDenseVersion(edge.first);
            const Version dst = toDenseVersion(edge.second);
            if (src == invalidVersion || dst == invalidVersion || src == dst)
                continue;
            VEdges[vedgeWrite++] = std::make_pair(src, dst);
        }
        VEdges.resize(vedgeWrite);

        nextVersion = nextDenseVersion;
        if (enableProfile)
            profile.step2Ticks += stat->getClk(true) - step2StartTicks;

        // --- step 3: materialize dense nodes/edges, then run simplify passes ---
        const double step3StartTicks = enableProfile ? stat->getClk(true) : 0.0;
        if (nextVersion != invalidVersion)
            graph->ensureVersionCapacity(nextVersion);

        // label node
        for (const NodeID stmtId : touchedConsumeLocs)
        {
            const Version consumeV = consumeVersionByLoc[stmtId];
            if (consumeV == invalidVersion)
                continue;
            graph->getOrAddNode(consumeV, isLoad(stmtId), false);
        }
        for (const NodeID stmtId : touchedYieldLocs)
        {
            const Version yieldV = yieldVersionByLoc[stmtId];
            if (yieldV == invalidVersion)
                continue;
            graph->getOrAddNode(yieldV, false, true);
        }
        // add edges
        for (const std::pair<Version, Version> &edge : Edges)
        {
            graph->addEdge(edge.first, edge.second, false);
        }
        for (const std::pair<Version, Version> &edge : VEdges)
        {
            graph->addEdge(edge.first, edge.second, true);
        }
        // add store consume->yield virtual edges
        for (const NodeID storeId : touchedYieldLocs)
        {
            const Version yieldV = yieldVersionByLoc[storeId];
            const Version consumeV = consumeVersionByLoc[storeId];
            if (consumeV != invalidVersion && yieldV != invalidVersion && consumeV != yieldV)
            {
                (void)graph->addEdge(consumeV, yieldV, true);
            }
        }

        for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
        {
            passes[passIdx](*graph);
            if (enableProfile)
            {
                const u64_t nodesAfterPass = static_cast<u64_t>(graph->getTotalNodeNum());
                ++passRuns[passIdx];
                passVDGNodeTotal[passIdx] += nodesAfterPass;
                if (nodesAfterPass > passVDGNodeMax[passIdx])
                    passVDGNodeMax[passIdx] = nodesAfterPass;
            }
        }
        if (enableProfile)
            profile.step3Ticks += stat->getClk(true) - step3StartTicks;

        // --- step 4: shrink/publish inside object pipeline, then map labels ---
        const double step4StartTicks = enableProfile ? stat->getClk(true) : 0.0;
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
        remappedConsumes.reserve(touchedConsumeLocs.size());
        for (const NodeID stmtId : touchedConsumeLocs)
        {
            const Version newV = mapToShrunkRep(consumeVersionByLoc[stmtId]);
            if (newV != invalidVersion)
                remappedConsumes.emplace_back(stmtId, newV);
        }

        std::vector<std::pair<NodeID, Version>> remappedYields;
        remappedYields.reserve(touchedYieldLocs.size());
        for (const NodeID stmtId : touchedYieldLocs)
        {
            const Version newV = mapToShrunkRep(yieldVersionByLoc[stmtId]);
            if (newV != invalidVersion)
                remappedYields.emplace_back(stmtId, newV);
        }

        std::vector<std::pair<Version, NodeID>> remappedStmtReliance;
        remappedStmtReliance.reserve(osStmtReliance.size());
        for (const std::pair<Version, NodeID> &vs : osStmtReliance)
        {
            const Version newV = mapToShrunkRep(vs.first);
            if (newV != invalidVersion)
                remappedStmtReliance.emplace_back(newV, vs.second);
        }

        std::unique_ptr<VDG> newGraph = std::make_unique<VDG>(o);
        if (nextNewV != invalidVersion)
            newGraph->ensureVersionCapacity(nextNewV);

        // Materialize shrunk nodes.
        for (const Version oldV : oldReps)
        {
            const Version newV = oldToNew[oldV];
            VDGNode *oldNode = oldGraph->getNode(oldV);
            newGraph->getOrAddNode(newV, oldNode->isLoadConsume(), oldNode->isStoreYield());
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
                }
            }
        }

        // Publish shrunk graph for this object.
        VDGManager::VDGMapTy &allVDGs = vdgManager.getAllVDGs();
        VDGManager::VDGMapTy::iterator vdgIt = allVDGs.find(o);
        assert(vdgIt != allVDGs.end() && "VDG must exist for current object");
        vdgIt->second = std::move(newGraph);
        graph = vdgIt->second.get();
        if (enableProfile)
        {
            ++profile.compressObjects;
            profile.preDenseVersionTotal += static_cast<u64_t>(nextVersionBeforeDense);
            profile.denseVersionTotal += static_cast<u64_t>(nextDenseVersion);
            if (static_cast<u64_t>(nextVersionBeforeDense) > profile.preDenseVersionMax)
                profile.preDenseVersionMax = static_cast<u64_t>(nextVersionBeforeDense);
            if (static_cast<u64_t>(nextDenseVersion) > profile.denseVersionMax)
                profile.denseVersionMax = static_cast<u64_t>(nextDenseVersion);
        }

        // Rebuild pending singleton-upgrade list only for store c->y edges
        // that survive simplify/shrink as virtual edges in the final graph.
        LocToVersionMap remappedConsumeByLoc;
        remappedConsumeByLoc.reserve(remappedConsumes.size());
        for (const std::pair<NodeID, Version> &lv : remappedConsumes)
            remappedConsumeByLoc[lv.first] = lv.second;

        // Check store stmt consume/yield consistency after shrink.
        // If consume/yield differ, keep a virtual c->y edge and record pending upgrade.
        for (const std::pair<NodeID, Version> &lv : remappedYields)
        {
            const NodeID storeId = lv.first;
            const Version yieldV = lv.second;
            const auto cIt = remappedConsumeByLoc.find(storeId);
            if (cIt == remappedConsumeByLoc.end())
                continue;

            const Version consumeV = cIt->second;
            if (consumeV == invalidVersion || yieldV == invalidVersion)
                continue;

            const bool consumeYieldConsistent = (consumeV == yieldV);
            if (consumeYieldConsistent)
                continue;

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
            profile.step4Ticks += stat->getClk(true) - step4StartTicks;
    }
    // Release reverse delta cache after build loop completes.
    Map<NodeID, NodeVector>().swap(deltaSrcCacheByDst);

    const double totalEndTicks = stat->getClk(true);
    vdgBuildTime = (totalEndTicks - labelStart) / TIMEINTERVAL;

    if (enableProfile)
    {
        SVFUtil::outs()
            << "buildVDG.hot.summary\tobjects:" << profile.objects
            << " totalTime:" << vdgBuildTime
            << " step1Time:" << profile.step1Ticks / TIMEINTERVAL
            << " step2Time:" << profile.step2Ticks / TIMEINTERVAL
            << " step3Time:" << profile.step3Ticks / TIMEINTERVAL
            << " step4Time:" << profile.step4Ticks / TIMEINTERVAL
            << "\n";

        SVFUtil::outs()
            << "buildVDG.compress.summary\tobjects:" << profile.compressObjects
            << " nextVersionTotal:" << profile.preDenseVersionTotal
            << " nextVersionMax:" << profile.preDenseVersionMax
            << " denseVersionTotal:" << profile.denseVersionTotal
            << " denseVersionMax:" << profile.denseVersionMax
            << "\n";

        for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
        {
            SVFUtil::outs()
                << "buildVDG.pass.summary\tidx:" << passIdx
                << " runs:" << passRuns[passIdx]
                << " vdgNodeTotal:" << passVDGNodeTotal[passIdx]
                << " vdgNodeMax:" << passVDGNodeMax[passIdx]
                << "\n";
        }
    }
}
