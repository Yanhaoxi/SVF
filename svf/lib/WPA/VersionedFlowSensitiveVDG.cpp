//===- VersionedFlowSensitiveVDG.cpp -- VDG build/simplify pipeline for VFS ---//

#include "Util/GeneralType.h"
#include "WPA/Andersen.h"
#include "WPA/VersionedFlowSensitive.h"
#include "Util/Options.h"
#include "MemoryModel/PointsTo.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <cctype>
#include <cstddef>
#include <functional>
#include <limits>
#include <memory>
#include <queue>
#include <string>
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

    void vdgSimplifyLoadVirtualBFSMerge(VDG &graph)
    {
        graph.bfsMergeByLoadConsumeAndVirtualOut();
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
        case 'L':
            registerVDGSimplifyPass(passes, vdgSimplifyLoadVirtualBFSMerge);
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

    void runSVFGPassProfiling(const VersionedFlowSensitive &pta, const SVFG *svfg);
}

void VersionedFlowSensitive::prelabel(void)
{
    // 由 Load 节点出发
    double start = stat->getClk(true);
    objStartingNodes.clear();
    prelabeledObjects.clear();
    fiObjects.clear();
    numPrelabelNodes = 0;
    numPrelabelFIObjs = 0;
    for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        NodeID l = it->first;
        const SVFGNode *ln = it->second;

        if (const LoadSVFGNode *ldn = SVFUtil::dyn_cast<LoadSVFGNode>(ln))
        {
            // l: p = *q.
            // If q points to o (Andersen's), l yields a new version for o.
            NodeID q = ldn->getPAGSrcNodeID();
            bool hasPrelabelObj = false;
            for (NodeID o : ander->getPts(q))
            {
                prelabeledObjects.insert(o);
                objStartingNodes[o].push_back(l);
                hasPrelabelObj = true;
            }
            if (hasPrelabelObj)
                ++numPrelabelNodes;
        }
    }
    // Pre-estimate non-strong-update objects.
    for (const NodeID o : prelabeledObjects)
    {
        if (isHeapMemObj(o) || isArrayMemObj(o)
            || pag->getBaseObject(o)->isFieldInsensitive()
            || isLocalVarInRecursiveFun(o))
        {
            fiObjects.insert(o);
        }
    }
    numPrelabelFIObjs = static_cast<u32_t>(fiObjects.size());

    double end = stat->getClk(true);
    prelabelingTime = (end - start) / TIMEINTERVAL;
    if (Options::VDGStat())
    {
        SVFUtil::outs()
            << "prelabel.summary\tloadNodes:" << numPrelabelNodes
            << " objects:" << prelabeledObjects.size()
            << " fiObjects:" << numPrelabelFIObjs
            << " time:" << prelabelingTime
            << "\n";
    }
}

void VersionedFlowSensitive::buildVDG(void)
{
    const double labelStart = stat->getClk(true);

    vdgManager.clear();
    pendingStoreObjsByLoc.clear();
    consume.clear();
    yield.clear();

    if (Options::VDGPassProfile())
    {
        runSVFGPassProfiling(*this, svfg);
        const double totalEndTicks = stat->getClk(true);
        vdgBuildTime = (totalEndTicks - labelStart) / TIMEINTERVAL;
        return;
    }

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
    std::vector<double> passTicks(passes.size(), 0.0);
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
                const bool keepVirtualStoreCY
                    = !Options::VFSObjFSLowerBound()
                    || fiObjects.find(o) == fiObjects.end();
                (void)graph->addEdge(consumeV, yieldV, keepVirtualStoreCY);
            }
        }

        for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
        {
            const double passStartTicks = enableProfile ? stat->getClk(true) : 0.0;
            passes[passIdx](*graph);
            if (enableProfile)
            {
                passTicks[passIdx] += stat->getClk(true) - passStartTicks;
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
            const double passTime = passTicks[passIdx] / TIMEINTERVAL;
            SVFUtil::outs()
                << "buildVDG.pass.summary\tidx:" << passIdx
                << " runs:" << passRuns[passIdx]
                << " vdgNodeTotal:" << passVDGNodeTotal[passIdx]
                << " vdgNodeMax:" << passVDGNodeMax[passIdx]
                << " passTime:" << passTime
                << "\n";
        }
    }

}

namespace
{
    enum class VDGProfileSVFGTy : u8_t
    {
        Addr = 0,
        Copy = 1,
        Gep = 2,
        Load = 3,
        Store = 4,
        Phi = 5,
        ActualParm = 6,
        FormalParm = 7,
        ActualRet = 8,
        FormalRet = 9,
        ActualIn = 10,
        ActualOut = 11,
        FormalIn = 12,
        FormalOut = 13,
        MSSAPhi = 14,
        DummyVersionProp = 15,
        Other = 16,
        Count = 17
    };

    static constexpr size_t kVDGProfileSVFGTyCount = static_cast<size_t>(VDGProfileSVFGTy::Count);
    using VDGTypeCountArray = std::array<u64_t, kVDGProfileSVFGTyCount>;

    enum class ProfileNodeRole : u8_t
    {
        Normal = 0,
        StoreConsume = 1,
        StoreYield = 2
    };

    using ProfileKey = u64_t;

    struct ProfileNode
    {
        VDGProfileSVFGTy svfgTy = VDGProfileSVFGTy::Other;
        bool loadConsume = false;
        bool storeYield = false;
        Set<ProfileKey> solidOut;
        Set<ProfileKey> solidIn;
        Set<ProfileKey> virtualOut;
        Set<ProfileKey> virtualIn;
    };

    struct ProfileGraph
    {
        Map<ProfileKey, ProfileNode> nodes;
    };

    inline ProfileKey makeProfileKey(const NodeID stmtId, const ProfileNodeRole role)
    {
        return (static_cast<ProfileKey>(stmtId) << 2) | static_cast<ProfileKey>(role);
    }

    inline NodeID getStmtIdFromProfileKey(const ProfileKey key)
    {
        return static_cast<NodeID>(key >> 2);
    }

    inline ProfileNodeRole getRoleFromProfileKey(const ProfileKey key)
    {
        return static_cast<ProfileNodeRole>(key & static_cast<ProfileKey>(0x3));
    }

    inline size_t svfgTyIndex(const VDGProfileSVFGTy ty)
    {
        return static_cast<size_t>(ty);
    }

    inline const char* svfgTyName(const VDGProfileSVFGTy ty)
    {
        switch (ty)
        {
        case VDGProfileSVFGTy::Addr:
            return "Addr";
        case VDGProfileSVFGTy::Copy:
            return "Copy";
        case VDGProfileSVFGTy::Gep:
            return "Gep";
        case VDGProfileSVFGTy::Load:
            return "Load";
        case VDGProfileSVFGTy::Store:
            return "Store";
        case VDGProfileSVFGTy::Phi:
            return "Phi";
        case VDGProfileSVFGTy::ActualParm:
            return "ActualParm";
        case VDGProfileSVFGTy::FormalParm:
            return "FormalParm";
        case VDGProfileSVFGTy::ActualRet:
            return "ActualRet";
        case VDGProfileSVFGTy::FormalRet:
            return "FormalRet";
        case VDGProfileSVFGTy::ActualIn:
            return "ActualIn";
        case VDGProfileSVFGTy::ActualOut:
            return "ActualOut";
        case VDGProfileSVFGTy::FormalIn:
            return "FormalIn";
        case VDGProfileSVFGTy::FormalOut:
            return "FormalOut";
        case VDGProfileSVFGTy::MSSAPhi:
            return "MSSAPhi";
        case VDGProfileSVFGTy::DummyVersionProp:
            return "DummyVersionProp";
        case VDGProfileSVFGTy::Other:
            return "Other";
        default:
            return "Unknown";
        }
    }

    inline VDGProfileSVFGTy classifySVFGNodeType(const SVFGNode *node)
    {
        if (node == nullptr) return VDGProfileSVFGTy::Other;
        if (SVFUtil::isa<AddrSVFGNode>(node)) return VDGProfileSVFGTy::Addr;
        if (SVFUtil::isa<LoadSVFGNode>(node)) return VDGProfileSVFGTy::Load;
        if (SVFUtil::isa<StoreSVFGNode>(node)) return VDGProfileSVFGTy::Store;
        if (SVFUtil::isa<GepSVFGNode>(node)) return VDGProfileSVFGTy::Gep;
        if (SVFUtil::isa<PHISVFGNode>(node)) return VDGProfileSVFGTy::Phi;
        if (SVFUtil::isa<ActualParmSVFGNode>(node)) return VDGProfileSVFGTy::ActualParm;
        if (SVFUtil::isa<FormalParmSVFGNode>(node)) return VDGProfileSVFGTy::FormalParm;
        if (SVFUtil::isa<ActualRetSVFGNode>(node)) return VDGProfileSVFGTy::ActualRet;
        if (SVFUtil::isa<FormalRetSVFGNode>(node)) return VDGProfileSVFGTy::FormalRet;
        if (SVFUtil::isa<ActualINSVFGNode>(node)) return VDGProfileSVFGTy::ActualIn;
        if (SVFUtil::isa<ActualOUTSVFGNode>(node)) return VDGProfileSVFGTy::ActualOut;
        if (SVFUtil::isa<FormalINSVFGNode>(node)) return VDGProfileSVFGTy::FormalIn;
        if (SVFUtil::isa<FormalOUTSVFGNode>(node)) return VDGProfileSVFGTy::FormalOut;
        if (SVFUtil::isa<MSSAPHISVFGNode>(node)) return VDGProfileSVFGTy::MSSAPhi;
        if (SVFUtil::isa<DummyVersionPropSVFGNode>(node)) return VDGProfileSVFGTy::DummyVersionProp;
        if (SVFUtil::isa<CopySVFGNode>(node)) return VDGProfileSVFGTy::Copy;
        return VDGProfileSVFGTy::Other;
    }

    inline bool isLoadConsumeRole(const SVFGNode *stmtNode, const ProfileNodeRole role)
    {
        return role == ProfileNodeRole::Normal && SVFUtil::isa<LoadSVFGNode>(stmtNode);
    }

    inline bool isStoreYieldRole(const ProfileNodeRole role)
    {
        return role == ProfileNodeRole::StoreYield;
    }

    std::string buildSVFGTypePatternKey(const VDGTypeCountArray &typeCounts)
    {
        std::string key;
        for (size_t i = 0; i < kVDGProfileSVFGTyCount; ++i)
        {
            const u64_t cnt = typeCounts[i];
            if (cnt == 0)
                continue;
            if (!key.empty())
                key += "|";
            key += svfgTyName(static_cast<VDGProfileSVFGTy>(i));
            key += ":";
            key += std::to_string(cnt);
        }
        if (key.empty())
            return "None";
        return key;
    }

    inline ProfileNode &getOrCreateProfileNode(ProfileGraph &graph, const ProfileKey key, const SVFG *svfg)
    {
        ProfileNode &node = graph.nodes[key];
        const NodeID stmtId = getStmtIdFromProfileKey(key);
        const ProfileNodeRole role = getRoleFromProfileKey(key);
        const SVFGNode *stmtNode = svfg->getSVFGNode(stmtId);
        node.svfgTy = classifySVFGNodeType(stmtNode);
        node.loadConsume = node.loadConsume || isLoadConsumeRole(stmtNode, role);
        node.storeYield = node.storeYield || isStoreYieldRole(role);
        return node;
    }

    inline bool addProfileEdge(ProfileGraph &graph,
                               const ProfileKey src,
                               const ProfileKey dst,
                               const bool isVirtual,
                               const SVFG *svfg)
    {
        ProfileNode &srcNode = getOrCreateProfileNode(graph, src, svfg);
        ProfileNode &dstNode = getOrCreateProfileNode(graph, dst, svfg);
        bool inserted = false;
        if (isVirtual)
        {
            inserted = srcNode.virtualOut.insert(dst).second;
            dstNode.virtualIn.insert(src);
        }
        else
        {
            inserted = srcNode.solidOut.insert(dst).second;
            dstNode.solidIn.insert(src);
        }
        return inserted;
    }

    void printSortedPatternCounts(const std::string &prefix,
                                  const Map<std::string, u64_t> &counts,
                                  const size_t limit = 0)
    {
        std::vector<std::pair<std::string, u64_t>> ordered(counts.begin(), counts.end());
        std::sort(ordered.begin(), ordered.end(),
                  [](const std::pair<std::string, u64_t> &lhs, const std::pair<std::string, u64_t> &rhs)
        {
            if (lhs.second != rhs.second)
                return lhs.second > rhs.second;
            return lhs.first < rhs.first;
        });

        const size_t maxPrint = (limit == 0) ? ordered.size() : std::min(limit, ordered.size());
        for (size_t i = 0; i < maxPrint; ++i)
        {
            SVFUtil::outs()
                << prefix
                << "\tidx:" << i
                << " pattern:" << ordered[i].first
                << " count:" << ordered[i].second
                << "\n";
        }
        if (maxPrint < ordered.size())
        {
            SVFUtil::outs()
                << prefix
                << "\ttruncated:" << (ordered.size() - maxPrint)
                << "\n";
        }
    }

    struct VDGPassProfileAggregate
    {
        u64_t graphs = 0;
        u64_t nodeMapObjects = 0;
        u64_t nodeMapEntries = 0;
        u64_t solidEdges = 0;
        u64_t virtualEdges = 0;

        u64_t forwardPairs = 0;
        u64_t backwardPairs = 0;
        u64_t bothForwardBackwardPairs = 0;
        Map<std::string, u64_t> forwardPatterns;
        Map<std::string, u64_t> backwardPatterns;

        u64_t sccCount = 0;
        u64_t sccTotalNodes = 0;
        u64_t sccNonTrivialCount = 0;
        u64_t sccNonTrivialNodes = 0;
        u64_t sccMaxSize = 0;
        Map<std::string, u64_t> sccPatternCounts;

        u64_t storeReachableNodes = 0;
        u64_t loadReverseReachableNodes = 0;
        u64_t bothReachableNodes = 0;
    };

    void profileVDGObjectForPassPatterns(const ProfileGraph &graph, VDGPassProfileAggregate &agg)
    {
        if (graph.nodes.empty())
            return;

        ++agg.graphs;
        ++agg.nodeMapObjects;
        agg.nodeMapEntries += static_cast<u64_t>(graph.nodes.size());

        for (const auto &kn : graph.nodes)
        {
            const ProfileNode &node = kn.second;
            agg.solidEdges += static_cast<u64_t>(node.solidOut.size());
            agg.virtualEdges += static_cast<u64_t>(node.virtualOut.size());

            bool forwardMatched = false;
            if (node.solidOut.size() == 1 && !node.loadConsume)
            {
                const ProfileKey dst = *node.solidOut.begin();
                const auto dstIt = graph.nodes.find(dst);
                if (dstIt != graph.nodes.end())
                {
                    const std::string key = std::string(svfgTyName(node.svfgTy))
                                          + "->" + svfgTyName(dstIt->second.svfgTy);
                    ++agg.forwardPatterns[key];
                    ++agg.forwardPairs;
                    forwardMatched = true;
                }
            }

            bool backwardMatched = false;
            if (node.solidIn.size() == 1 && node.virtualIn.empty() && !node.storeYield)
            {
                const ProfileKey src = *node.solidIn.begin();
                const auto srcIt = graph.nodes.find(src);
                if (srcIt != graph.nodes.end())
                {
                    const std::string key = std::string(svfgTyName(srcIt->second.svfgTy))
                                          + "->" + svfgTyName(node.svfgTy);
                    ++agg.backwardPatterns[key];
                    ++agg.backwardPairs;
                    backwardMatched = true;
                }
            }

            if (forwardMatched && backwardMatched)
                ++agg.bothForwardBackwardPairs;
        }

        // Tarjan SCC on solid edges.
        Map<ProfileKey, u64_t> index;
        Map<ProfileKey, u64_t> lowlink;
        Set<ProfileKey> onStack;
        std::vector<ProfileKey> stack;
        u64_t nextIndex = 1;

        std::function<void(ProfileKey)> strongConnect = [&](ProfileKey v)
        {
            index[v] = nextIndex;
            lowlink[v] = nextIndex;
            ++nextIndex;
            stack.push_back(v);
            onStack.insert(v);

            const auto vIt = graph.nodes.find(v);
            if (vIt != graph.nodes.end())
            {
                for (const ProfileKey w : vIt->second.solidOut)
                {
                    if (graph.nodes.find(w) == graph.nodes.end())
                        continue;

                    if (index.find(w) == index.end())
                    {
                        strongConnect(w);
                        lowlink[v] = std::min(lowlink[v], lowlink[w]);
                    }
                    else if (onStack.find(w) != onStack.end())
                    {
                        lowlink[v] = std::min(lowlink[v], index[w]);
                    }
                }
            }

            if (lowlink[v] == index[v])
            {
                VDGTypeCountArray kindCnt{};
                u64_t sccSize = 0;
                while (!stack.empty())
                {
                    const ProfileKey w = stack.back();
                    stack.pop_back();
                    onStack.erase(w);
                    ++sccSize;
                    const auto wIt = graph.nodes.find(w);
                    if (wIt != graph.nodes.end())
                        ++kindCnt[svfgTyIndex(wIt->second.svfgTy)];
                    if (w == v)
                        break;
                }

                ++agg.sccCount;
                agg.sccTotalNodes += sccSize;
                if (sccSize > 1)
                {
                    ++agg.sccNonTrivialCount;
                    agg.sccNonTrivialNodes += sccSize;
                }
                if (sccSize > agg.sccMaxSize)
                    agg.sccMaxSize = sccSize;
                ++agg.sccPatternCounts[buildSVFGTypePatternKey(kindCnt)];
            }
        };

        for (const auto &kn : graph.nodes)
        {
            const ProfileKey v = kn.first;
            if (index.find(v) == index.end())
                strongConnect(v);
        }

        // Step5: reachability ratios over solid edges.
        Set<ProfileKey> storeSeen;
        std::queue<ProfileKey> storeQ;
        for (const auto &kn : graph.nodes)
        {
            if (!kn.second.storeYield)
                continue;
            if (storeSeen.insert(kn.first).second)
                storeQ.push(kn.first);
        }
        while (!storeQ.empty())
        {
            const ProfileKey cur = storeQ.front();
            storeQ.pop();
            const auto curIt = graph.nodes.find(cur);
            if (curIt == graph.nodes.end())
                continue;
            for (const ProfileKey dst : curIt->second.solidOut)
            {
                if (graph.nodes.find(dst) == graph.nodes.end())
                    continue;
                if (storeSeen.insert(dst).second)
                    storeQ.push(dst);
            }
        }
        agg.storeReachableNodes += static_cast<u64_t>(storeSeen.size());

        Set<ProfileKey> loadRevSeen;
        std::queue<ProfileKey> loadRevQ;
        for (const auto &kn : graph.nodes)
        {
            if (!kn.second.loadConsume)
                continue;
            if (loadRevSeen.insert(kn.first).second)
                loadRevQ.push(kn.first);
        }
        while (!loadRevQ.empty())
        {
            const ProfileKey cur = loadRevQ.front();
            loadRevQ.pop();
            const auto curIt = graph.nodes.find(cur);
            if (curIt == graph.nodes.end())
                continue;
            for (const ProfileKey src : curIt->second.solidIn)
            {
                if (graph.nodes.find(src) == graph.nodes.end())
                    continue;
                if (loadRevSeen.insert(src).second)
                    loadRevQ.push(src);
            }
        }
        agg.loadReverseReachableNodes += static_cast<u64_t>(loadRevSeen.size());

        u64_t bothReachable = 0;
        if (storeSeen.size() <= loadRevSeen.size())
        {
            for (const ProfileKey key : storeSeen)
            {
                if (loadRevSeen.find(key) != loadRevSeen.end())
                    ++bothReachable;
            }
        }
        else
        {
            for (const ProfileKey key : loadRevSeen)
            {
                if (storeSeen.find(key) != storeSeen.end())
                    ++bothReachable;
            }
        }
        agg.bothReachableNodes += bothReachable;
    }

    void dumpVDGPassProfile(const VDGPassProfileAggregate &agg)
    {
        const u64_t solidSolidVirtualDen = agg.solidEdges + agg.virtualEdges;
        const double step2Ratio = solidSolidVirtualDen == 0
                                ? 0.0
                                : static_cast<double>(agg.forwardPairs)
                                / static_cast<double>(solidSolidVirtualDen);
        const double step3Ratio = solidSolidVirtualDen == 0
                                ? 0.0
                                : static_cast<double>(agg.backwardPairs)
                                / static_cast<double>(solidSolidVirtualDen);
        const double bothForwardBackwardRatio = solidSolidVirtualDen == 0
                                              ? 0.0
                                              : static_cast<double>(agg.bothForwardBackwardPairs)
                                              / static_cast<double>(solidSolidVirtualDen);

        SVFUtil::outs()
            << "vdg.passprofile.step1.summary\tgraphs:" << agg.graphs
            << " nodeMapObjects:" << agg.nodeMapObjects
            << " nodeMapEntries:" << agg.nodeMapEntries
            << " solidEdges:" << agg.solidEdges
            << " virtualEdges:" << agg.virtualEdges
            << "\n";

        SVFUtil::outs()
            << "vdg.passprofile.step2.summary\tpairs:" << agg.forwardPairs
            << " ratio:" << step2Ratio
            << " patternKinds:" << agg.forwardPatterns.size()
            << "\n";
        printSortedPatternCounts("vdg.passprofile.step2.pattern", agg.forwardPatterns);

        SVFUtil::outs()
            << "vdg.passprofile.step3.summary\tpairs:" << agg.backwardPairs
            << " ratio:" << step3Ratio
            << " patternKinds:" << agg.backwardPatterns.size()
            << "\n";
        printSortedPatternCounts("vdg.passprofile.step3.pattern", agg.backwardPatterns);

        SVFUtil::outs()
            << "vdg.passprofile.step23.summary\tbothPairs:" << agg.bothForwardBackwardPairs
            << " solidSolidVirtual:" << solidSolidVirtualDen
            << " ratio:" << bothForwardBackwardRatio
            << "\n";

        SVFUtil::outs()
            << "vdg.passprofile.step4.summary\tsccCount:" << agg.sccCount
            << " sccTotalNodes:" << agg.sccTotalNodes
            << " nonTrivialSccCount:" << agg.sccNonTrivialCount
            << " nonTrivialSccNodes:" << agg.sccNonTrivialNodes
            << " sccMaxSize:" << agg.sccMaxSize
            << " patternKinds:" << agg.sccPatternCounts.size()
            << "\n";
        printSortedPatternCounts("vdg.passprofile.step4.pattern", agg.sccPatternCounts, 20);

        const double storeReachRatio = agg.nodeMapEntries == 0
                                     ? 0.0
                                     : static_cast<double>(agg.storeReachableNodes) / static_cast<double>(agg.nodeMapEntries);
        const double loadRevReachRatio = agg.nodeMapEntries == 0
                                       ? 0.0
                                       : static_cast<double>(agg.loadReverseReachableNodes) / static_cast<double>(agg.nodeMapEntries);
        const double bothReachRatio = agg.nodeMapEntries == 0
                                    ? 0.0
                                    : static_cast<double>(agg.bothReachableNodes) / static_cast<double>(agg.nodeMapEntries);
        SVFUtil::outs()
            << "vdg.passprofile.step5.summary\tstoreReachable:" << agg.storeReachableNodes
            << "/" << agg.nodeMapEntries
            << " ratio:" << storeReachRatio
            << " loadReverseReachable:" << agg.loadReverseReachableNodes
            << "/" << agg.nodeMapEntries
            << " ratio:" << loadRevReachRatio
            << " bothReachable:" << agg.bothReachableNodes
            << "/" << agg.nodeMapEntries
            << " ratio:" << bothReachRatio
            << "\n";
    }

    void runSVFGPassProfiling(const VersionedFlowSensitive &pta, const SVFG *svfg)
    {
        if (svfg == nullptr)
            return;

        Map<NodeID, ProfileGraph> objGraphs;
        Map<NodeID, NodeVector> deltaSrcCacheByDst;
        SVFG *mutableSVFG = const_cast<SVFG *>(svfg);
        CallGraph *cg = pta.getCallGraph();

        auto nonStrongUpdateObj = [&pta](const NodeID o) -> bool
        {
            const BaseObjVar *base = pta.getPAG()->getBaseObject(o);
            if (base == nullptr)
                return true;
            return pta.isHeapMemObj(o) || pta.isArrayMemObj(o)
                || base->isFieldInsensitive()
                || pta.isLocalVarInRecursiveFun(o);
        };

        // Rebuild delta/delta-source marks locally for profiling (same criteria as buildDeltaMaps).
        std::vector<bool> deltaMap(svfg->getTotalNodeNum(), false);
        std::vector<bool> deltaSourceMap(svfg->getTotalNodeNum(), false);
        Set<const CallICFGNode *> deltaCBNs;
        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const NodeID l = it->first;
            if (l >= deltaMap.size())
                continue;

            const SVFGNode *s = it->second;
            bool isDelta = false;
            if (const FunObjVar *fn = svfg->isFunEntrySVFGNode(s))
            {
                if (cg != nullptr)
                {
                    CallGraphEdge::CallInstSet callsites;
                    cg->getIndCallSitesInvokingCallee(fn, callsites);
                    isDelta = !callsites.empty();
                    if (isDelta)
                    {
                        for (const CallICFGNode *cbn : callsites)
                            deltaCBNs.insert(cbn);
                    }
                }
            }
            else if (const CallICFGNode *cbn = svfg->isCallSiteRetSVFGNode(s))
            {
                isDelta = cbn->isIndirectCall();
                if (isDelta)
                    deltaCBNs.insert(cbn);
            }
            deltaMap[l] = isDelta;
        }
        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const NodeID l = it->first;
            if (l >= deltaSourceMap.size())
                continue;

            const SVFGNode *s = it->second;
            if (const CallICFGNode *cbn = SVFUtil::dyn_cast<CallICFGNode>(s->getICFGNode()))
            {
                if (deltaCBNs.find(cbn) != deltaCBNs.end())
                    deltaSourceMap[l] = true;
            }
            if (SVFUtil::isa<FormalOUTSVFGNode>(s))
                deltaSourceMap[l] = true;
        }

        // Build delta-source -> delta-destination reverse cache (same ind-call resolution logic as buildVDG).
        Map<NodeID, NodeVector> deltaDstCache;
        auto getDeltaDstsForSrc = [&deltaMap, cg, svfg, mutableSVFG, &deltaDstCache](NodeID srcId) -> const NodeVector&
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
                        if (cg != nullptr && cg->hasCallGraphEdge(cs))
                        {
                            for (CallGraph::CallGraphEdgeSet::const_iterator it = cg->getCallEdgeBegin(cs),
                                 eit = cg->getCallEdgeEnd(cs); it != eit; ++it)
                            {
                                const FunObjVar *callee = (*it)->getDstNode()->getFunction();
                                if (!svfg->hasFormalINSVFGNodes(callee))
                                    continue;
                                const SVFG::FormalINSVFGNodeSet &formalIns
                                    = mutableSVFG->getFormalINSVFGNodes(callee);
                                for (const NodeID dstId : formalIns)
                                {
                                    if (dstId < deltaMap.size() && deltaMap[dstId])
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
                    if (fun != nullptr && cg != nullptr)
                    {
                        CallGraphEdge::CallInstSet callsites;
                        cg->getIndCallSitesInvokingCallee(fun, callsites);
                        for (const CallICFGNode *cs : callsites)
                        {
                            if (!svfg->hasActualOUTSVFGNodes(cs))
                                continue;
                            const SVFG::ActualOUTSVFGNodeSet &actualOuts
                                = mutableSVFG->getActualOUTSVFGNodes(cs);
                            for (const NodeID dstId : actualOuts)
                            {
                                if (dstId < deltaMap.size() && deltaMap[dstId])
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

        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const NodeID srcId = it->first;
            if (srcId >= deltaSourceMap.size() || !deltaSourceMap[srcId])
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

        // Build profiling graph directly from SVFG indirect edges.
        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const SVFGNode *srcNode = it->second;
            const NodeID srcStmt = srcNode->getId();
            const ProfileNodeRole srcRole = pta.isStore(srcStmt)
                                          ? ProfileNodeRole::StoreYield
                                          : ProfileNodeRole::Normal;
            const ProfileKey srcKey = makeProfileKey(srcStmt, srcRole);

            for (const SVFGEdge *edge : srcNode->getOutEdges())
            {
                const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge);
                if (ie == nullptr)
                    continue;

                const SVFGNode *dstNode = ie->getDstNode();
                const NodeID dstStmt = dstNode->getId();
                const ProfileNodeRole dstRole = pta.isStore(dstStmt)
                                              ? ProfileNodeRole::StoreConsume
                                              : ProfileNodeRole::Normal;
                const ProfileKey dstKey = makeProfileKey(dstStmt, dstRole);

                for (NodeID o : ie->getPointsTo())
                {
                    ProfileGraph &g = objGraphs[o];
                    (void)addProfileEdge(g, srcKey, dstKey, false, svfg);
                }
            }
        }

        // Add delta virtual edges expanded through resolved indirect calls.
        for (const Map<NodeID, NodeVector>::value_type &entry : deltaSrcCacheByDst)
        {
            const NodeID dstStmt = entry.first;
            const SVFGNode *dstNode = svfg->getSVFGNode(dstStmt);
            const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dstNode);
            if (dstMR == nullptr)
                continue;

            const ProfileNodeRole dstRole = pta.isStore(dstStmt)
                                          ? ProfileNodeRole::StoreConsume
                                          : ProfileNodeRole::Normal;
            const ProfileKey dstKey = makeProfileKey(dstStmt, dstRole);

            for (NodeID o : dstMR->getPointsTo())
            {
                ProfileGraph &g = objGraphs[o];
                for (const NodeID srcStmt : entry.second)
                {
                    const SVFGNode *srcNode = svfg->getSVFGNode(srcStmt);
                    const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
                    if (srcMR == nullptr || !srcMR->getPointsTo().test(o))
                        continue;

                    const ProfileNodeRole srcRole = pta.isStore(srcStmt)
                                                  ? ProfileNodeRole::StoreYield
                                                  : ProfileNodeRole::Normal;
                    const ProfileKey srcKey = makeProfileKey(srcStmt, srcRole);
                    (void)addProfileEdge(g, srcKey, dstKey, true, svfg);
                }
            }
        }

        // Add store C->Y edges with existing virtual/solid logic.
        const bool useFSLowerBound = Options::VFSObjFSLowerBound();
        for (Map<NodeID, ProfileGraph>::value_type &entry : objGraphs)
        {
            const NodeID o = entry.first;
            ProfileGraph &g = entry.second;
            Set<NodeID> storeStmtIds;
            for (const auto &kn : g.nodes)
            {
                const NodeID stmtId = getStmtIdFromProfileKey(kn.first);
                if (pta.isStore(stmtId))
                    storeStmtIds.insert(stmtId);
            }

            const bool keepVirtualStoreCY = !useFSLowerBound || !nonStrongUpdateObj(o);
            for (const NodeID storeStmt : storeStmtIds)
            {
                const ProfileKey cKey = makeProfileKey(storeStmt, ProfileNodeRole::StoreConsume);
                const ProfileKey yKey = makeProfileKey(storeStmt, ProfileNodeRole::StoreYield);
                (void)addProfileEdge(g, cKey, yKey, keepVirtualStoreCY, svfg);
            }
        }

        VDGPassProfileAggregate agg;
        for (const Map<NodeID, ProfileGraph>::value_type &entry : objGraphs)
            profileVDGObjectForPassPatterns(entry.second, agg);
        dumpVDGPassProfile(agg);
    }
}
