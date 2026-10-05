//===- VDGBuilder.cpp -- VDG build/simplify pipeline for LOPA ---//

#include "Util/GeneralType.h"
#include "WPA/Andersen.h"
#include "WPA/LOPA.h"
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
                SVFUtil::errs() << "LOPA: unknown VDG pass key '" << raw
                                << "' in -vdg-pass-order=" << order << "\n";
        }

        if (!passes.empty())
            return;

        // Explicit "none" disables the pass pipeline (no fallback).
        std::string lowered;
        lowered.reserve(order.size());
        for (char raw : order)
        {
            const unsigned char c = static_cast<unsigned char>(raw);
            if (!std::isspace(c))
                lowered.push_back(static_cast<char>(std::tolower(c)));
        }
        if (lowered == "none")
            return;

        const std::string fallback = "SPC";
        for (char key : fallback)
            (void)registerVDGSimplifyPassByKey(passes, key);
        SVFUtil::errs() << "LOPA: empty VDG pass pipeline, fallback to -vdg-pass-order="
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
            return v != LOPA::invalidVersion && static_cast<size_t>(v) < parent.size();
        }

        Version find(const Version v)
        {
            if (!valid(v))
                return LOPA::invalidVersion;

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
            if (rl == LOPA::invalidVersion
                || rr == LOPA::invalidVersion
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

//===----------------------------------------------------------------------===//
// VDGBuildContext - per-build state for the object-major VDG pipeline.
//
// Owns the scratch buffers reused across objects (dense version maps,
// discovered marks) and the per-object artifacts collected by the four steps:
//   step1 labelObjectVersions, step2 compressEquivVersions,
//   step3 materializeAndSimplify, step4 shrinkAndPublish.
//===----------------------------------------------------------------------===//
struct LOPA::VDGBuildContext
{
    struct HotProfile
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
    };

    LOPA &pta;
    const bool enableProfile;
    const size_t totalSVFGNodes;

    // Shared scratch, reused across objects.
    std::vector<bool> discovered;
    NodeVector touchedDiscovered;
    std::vector<Version> consumeVersionByLoc;
    std::vector<Version> yieldVersionByLoc;
    NodeVector touchedConsumeLocs;
    NodeVector touchedYieldLocs;
    Map<NodeID, NodeVector> deltaSrcCacheByDst;

    // Profiling accumulators.
    HotProfile profile;
    std::vector<u64_t> passRuns;
    std::vector<u64_t> passVDGNodeTotal;
    std::vector<u64_t> passVDGNodeMax;
    std::vector<double> passTicks;

    // Per-object artifacts.
    NodeID obj = 0;
    VDG *graph = nullptr;
    std::vector<std::pair<Version, NodeID>> osStmtReliance; // load stmts bound to a version
    std::vector<std::pair<Version, Version>> edges;         // solid cflow dependency edges
    std::vector<std::pair<Version, Version>> vedges;        // virtual dependency edges
    std::vector<std::pair<Version, Version>> equiv;         // equivalent versions
    Version nextVersion = LOPA::invalidVersion;
    Version nextVersionBeforeDense = LOPA::invalidVersion;
    Version nextDenseVersion = LOPA::invalidVersion;

    VDGBuildContext(LOPA &pta_, bool enableProfile_)
        : pta(pta_),
          enableProfile(enableProfile_),
          totalSVFGNodes(pta_.svfg->getTotalNodeNum()),
          discovered(totalSVFGNodes, false),
          consumeVersionByLoc(totalSVFGNodes, LOPA::invalidVersion),
          yieldVersionByLoc(totalSVFGNodes, LOPA::invalidVersion)
    {
        touchedDiscovered.reserve(totalSVFGNodes / 6 + 1);
        touchedConsumeLocs.reserve(totalSVFGNodes / 6 + 1);
        touchedYieldLocs.reserve(totalSVFGNodes / 12 + 1);
    }

    /// Build the object-independent reverse delta index once per build.
    void prepareDeltaIndex();
    /// Run the four-step pipeline for a single object.
    void buildObject(NodeID o, const NodeVector &starts, const std::vector<VDGSimplifyPass> &passes);
    /// Emit -vdg-stat hot/compress/pass summaries.
    void printSummary() const;

private:
    void resetScratch();
    bool markDiscovered(NodeID n);
    Version getOrCreateConsumeVersion(NodeID stmtId);
    Version getOrCreateStoreYieldVersion(NodeID storeId);
    void labelObjectVersions(const NodeVector &starts);
    void compressEquivVersions();
    void materializeAndSimplify(const std::vector<VDGSimplifyPass> &passes);
    void shrinkAndPublish();
};

void LOPA::VDGBuildContext::prepareDeltaIndex()
{
    // Cache possible delta destinations per delta-source statement (srcId).
    // This is object-independent and should be built once per srcId.
    Map<NodeID, NodeVector> deltaDstCache;
    auto getDeltaDstsForSrc = [this, &deltaDstCache](NodeID srcId) -> const NodeVector&
    {
        const auto cached = deltaDstCache.find(srcId);
        if (cached != deltaDstCache.end())
            return cached->second;

        NodeVector dsts;
        const SVFGNode *srcNode = pta.svfg->getSVFGNode(srcId);
        if (srcNode != nullptr)
        {
            if (const ActualINSVFGNode *actualIn = SVFUtil::dyn_cast<ActualINSVFGNode>(srcNode))
            {
                const CallICFGNode *cs = actualIn->getCallSite();
                if (cs && cs->isIndirectCall())
                {
                    CallGraph *cg = pta.ander->getCallGraph();
                    if (cg->hasCallGraphEdge(cs))
                    {
                        for (CallGraph::CallGraphEdgeSet::const_iterator it = cg->getCallEdgeBegin(cs),
                             eit = cg->getCallEdgeEnd(cs); it != eit; ++it)
                        {
                            const FunObjVar *callee = (*it)->getDstNode()->getFunction();
                            if (!pta.svfg->hasFormalINSVFGNodes(callee)) continue;
                            const SVFG::FormalINSVFGNodeSet &formalIns = pta.svfg->getFormalINSVFGNodes(callee);
                            for (const NodeID dstId : formalIns)
                            {
                                if (!pta.delta(dstId))
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
                    pta.ander->getCallGraph()->getIndCallSitesInvokingCallee(fun, callsites);
                    for (const CallICFGNode *cs : callsites)
                    {
                        if (!pta.svfg->hasActualOUTSVFGNodes(cs)) continue;
                        const SVFG::ActualOUTSVFGNodeSet &actualOuts = pta.svfg->getActualOUTSVFGNodes(cs);
                        for (const NodeID dstId : actualOuts)
                        {
                            if (!pta.delta(dstId))
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

    for (SVFG::const_iterator it = pta.svfg->begin(), eit = pta.svfg->end(); it != eit; ++it)
    {
        const NodeID srcId = it->first;
        if (!pta.deltaSource(srcId))
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
}

void LOPA::VDGBuildContext::resetScratch()
{
    for (const NodeID n : touchedDiscovered)
        discovered[n] = false;
    touchedDiscovered.clear();

    for (const NodeID stmtId : touchedConsumeLocs)
        consumeVersionByLoc[stmtId] = LOPA::invalidVersion;
    touchedConsumeLocs.clear();

    for (const NodeID stmtId : touchedYieldLocs)
        yieldVersionByLoc[stmtId] = LOPA::invalidVersion;
    touchedYieldLocs.clear();

    osStmtReliance.clear();
    edges.clear();
    vedges.clear();
    equiv.clear();
    nextVersion = LOPA::invalidVersion;
    nextVersionBeforeDense = LOPA::invalidVersion;
    nextDenseVersion = LOPA::invalidVersion;
}

bool LOPA::VDGBuildContext::markDiscovered(const NodeID n)
{
    if (n >= discovered.size() || discovered[n])
        return false;
    discovered[n] = true;
    touchedDiscovered.push_back(n);
    return true;
}

Version LOPA::VDGBuildContext::getOrCreateConsumeVersion(const NodeID stmtId)
{
    assert(static_cast<size_t>(stmtId) < consumeVersionByLoc.size() && "stmtId out of dense consume map range");
    Version &slot = consumeVersionByLoc[stmtId];
    if (slot != LOPA::invalidVersion)
        return slot;

    slot = ++nextVersion;
    touchedConsumeLocs.push_back(stmtId);
    if (pta.isLoad(stmtId))
        osStmtReliance.emplace_back(slot, stmtId);
    return slot;
}

Version LOPA::VDGBuildContext::getOrCreateStoreYieldVersion(const NodeID storeId)
{
    assert(static_cast<size_t>(storeId) < yieldVersionByLoc.size() && "storeId out of dense yield map range");
    Version &slot = yieldVersionByLoc[storeId];
    if (slot != LOPA::invalidVersion)
        return slot;

    slot = ++nextVersion;
    touchedYieldLocs.push_back(storeId);
    return slot;
}

void LOPA::VDGBuildContext::labelObjectVersions(const NodeVector &osStartingNodes)
{
    // --- step 1: traverse object footprint and collect versions/edges only ---
    const double step1StartTicks = enableProfile ? pta.stat->getClk(true) : 0.0;
    std::queue<const SVFGNode *> waveQueue;

    // 预处理起始节点（-lopa-no-offline 时可为任意间接边端点，否则为 Load）
    for (const NodeID startId : osStartingNodes)
    {
        const SVFGNode *startNode = pta.svfg->getSVFGNode(startId);
        if (startNode == nullptr)
            continue;
        if (!Options::LOPANoOffline())
            assert(SVFUtil::isa<LoadSVFGNode>(startNode) && "starting nodes should be loads");
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
        const bool dstIsDelta = pta.delta(dstId);

        unsigned inedge = 0;
        Version singlePredV = LOPA::invalidVersion;
        for (const SVFGEdge *edge : dst->getInEdges())
        {
            const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge);
            if (!ie)
                continue;
            if (!ie->getPointsTo().test(obj))
                continue;
            inedge++;

            const SVFGNode *src = ie->getSrcNode();
            const NodeID srcId = src->getId();
            const Version srcConsumeV = getOrCreateConsumeVersion(srcId);
            const Version srcV = pta.isStore(srcId) ? getOrCreateStoreYieldVersion(srcId) : srcConsumeV;
            if (dstIsDelta)
            {
                edges.emplace_back(srcV, dstConsumeV);
            }
            else if (inedge == 1)
            {
                // For non-delta dst, defer emitting the first edge until we know
                // whether this is truly single-predecessor (only Equiv needed).
                singlePredV = srcV;
                assert(singlePredV != LOPA::invalidVersion && "single pred version should be valid");
            }
            else
            {
                // The second predecessor confirms this dst is not single-pred:
                // flush deferred first edge, then append current edge.
                if (inedge == 2)
                {
                    assert(singlePredV != LOPA::invalidVersion && "deferred first pred should be valid");
                    edges.emplace_back(singlePredV, dstConsumeV);
                }
                edges.emplace_back(srcV, dstConsumeV);
            }

            if (markDiscovered(srcId))
                waveQueue.push(src);
        }

        // 后向收缩 (delta 有虚入边所以不做收缩)
        if (!dstIsDelta)
        {
            if (inedge == 1)
            {
                equiv.emplace_back(dstConsumeV, singlePredV);
            }
            continue;
        }

        const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dst);
        if (!dstMR || !dstMR->getPointsTo().test(obj))
            continue;

        const Map<NodeID, NodeVector>::const_iterator deltaSrcIt = deltaSrcCacheByDst.find(dstId);
        if (deltaSrcIt == deltaSrcCacheByDst.end())
            continue;

        for (const NodeID srcId : deltaSrcIt->second)
        {
            const SVFGNode *srcNode = pta.svfg->getSVFGNode(srcId);
            const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
            if (!srcMR || !srcMR->getPointsTo().test(obj))
                continue;

            const Version srcConsumeV = getOrCreateConsumeVersion(srcId);
            const Version srcV = pta.isStore(srcId) ? getOrCreateStoreYieldVersion(srcId) : srcConsumeV;
            vedges.emplace_back(srcV, dstConsumeV);

            if (srcNode != nullptr && markDiscovered(srcId))
                waveQueue.push(srcNode);
        }
    }
    if (enableProfile)
        profile.step1Ticks += pta.stat->getClk(true) - step1StartTicks;
}

void LOPA::VDGBuildContext::compressEquivVersions()
{
    nextVersionBeforeDense = nextVersion;

    // step 2: 基于 DSU 合并等价版本 (单前驱非 delta 版本)，并重映射版本号到连续空间
    const double step2StartTicks = enableProfile ? pta.stat->getClk(true) : 0.0;

    if (Options::LOPANoOffline() || Options::LOPANoDSU())
    {
        // Uncompressed construction: keep every version distinct and materialize
        // the deferred single-predecessor dependences as solid edges. This yields
        // a VDG without offline equivalence merging, for ablation.
        // -lopa-no-offline additionally disables the simplify pass pipeline;
        // -lopa-no-dsu keeps the passes so the pipeline runs on the raw graph.
        for (const std::pair<Version, Version> &eq : equiv)
        {
            if (eq.first == LOPA::invalidVersion || eq.second == LOPA::invalidVersion
                || eq.first == eq.second)
                continue;
            edges.emplace_back(eq.second, eq.first); // singlePredV -> dstConsumeV
        }
        nextDenseVersion = nextVersion;
        if (enableProfile)
            profile.step2Ticks += pta.stat->getClk(true) - step2StartTicks;
        return;
    }

    VersionDSU equivDsu;
    equivDsu.reset(nextVersion);
    for (const std::pair<Version, Version> &eq : equiv)
        (void)equivDsu.unite(eq.first, eq.second);

    // Build root -> dense-version map (1..N) after DSU is frozen.
    // Versions are already dense in [1..nextVersion], so vector remap is
    // cheaper than per-lookup hash maps in this hot path.
    std::vector<Version> rootToDense(static_cast<size_t>(nextVersion) + 1, LOPA::invalidVersion);
    std::vector<Version> versionToDense(static_cast<size_t>(nextVersion) + 1, LOPA::invalidVersion);
    Version nextDense = LOPA::invalidVersion;
    for (Version v = LOPA::invalidVersion + 1; v <= nextVersion; ++v)
    {
        const Version root = equivDsu.find(v);
        if (root == LOPA::invalidVersion)
            continue;

        Version &denseSlot = rootToDense[root];
        if (denseSlot == LOPA::invalidVersion)
        {
            denseSlot = ++nextDense;
        }
        versionToDense[v] = denseSlot;
    }

    auto toDenseVersion = [&versionToDense](const Version oldV) -> Version
    {
        if (oldV == LOPA::invalidVersion)
            return LOPA::invalidVersion;
        const size_t idx = static_cast<size_t>(oldV);
        if (idx >= versionToDense.size())
            return LOPA::invalidVersion;
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
    for (const std::pair<Version, Version> &edge : edges)
    {
        const Version src = toDenseVersion(edge.first);
        const Version dst = toDenseVersion(edge.second);
        if (src == LOPA::invalidVersion || dst == LOPA::invalidVersion || src == dst)
            continue;
        edges[edgeWrite++] = std::make_pair(src, dst);
    }
    edges.resize(edgeWrite);

    size_t vedgeWrite = 0;
    for (const std::pair<Version, Version> &edge : vedges)
    {
        const Version src = toDenseVersion(edge.first);
        const Version dst = toDenseVersion(edge.second);
        if (src == LOPA::invalidVersion || dst == LOPA::invalidVersion || src == dst)
            continue;
        vedges[vedgeWrite++] = std::make_pair(src, dst);
    }
    vedges.resize(vedgeWrite);

    nextVersion = nextDense;
    nextDenseVersion = nextDense;
    if (enableProfile)
        profile.step2Ticks += pta.stat->getClk(true) - step2StartTicks;
}

void LOPA::VDGBuildContext::materializeAndSimplify(const std::vector<VDGSimplifyPass> &passes)
{
    // --- step 3: materialize dense nodes/edges, then run simplify passes ---
    const double step3StartTicks = enableProfile ? pta.stat->getClk(true) : 0.0;
    if (nextVersion != LOPA::invalidVersion)
        graph->ensureVersionCapacity(nextVersion);

    // label node
    for (const NodeID stmtId : touchedConsumeLocs)
    {
        const Version consumeV = consumeVersionByLoc[stmtId];
        if (consumeV == LOPA::invalidVersion)
            continue;
        graph->getOrAddNode(consumeV, pta.isLoad(stmtId), false);
    }
    for (const NodeID stmtId : touchedYieldLocs)
    {
        const Version yieldV = yieldVersionByLoc[stmtId];
        if (yieldV == LOPA::invalidVersion)
            continue;
        graph->getOrAddNode(yieldV, false, true);
    }
    // add edges
    for (const std::pair<Version, Version> &edge : edges)
    {
        graph->addEdge(edge.first, edge.second, false);
    }
    for (const std::pair<Version, Version> &edge : vedges)
    {
        graph->addEdge(edge.first, edge.second, true);
    }
    // add store consume->yield virtual edges
    for (const NodeID storeId : touchedYieldLocs)
    {
        const Version yieldV = yieldVersionByLoc[storeId];
        const Version consumeV = consumeVersionByLoc[storeId];
        if (consumeV != LOPA::invalidVersion && yieldV != LOPA::invalidVersion && consumeV != yieldV)
        {
            const bool keepVirtualStoreCY
                = !Options::LOPAObjFSLowerBound()
                || pta.fiObjects.find(obj) == pta.fiObjects.end();
            (void)graph->addEdge(consumeV, yieldV, keepVirtualStoreCY);
        }
    }

    for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
    {
        const double passStartTicks = enableProfile ? pta.stat->getClk(true) : 0.0;
        passes[passIdx](*graph);
        if (enableProfile)
        {
            passTicks[passIdx] += pta.stat->getClk(true) - passStartTicks;
            const u64_t nodesAfterPass = static_cast<u64_t>(graph->getTotalNodeNum());
            ++passRuns[passIdx];
            passVDGNodeTotal[passIdx] += nodesAfterPass;
            if (nodesAfterPass > passVDGNodeMax[passIdx])
                passVDGNodeMax[passIdx] = nodesAfterPass;
        }
    }
    if (enableProfile)
        profile.step3Ticks += pta.stat->getClk(true) - step3StartTicks;
}

void LOPA::VDGBuildContext::shrinkAndPublish()
{
    // --- step 4: shrink/publish inside object pipeline, then map labels ---
    const double step4StartTicks = enableProfile ? pta.stat->getClk(true) : 0.0;
    VDG *oldGraph = graph;
    NodeVector oldReps;
    oldReps.reserve(oldGraph->getTotalNodeNum());
    oldGraph->forEachSuperNode([&oldReps](Version oldV, VDGNode *)
    {
        oldReps.push_back(oldV);
    });

    const size_t oldCap = oldGraph->capacity();
    std::vector<Version> oldToNew(oldCap, LOPA::invalidVersion);
    Version nextNewV = LOPA::invalidVersion;
    for (const Version oldV : oldReps)
        oldToNew[oldV] = ++nextNewV;

    auto mapToShrunkRep = [oldGraph, &oldToNew](Version oldV) -> Version
    {
        if (oldV == LOPA::invalidVersion || !oldGraph->hasVersion(oldV))
            return LOPA::invalidVersion;
        const Version oldRepV = oldGraph->getRepVersion(oldV);
        if (oldRepV == LOPA::invalidVersion || !oldGraph->hasVersion(oldRepV))
            return LOPA::invalidVersion;
        if (static_cast<size_t>(oldRepV) >= oldToNew.size())
            return LOPA::invalidVersion;
        return oldToNew[oldRepV];
    };

    std::vector<std::pair<NodeID, Version>> remappedConsumes;
    remappedConsumes.reserve(touchedConsumeLocs.size());
    for (const NodeID stmtId : touchedConsumeLocs)
    {
        const Version newV = mapToShrunkRep(consumeVersionByLoc[stmtId]);
        if (newV != LOPA::invalidVersion)
            remappedConsumes.emplace_back(stmtId, newV);
    }

    std::vector<std::pair<NodeID, Version>> remappedYields;
    remappedYields.reserve(touchedYieldLocs.size());
    for (const NodeID stmtId : touchedYieldLocs)
    {
        const Version newV = mapToShrunkRep(yieldVersionByLoc[stmtId]);
        if (newV != LOPA::invalidVersion)
            remappedYields.emplace_back(stmtId, newV);
    }

    std::vector<std::pair<Version, NodeID>> remappedStmtReliance;
    remappedStmtReliance.reserve(osStmtReliance.size());
    for (const std::pair<Version, NodeID> &vs : osStmtReliance)
    {
        const Version newV = mapToShrunkRep(vs.first);
        if (newV != LOPA::invalidVersion)
            remappedStmtReliance.emplace_back(newV, vs.second);
    }

    std::unique_ptr<VDG> newGraph = std::make_unique<VDG>(obj);
    if (nextNewV != LOPA::invalidVersion)
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
            if (newDst != LOPA::invalidVersion)
            {
                (void)newGraph->addEdge(newSrc, newDst, false);
            }
        }

        for (const Version oldDst : oldNode->getVirtualOut())
        {
            if (static_cast<size_t>(oldDst) >= oldToNew.size())
                continue;
            const Version newDst = oldToNew[oldDst];
            if (newDst != LOPA::invalidVersion)
            {
                (void)newGraph->addEdge(newSrc, newDst, true);
            }
        }
    }

    // Publish shrunk graph for this object.
    VDGManager::VDGMapTy &allVDGs = pta.vdgManager.getAllVDGs();
    VDGManager::VDGMapTy::iterator vdgIt = allVDGs.find(obj);
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
        if (consumeV == LOPA::invalidVersion || yieldV == LOPA::invalidVersion)
            continue;

        const bool consumeYieldConsistent = (consumeV == yieldV);
        if (consumeYieldConsistent)
            continue;

        pta.pendingStoreObjsByLoc[storeId].push_back(obj);
    }

    // Map consume/yield/reliance after shrink.
    for (const std::pair<NodeID, Version> &lv : remappedConsumes)
        pta.setConsume(lv.first, obj, lv.second);

    for (const std::pair<NodeID, Version> &lv : remappedYields)
        pta.setYield(lv.first, obj, lv.second);

    for (const std::pair<Version, NodeID> &vs : remappedStmtReliance)
        graph->bindStmtRelianceStmt(vs.first, vs.second);

    if (enableProfile)
        profile.step4Ticks += pta.stat->getClk(true) - step4StartTicks;
}

void LOPA::VDGBuildContext::buildObject(NodeID o, const NodeVector &starts,
                                        const std::vector<VDGSimplifyPass> &passes)
{
    if (enableProfile)
        ++profile.objects;

    resetScratch();
    obj = o;
    graph = pta.vdgManager.getOrCreateVDG(o);

    labelObjectVersions(starts);
    compressEquivVersions();
    materializeAndSimplify(passes);
    shrinkAndPublish();
}

void LOPA::VDGBuildContext::printSummary() const
{
    if (!enableProfile)
        return;

    SVFUtil::outs()
        << "buildVDG.hot.summary\tobjects:" << profile.objects
        << " totalTime:" << pta.vdgBuildTime
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

    for (size_t passIdx = 0; passIdx < passRuns.size(); ++passIdx)
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

void LOPA::prelabel(void)
{
    // 由 Load 节点出发
    double start = stat->getClk(true);
    objStartingNodes.clear();
    prelabeledObjects.clear();
    fiObjects.clear();
    numPrelabelNodes = 0;
    numPrelabelFIObjs = 0;

    if (Options::LOPANoOffline())
    {
        // Fully-materialized construction: anchor at every indirect-edge
        // destination instead of load anchors, so no load-reachability pruning
        // happens. Every object touched by any indirect edge is materialized.
        for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
        {
            const SVFGNode *srcNode = it->second;
            for (const SVFGEdge *edge : srcNode->getOutEdges())
            {
                const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge);
                if (ie == nullptr)
                    continue;
                const NodeID dstId = ie->getDstNode()->getId();
                for (NodeID o : ie->getPointsTo())
                {
                    prelabeledObjects.insert(o);
                    objStartingNodes[o].push_back(dstId);
                }
            }
        }
        numPrelabelNodes = static_cast<u32_t>(prelabeledObjects.size());
    }
    else
    {
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
    }
    // Pre-estimate non-strong-update objects.
    for (const NodeID o : prelabeledObjects)
    {
        const BaseObjVar *base = pag->getBaseObject(o);
        if (base == nullptr)
            continue;
        if (isHeapMemObj(o) || isArrayMemObj(o)
            || base->isFieldInsensitive()
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

void LOPA::buildVDG(void)
{
    const double labelStart = stat->getClk(true);

    vdgManager.clear();
    pendingStoreObjsByLoc.clear();
    consume.clear();
    yield.clear();

    if (!Options::VDGPassProfile().empty())
    {
        runSVFGPassProfiling(*this, svfg);
        const double totalEndTicks = stat->getClk(true);
        vdgBuildTime = (totalEndTicks - labelStart) / TIMEINTERVAL;
        return;
    }

    std::vector<VDGSimplifyPass> passes;
    if (Options::LOPANoOffline())
    {
        // -lopa-no-offline disables the whole offline compression, including the
        // simplify pass pipeline, so leave `passes` empty (no fallback).
    }
    else
    {
        buildVDGSimplifyPassPipeline(passes, Options::VDGPassOrder());
    }

    VDGBuildContext ctx(*this, Options::VDGStat());
    ctx.prepareDeltaIndex();
    ctx.passRuns.assign(passes.size(), 0);
    ctx.passVDGNodeTotal.assign(passes.size(), 0);
    ctx.passVDGNodeMax.assign(passes.size(), 0);
    ctx.passTicks.assign(passes.size(), 0.0);

    const NodeVector emptyStartingNodes;
    // Iterate objects in ascending NodeID order. step1 tests every reached
    // node's indirect in-edge NodeBS against the current object; a sorted object
    // order lets each bitset's sparse lookup cache advance monotonically instead
    // of thrashing, without changing any per-object result.
    NodeVector objects(prelabeledObjects.begin(), prelabeledObjects.end());
    std::sort(objects.begin(), objects.end());
    for (const NodeID o : objects)
    {
        const Map<NodeID, NodeVector>::const_iterator startsIt = objStartingNodes.find(o);
        const NodeVector &osStartingNodes
            = startsIt == objStartingNodes.end() ? emptyStartingNodes : startsIt->second;
        ctx.buildObject(o, osStartingNodes, passes);
    }
    // Release reverse delta cache after build loop completes.
    Map<NodeID, NodeVector>().swap(ctx.deltaSrcCacheByDst);

    if (Options::VDGStat())
    {
        size_t pendingStores = 0;
        size_t pendingEntries = 0;
        size_t pendingMax = 0;
        for (const auto &kv : pendingStoreObjsByLoc)
        {
            ++pendingStores;
            pendingEntries += kv.second.size();
            pendingMax = std::max(pendingMax, kv.second.size());
        }
        SVFUtil::outs() << "pendingStore.summary\tstores:" << pendingStores
                        << " entries:" << pendingEntries
                        << " maxPerStore:" << pendingMax << "\n";
    }

    const double totalEndTicks = stat->getClk(true);
    vdgBuildTime = (totalEndTicks - labelStart) / TIMEINTERVAL;

    ctx.printSummary();
}
