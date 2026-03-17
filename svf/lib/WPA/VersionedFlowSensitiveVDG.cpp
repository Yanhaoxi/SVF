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

    inline char vdgSimplifyPassKey(VDGSimplifyPass pass)
    {
        if (pass == vdgSimplifySCCMerge) return 'S';
        if (pass == vdgSimplifyReverseReachMerge) return 'A';
        if (pass == vdgSimplifyStableReachability) return 'M';
        if (pass == vdgSimplifyPrune) return 'P';
        if (pass == vdgSimplifyTransRedundancy) return 'T';
        if (pass == vdgSimplifyChainContraction) return 'C';
        return '?';
    }

    inline const char *vdgSimplifyPassName(VDGSimplifyPass pass)
    {
        if (pass == vdgSimplifySCCMerge) return "scc_merge";
        if (pass == vdgSimplifyReverseReachMerge) return "reverse_reach_merge";
        if (pass == vdgSimplifyStableReachability) return "stable_reachability";
        if (pass == vdgSimplifyPrune) return "prune";
        if (pass == vdgSimplifyTransRedundancy) return "transitive_redundancy";
        if (pass == vdgSimplifyChainContraction) return "chain_contraction";
        return "unknown";
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

    struct MeldLabelProfileTotals
    {
        u64_t processedObjects = 0;
        double setupTicks = 0.0;
        double step1Ticks = 0.0;
        double step1SeedTicks = 0.0;
        double step1SCCInitTicks = 0.0;
        double step1SCCVisitTicks = 0.0;
        double step2Ticks = 0.0;
        double step3Ticks = 0.0;
        u64_t step3UniteAttempts = 0;
        u64_t step3UniteEffective = 0;
        u64_t step3AllocatedEquiVersions = 0;
        u64_t step3MaxAllocatedEquiVersions = 0;
        double step4Ticks = 0.0;
        u64_t step4FinalVersions = 0;
        u64_t step4MaxFinalVersions = 0;
        u64_t step4ReducedVersions = 0;
        double step5Ticks = 0.0;
        double step6Ticks = 0.0;
        double step7BuildVDGTicks = 0.0;
        u64_t step7StoreSolidEdges = 0;
        u64_t step7StoreVirtualEdges = 0;
        double step8SimplifyVDGTicks = 0.0;
        double step9BindStmtTicks = 0.0;
        double step9AssignVersionMapTicks = 0.0;
        double step9BindStmtOnlyTicks = 0.0;
    };

    const bool enableMeldProfile = Options::VDGStat();
    MeldLabelProfileTotals profileTotals;
    const double setupStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

    // Nodes requiring explicit consume/yield assignment during solving.
    std::vector<NodeID> nodesWhichNeedVersions;
    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID n = it->first;
        if (delta(n) || deltaSource(n) || isStore(n) || isLoad(n)) nodesWhichNeedVersions.push_back(n);
    }

    vdgManager.clear();
    // Store sites whose consume->yield relation is still deferred because they are
    // currently strong-update singleton stores.
    pendingStoreObjsByLoc.clear();

    std::vector<VDGSimplifyPass> passes;
    buildVDGSimplifyPassPipeline(passes, Options::VDGPassOrder());
    std::vector<double> simplifyPassTicks(passes.size(), 0.0);
    std::vector<u64_t> simplifyPassInvocations(passes.size(), 0);
    std::vector<u64_t> simplifyPassNodeReduceTotal(passes.size(), 0);
    std::vector<u64_t> simplifyPassNodeReduceMax(passes.size(), 0);

    auto addVirtualIndCallEdgeForObj =
        [this](NodeID srcId,
               NodeID dstId,
               NodeID o,
               const LocToVersionMap &consumeMap,
               const LocToVersionMap &yieldMap,
               VDG &graph)
    {
        const SVFGNode *srcNode = svfg->getSVFGNode(srcId);
        const SVFGNode *dstNode = svfg->getSVFGNode(dstId);
        const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
        const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dstNode);
        if (!srcMR || !dstMR) return;
        if (!srcMR->getPointsTo().test(o) || !dstMR->getPointsTo().test(o)) return;

        assert(delta(dstId) && "VFS::updateConnectedNodes: new edges should be to delta nodes!");
        assert(deltaSource(srcId) && "VFS::updateConnectedNodes: new indirect edges should be from delta source nodes!");

        Version srcY = invalidVersion;
        if (isStore(srcId))
        {
            const LocToVersionMap::const_iterator srcYIt = yieldMap.find(srcId);
            if (srcYIt != yieldMap.end())
                srcY = srcYIt->second;
        }
        else
        {
            const LocToVersionMap::const_iterator srcCIt = consumeMap.find(srcId);
            if (srcCIt != consumeMap.end())
                srcY = srcCIt->second;
        }
        if (srcY == invalidVersion) return;
        const LocToVersionMap::const_iterator dstCIt = consumeMap.find(dstId);
        if (dstCIt == consumeMap.end()) return;
        const Version dstC = dstCIt->second;
        if (dstC == invalidVersion) return;
        if (srcY == dstC) return;

        graph.getOrAddNode(srcY, false, false);
        graph.getOrAddNode(dstC, false, false);
        graph.addEdge(srcY, dstC, true);
    };

    // Cache indirect-call structural sources per destination statement (dstId).
    // This is object-independent and should be built once per dstId.
    Map<NodeID, NodeVector> indirectSrcCache;
    auto getIndirectSourcesForDst = [this, &indirectSrcCache](NodeID dstId) -> const NodeVector&
    {
        const auto cached = indirectSrcCache.find(dstId);
        if (cached != indirectSrcCache.end())
            return cached->second;

        NodeVector srcs;
        const SVFGNode *dstNode = svfg->getSVFGNode(dstId);

        if (const FunObjVar *fn = svfg->isFunEntrySVFGNode(dstNode))
        {
            if (svfg->hasFormalINSVFGNodes(fn))
            {
                const SVFG::FormalINSVFGNodeSet &formalIns = svfg->getFormalINSVFGNodes(fn);
                if (formalIns.test(dstId))
                {
                    CallGraphEdge::CallInstSet callsites;
                    ander->getCallGraph()->getIndCallSitesInvokingCallee(fn, callsites);
                    for (const CallICFGNode *cs : callsites)
                    {
                        if (!svfg->hasActualINSVFGNodes(cs)) continue;
                        const SVFG::ActualINSVFGNodeSet &actualIns = svfg->getActualINSVFGNodes(cs);
                        for (const NodeID srcId : actualIns)
                            srcs.push_back(srcId);
                    }
                }
            }
        }
        else if (const CallICFGNode *cs = svfg->isCallSiteRetSVFGNode(dstNode))
        {
            if (cs->isIndirectCall() && svfg->hasActualOUTSVFGNodes(cs))
            {
                const SVFG::ActualOUTSVFGNodeSet &actualOuts = svfg->getActualOUTSVFGNodes(cs);
                if (actualOuts.test(dstId))
                {
                    CallGraph *cg = ander->getCallGraph();
                    if (cg->hasCallGraphEdge(cs))
                    {
                        for (CallGraph::CallGraphEdgeSet::const_iterator it = cg->getCallEdgeBegin(cs),
                             eit = cg->getCallEdgeEnd(cs); it != eit; ++it)
                        {
                            const FunObjVar *callee = (*it)->getDstNode()->getFunction();
                            if (!svfg->hasFormalOUTSVFGNodes(callee)) continue;
                            const SVFG::FormalOUTSVFGNodeSet &formalOuts = svfg->getFormalOUTSVFGNodes(callee);
                            for (const NodeID srcId : formalOuts)
                                srcs.push_back(srcId);
                        }
                    }
                }
            }
        }

        if (!srcs.empty())
        {
            std::sort(srcs.begin(), srcs.end());
            srcs.erase(std::unique(srcs.begin(), srcs.end()), srcs.end());
        }

        const auto inserted = indirectSrcCache.emplace(dstId, std::move(srcs));
        return inserted.first->second;
    };

    if (enableMeldProfile)
        profileTotals.setupTicks = stat->getClk(true) - setupStartTicks;

    std::vector<int> partOf;
    std::vector<const IndirectSVFGEdge *> footprint;
    for (const NodeID o : prelabeledObjects)
    {
        if (enableMeldProfile)
            ++profileTotals.processedObjects;

        // 1. Compute the SCCs for the nodes on the graph overlay of o.
        // For starting nodes, we only need those which did prelabeling for o specifically.
        const double step1StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        const double step1SeedStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        const Map<NodeID, NodeVector>::const_iterator startsIt = objStartingNodes.find(o);
        static const NodeVector emptyStartingNodes;
        const NodeVector &osStartingNodes
            = startsIt == objStartingNodes.end() ? emptyStartingNodes : startsIt->second;
        if (enableMeldProfile)
            profileTotals.step1SeedTicks += stat->getClk(true) - step1SeedStartTicks;

        SCC::DetectProfile sccDetectProfile;
        unsigned numSCCs = SCC::detectSCCs(
            this,
            this->svfg,
            o,
            osStartingNodes,
            partOf,
            footprint,
            enableMeldProfile ? &sccDetectProfile : nullptr);
        if (enableMeldProfile)
        {
            profileTotals.step1Ticks += stat->getClk(true) - step1StartTicks;
            profileTotals.step1SCCInitTicks += sccDetectProfile.initTicks;
            profileTotals.step1SCCVisitTicks += sccDetectProfile.visitTicks;
        }

        // 2. Initialize DSU-based equivalence classes for SCC consume versions,
        // and allocate dedicated yield ids for store nodes.
        const double step2StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        // SCC ids [0, numSCCs) are the initial DSU nodes.
        VersionDSU VersionManager(numSCCs);
        // Stores have distinct yielded versions; keep their EquiVersion ids here.
        Map<NodeID, EquiVersion> storesYieldedEquiVersion;

        // Build object-local reverse overlay from footprint edges.
        // in[n]  = predecessors of n on object o's footprint.
        Map<NodeID, NodeVector> footprintInMap;
        for (const IndirectSVFGEdge *ie : footprint)
        {
            const NodeID src = ie->getSrcNode()->getId();
            const NodeID dst = ie->getDstNode()->getId();
            footprintInMap[dst].push_back(src);
        }
        // Each store node gets a dedicated yield EquiVersion.
        // Under current SCC traversal rules, store nodes are singleton SCCs.
        std::vector<int> storeSCC(numSCCs, -1);
        for (const NodeID node : osStartingNodes)
        {
            if (isStore(node) && storesYieldedEquiVersion.find(node) == storesYieldedEquiVersion.end())
            {
                storesYieldedEquiVersion[node] = VersionManager.addNode();
                const int nSCC = partOf[node];
                storeSCC[nSCC] = node;
            }
        }
        // Current allocated EquiVersion count before any unite() in step3.
        const u64_t allocatedEquiVersions =
            static_cast<u64_t>(numSCCs) + static_cast<u64_t>(storesYieldedEquiVersion.size());
        if (enableMeldProfile)
        {
            profileTotals.step3AllocatedEquiVersions += allocatedEquiVersions;
            if (allocatedEquiVersions > profileTotals.step3MaxAllocatedEquiVersions)
                profileTotals.step3MaxAllocatedEquiVersions = allocatedEquiVersions;
        }

        if (enableMeldProfile)
            profileTotals.step2Ticks += stat->getClk(true) - step2StartTicks;

        // 3. Build SCC reliance and propagate SCC equivalence rules.
        const double step3StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

        // sccReliance[x] = { y_1, y_2, ... } if there exists an edge from a node
        // in SCC x to SCC y_i.
        std::vector<Set<int>> sccReliance(numSCCs);
        for (auto it = footprintInMap.begin(); it != footprintInMap.end(); ++it)
        {
            NodeID n = it->first;
            int nSCC = partOf[n];

            // Given m -> n
            const Map<NodeID, NodeVector>::const_iterator inIt = footprintInMap.find(n);
            if (inIt == footprintInMap.end()) continue;
            for (const NodeID m : inIt->second)
            {
                int mSCC = partOf[m];
                // If predecessor m is a store, merge against its yielded EquiVersion;
                // otherwise merge against m's SCC consume EquiVersion.
                const EquiVersion mEquiVersion
                    = isStore(m) ? storesYieldedEquiVersion[m] : static_cast<EquiVersion>(mSCC);
                const EquiVersion nEquiVersion = static_cast<EquiVersion>(nSCC);

                // There is an edge from the SCC n belongs to that m belongs to.
                sccReliance[mSCC].insert(nSCC);

                // If n has exactly one predecessor on the object footprint,
                // merge predecessor/destination SCC consume versions.
                if (mEquiVersion != nEquiVersion && inIt->second.size() == 1)
                {
                    if (enableMeldProfile)
                        ++profileTotals.step3UniteAttempts;
                    if (VersionManager.unite(mEquiVersion, nEquiVersion) && enableMeldProfile)
                        ++profileTotals.step3UniteEffective;
                }
            }
        }
        if (enableMeldProfile)
            profileTotals.step3Ticks += stat->getClk(true) - step3StartTicks;

        // 4. Compress DSU reps into dense Version ids.
        const double step4StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        Map<EquiVersion, Version> mvv;
        std::vector<Version> sccToVersion(numSCCs, invalidVersion);
        Version curVersion = 0;
        for (u32_t scc = 0; scc < numSCCs; ++scc)
        {
            const EquiVersion &mv = VersionManager.find(scc);
            Map<EquiVersion, Version>::const_iterator foundVersion = mvv.find(mv);
            Version v = foundVersion == mvv.end() ? mvv[mv] = ++curVersion : foundVersion->second;
            sccToVersion[scc] = v;
        }

        // Do the same mapping for store yielded EquiVersion ids.
        // Note: store yielded ids may have been unified in VersionManager,
        // so canonicalize via find() before mapping to final Version.
        Map<NodeID, Version> storesYieldedVersion;
        for (auto const& nmv : storesYieldedEquiVersion)
        {
            const NodeID n = nmv.first;
            const EquiVersion &mv = nmv.second;
            const EquiVersion rep = VersionManager.find(mv);

            Map<EquiVersion, Version>::const_iterator foundVersion = mvv.find(rep);
            Version v = foundVersion == mvv.end() ? mvv[rep] = ++curVersion : foundVersion->second;
            storesYieldedVersion[n] = v;
        }
        // built Node according to SCC-based versions, but without edges yet.
        VDG* graph = vdgManager.getOrCreateVDG(o);
        graph->ensureDenseVersionNodes(curVersion);

        storesYieldedEquiVersion.clear();
        mvv.clear();

        if (enableMeldProfile)
        {
            const u64_t finalVersions = static_cast<u64_t>(curVersion);
            profileTotals.step4FinalVersions += finalVersions;
            if (finalVersions > profileTotals.step4MaxFinalVersions)
                profileTotals.step4MaxFinalVersions = finalVersions;
            if (allocatedEquiVersions > finalVersions)
                profileTotals.step4ReducedVersions += (allocatedEquiVersions - finalVersions);
        }

        if (enableMeldProfile)
            profileTotals.step4Ticks += stat->getClk(true) - step4StartTicks;

        // 5. From SCC reliance, materialize version-reliance edges directly.
        const double step5StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        for (u32_t scc = 0; scc < numSCCs; ++scc)
        {
            if (sccReliance[scc].empty()) continue;

            // Reliance source uses store-yield Version when the predecessor SCC is store-backed;
            // otherwise it uses the SCC consume Version.
            const Version version
                = storeSCC[scc] != -1 ? storesYieldedVersion[storeSCC[scc]] : sccToVersion[scc];

            if (version == invalidVersion)
                continue;

            for (const int reliantSCC : sccReliance[scc])
            {
                const Version reliantVersion = sccToVersion[reliantSCC];
                if (reliantVersion == invalidVersion || version == reliantVersion)
                    continue;
                graph->addEdge(version, reliantVersion, false);
            }
        }
        if (enableMeldProfile)
            profileTotals.step5Ticks += stat->getClk(true) - step5StartTicks;

        // 6. Prepare object-local consume/yield and stmt reliance labels.
        const double step6StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        LocToVersionMap objectConsume;
        LocToVersionMap objectYield;
        Map<Version, NodeBS> osStmtReliance;
        for (const NodeID n : nodesWhichNeedVersions)
        {
            const int scc = partOf[n];
            if (scc == -1) continue;

            const Version c = sccToVersion[scc];
            if (c != invalidVersion)
            {
                objectConsume[n] = c;
                // Version-change reprocessing is load-driven: keep only loads in stmt reliance.
                if (this->isLoad(n))
                    osStmtReliance[c].set(n);
            }

            if (this->isStore(n))
            {
                const Map<NodeID, Version>::const_iterator yIt = storesYieldedVersion.find(n);
                if (yIt != storesYieldedVersion.end())
                    objectYield[n] = yIt->second;
            }
        }
        if (enableMeldProfile)
            profileTotals.step6Ticks += stat->getClk(true) - step6StartTicks;

        // 7. Materialize consume/yield and virtual-indirect edges for this object.
        const bool hasConsume = !objectConsume.empty();
        if (!hasConsume && graph == nullptr)
            continue;

        const double step7BuildVDGStartTicks = stat->getClk(true);
        if (hasConsume)
        {
            VDG &objectGraph = *graph;
            for (const LocToVersionMap::value_type &lv : objectConsume)
            {
                const NodeID l = lv.first;
                const Version c = lv.second;
                if (c == invalidVersion) continue;

                objectGraph.getOrAddNode(c, isLoad(l), false);

                if (isStore(l))
                {
                    const StoreSVFGNode *store = SVFUtil::dyn_cast<StoreSVFGNode>(svfg->getSVFGNode(l));
                    if (store == nullptr)
                        continue;

                    const LocToVersionMap::const_iterator bIt = objectYield.find(l);
                    if (bIt == objectYield.end()) continue;
                    const Version b = bIt->second;
                    if (b == invalidVersion) continue;

                    if (c == b)
                    {
                        objectGraph.getOrAddNode(c, false, true);
                        continue;
                    }

                    // const NodeID q = store->getPAGSrcNodeID();
                    // objectGraph.getOrAddNode(b, false, !ander->getPts(q).empty());
                    objectGraph.getOrAddNode(b, false, true);


                    const PointsTo &dstVPts = getPts(store->getPAGDstNodeID());
                    const size_t dstCount = dstVPts.count();
                    const bool addSolidStoreEdge =
                        dstCount >= 2 || (dstCount == 1 && *dstVPts.begin() != o);

                    if (addSolidStoreEdge)
                    {
                        objectGraph.addEdge(c, b, false);
                        if (enableMeldProfile)
                            ++profileTotals.step7StoreSolidEdges;
                    }
                    else
                    {
                        objectGraph.addEdge(c, b, true);
                        if (enableMeldProfile)
                            ++profileTotals.step7StoreVirtualEdges;
                        pendingStoreObjsByLoc[l].push_back(o);
                    }
                }
                else
                {
                    // Delta virtual edges (formal-in / actual-out) for this object only.
                    const NodeVector &indirectSrcs = getIndirectSourcesForDst(l);
                    for (const NodeID srcId : indirectSrcs)
                        addVirtualIndCallEdgeForObj(srcId, l, o, objectConsume, objectYield, objectGraph);
                }
            }
        }
        const double step7BuildVDGElapsedTicks = stat->getClk(true) - step7BuildVDGStartTicks;
        if (enableMeldProfile)
            profileTotals.step7BuildVDGTicks += step7BuildVDGElapsedTicks;

        // 8. Simplify the VDG with the specified pass pipeline.
        const double step8SimplifyVDGStartTicks = stat->getClk(true);
        assert(graph != nullptr && "VFS::buildVDG: graph should exist when simplify step runs");
        VDG &objectGraph = *graph;
        for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
        {
            VDGSimplifyPass pass = passes[passIdx];
            const u64_t nodesBefore = enableMeldProfile
                ? static_cast<u64_t>(objectGraph.getTotalNodeNum())
                : 0;
            const double passStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            pass(objectGraph);
            if (enableMeldProfile)
            {
                simplifyPassTicks[passIdx] += stat->getClk(true) - passStartTicks;
                ++simplifyPassInvocations[passIdx];

                const u64_t nodesAfter = static_cast<u64_t>(objectGraph.getTotalNodeNum());
                const u64_t reduced = nodesBefore > nodesAfter ? (nodesBefore - nodesAfter) : 0;
                simplifyPassNodeReduceTotal[passIdx] += reduced;
                if (reduced > simplifyPassNodeReduceMax[passIdx])
                    simplifyPassNodeReduceMax[passIdx] = reduced;
            }
        }
        const double step8SimplifyVDGElapsedTicks = stat->getClk(true) - step8SimplifyVDGStartTicks;
        if (enableMeldProfile)
            profileTotals.step8SimplifyVDGTicks += step8SimplifyVDGElapsedTicks;

        // 9. Finalize object labels and bind stmt reliance directly to simplified VDG reps.
        const double step9BindStmtStartTicks = stat->getClk(true);
        const double step9AssignVersionMapStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        for (const LocToVersionMap::value_type &lv : objectConsume)
            setConsume(lv.first, o, lv.second);
        for (const LocToVersionMap::value_type &lv : objectYield)
            setYield(lv.first, o, lv.second);
        if (enableMeldProfile)
            profileTotals.step9AssignVersionMapTicks += stat->getClk(true) - step9AssignVersionMapStartTicks;

        const double step9BindStmtOnlyStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
        if (!osStmtReliance.empty())
        {
            Map<Version, NodeBS> repStmtReliance;
            for (const Map<Version, NodeBS>::value_type &vss : osStmtReliance)
            {
                const Version v = vss.first;
                if (v == invalidVersion) continue;
                // Passes in step8 may delete versions (repVec[v] -> 0).
                // Skip those stale labels just like the old global bind path did.
                if (!graph->hasVersion(v)) continue;
                const Version repV = graph->getRepVersion(v);
                if (repV == invalidVersion || !graph->hasVersion(repV)) continue;
                repStmtReliance[repV] |= vss.second;
            }

            for (const Map<Version, NodeBS>::value_type &repVss : repStmtReliance)
            {
                if (!repVss.second.empty())
                    objectGraph.bindStmtReliance(repVss.first, repVss.second);
            }
        }
        if (enableMeldProfile)
            profileTotals.step9BindStmtOnlyTicks += stat->getClk(true) - step9BindStmtOnlyStartTicks;

        const double step9BindStmtElapsedTicks = stat->getClk(true) - step9BindStmtStartTicks;
        if (enableMeldProfile)
            profileTotals.step9BindStmtTicks += step9BindStmtElapsedTicks;
    }

    const double totalEndTicks = stat->getClk(true);
    const double totalTicks = totalEndTicks - labelStart;
    const double totalSec = totalTicks / TIMEINTERVAL;
    vdgBuildTime = totalSec;

    if (enableMeldProfile)
    {
        const double setupSec = profileTotals.setupTicks / TIMEINTERVAL;
        const double step1Sec = profileTotals.step1Ticks / TIMEINTERVAL;
        const double step1SeedSec = profileTotals.step1SeedTicks / TIMEINTERVAL;
        const double step1SCCInitSec = profileTotals.step1SCCInitTicks / TIMEINTERVAL;
        const double step1SCCVisitSec = profileTotals.step1SCCVisitTicks / TIMEINTERVAL;
        const double step2Sec = profileTotals.step2Ticks / TIMEINTERVAL;
        const double step3Sec = profileTotals.step3Ticks / TIMEINTERVAL;
        const double step4Sec = profileTotals.step4Ticks / TIMEINTERVAL;
        const double step5Sec = profileTotals.step5Ticks / TIMEINTERVAL;
        const double step6Sec = profileTotals.step6Ticks / TIMEINTERVAL;
        const double step7Sec = profileTotals.step7BuildVDGTicks / TIMEINTERVAL;
        const u64_t step7StoreSolidEdges = profileTotals.step7StoreSolidEdges;
        const u64_t step7StoreVirtualEdges = profileTotals.step7StoreVirtualEdges;
        const u64_t step7StoreEdges = step7StoreSolidEdges + step7StoreVirtualEdges;
        const double step8Sec = profileTotals.step8SimplifyVDGTicks / TIMEINTERVAL;
        const double step9Sec = profileTotals.step9BindStmtTicks / TIMEINTERVAL;
        const double step9AssignSec = profileTotals.step9AssignVersionMapTicks / TIMEINTERVAL;
        const double step9BindOnlySec = profileTotals.step9BindStmtOnlyTicks / TIMEINTERVAL;

        const double accumulatedSec =
            setupSec + step1Sec + step2Sec + step3Sec + step4Sec + step5Sec + step6Sec + step7Sec + step8Sec + step9Sec;
        auto pct = [accumulatedSec](double sec) -> double
        {
            return accumulatedSec > 0.0 ? (100.0 * sec / accumulatedSec) : 0.0;
        };
        auto step1Pct = [step1Sec](double sec) -> double
        {
            return step1Sec > 0.0 ? (100.0 * sec / step1Sec) : 0.0;
        };
        auto step9Pct = [step9Sec](double sec) -> double
        {
            return step9Sec > 0.0 ? (100.0 * sec / step9Sec) : 0.0;
        };
        const u64_t processedObjects = profileTotals.processedObjects;
        const double avgAllocatedEquiVersions = processedObjects > 0
            ? static_cast<double>(profileTotals.step3AllocatedEquiVersions) / static_cast<double>(processedObjects)
            : 0.0;
        const double avgFinalVersions = processedObjects > 0
            ? static_cast<double>(profileTotals.step4FinalVersions) / static_cast<double>(processedObjects)
            : 0.0;
        const double reductionRatio = profileTotals.step3AllocatedEquiVersions > 0
            ? 100.0 * static_cast<double>(profileTotals.step4ReducedVersions)
                  / static_cast<double>(profileTotals.step3AllocatedEquiVersions)
            : 0.0;
        const double uniteEffectiveRatio = profileTotals.step3UniteAttempts > 0
            ? 100.0 * static_cast<double>(profileTotals.step3UniteEffective)
                  / static_cast<double>(profileTotals.step3UniteAttempts)
            : 0.0;

        SVFUtil::outs() << "VFS buildVDG(object pipeline) profiling:\n";
        SVFUtil::outs() << "  objects processed: " << processedObjects << "\n";
        SVFUtil::outs() << "  wall total (sec): " << totalSec << "\n";
        SVFUtil::outs() << "  VDGBuildTime total (sec): " << vdgBuildTime << "\n";
        SVFUtil::outs() << "  accumulated step total (sec): " << accumulatedSec << "\n";
        SVFUtil::outs() << "  setup: " << setupSec << " (" << pct(setupSec) << "%)\n";
        SVFUtil::outs() << "  step1_scc: " << step1Sec << " (" << pct(step1Sec) << "%)\n";
        SVFUtil::outs() << "    step1_seed_select: " << step1SeedSec
                        << " (" << step1Pct(step1SeedSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_scc_init: " << step1SCCInitSec
                        << " (" << step1Pct(step1SCCInitSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_scc_visit: " << step1SCCVisitSec
                        << " (" << step1Pct(step1SCCVisitSec) << "% of step1)\n";
        SVFUtil::outs() << "  step2_init: " << step2Sec << " (" << pct(step2Sec) << "%)\n";
        SVFUtil::outs() << "  step3_meld: " << step3Sec << " (" << pct(step3Sec) << "%)\n";
        SVFUtil::outs() << "    step3_unite_attempts/effective: "
                        << profileTotals.step3UniteAttempts << "/"
                        << profileTotals.step3UniteEffective << " ("
                        << uniteEffectiveRatio << "%)\n";
        SVFUtil::outs() << "    step3_allocated_versions_sum/avg/max: "
                        << profileTotals.step3AllocatedEquiVersions << "/"
                        << avgAllocatedEquiVersions << "/"
                        << profileTotals.step3MaxAllocatedEquiVersions << "\n";
        SVFUtil::outs() << "  step4_versionize: " << step4Sec << " (" << pct(step4Sec) << "%)\n";
        SVFUtil::outs() << "    step4_final_versions_sum/avg/max: "
                        << profileTotals.step4FinalVersions << "/"
                        << avgFinalVersions << "/"
                        << profileTotals.step4MaxFinalVersions << "\n";
        SVFUtil::outs() << "    step4_version_reduced_sum/ratio: "
                        << profileTotals.step4ReducedVersions << "/"
                        << reductionRatio << "%\n";
        SVFUtil::outs() << "  step5_reliance: " << step5Sec << " (" << pct(step5Sec) << "%)\n";
        SVFUtil::outs() << "  step6_prepare_labels: " << step6Sec << " (" << pct(step6Sec) << "%)\n";
        SVFUtil::outs() << "  step7_buildvdg: " << step7Sec << " (" << pct(step7Sec) << "%)\n";
        if (step7StoreEdges > 0)
        {
            const double solidRatio = 100.0 * static_cast<double>(step7StoreSolidEdges)
                                      / static_cast<double>(step7StoreEdges);
            SVFUtil::outs() << "    step7_store_solid_ratio: " << solidRatio << "% ("
                            << step7StoreSolidEdges << "/" << step7StoreEdges << ")\n";
        }
        else
        {
            SVFUtil::outs() << "    step7_store_solid_ratio: n/a (0/0)\n";
        }
        SVFUtil::outs() << "  step8_simplifyvdg: " << step8Sec << " (" << pct(step8Sec) << "%)\n";
        if (!passes.empty())
        {
            size_t hottestPassIdx = 0;
            for (size_t i = 1; i < simplifyPassTicks.size(); ++i)
            {
                if (simplifyPassTicks[i] > simplifyPassTicks[hottestPassIdx])
                    hottestPassIdx = i;
            }
            const double hottestPassSec = simplifyPassTicks[hottestPassIdx] / TIMEINTERVAL;
            const VDGSimplifyPass hottestPass = passes[hottestPassIdx];
            const double hottestPassPct = step8Sec > 0.0 ? (100.0 * hottestPassSec / step8Sec) : 0.0;
            SVFUtil::outs() << "    step8_hottest_pass: ["
                            << vdgSimplifyPassKey(hottestPass) << "] "
                            << vdgSimplifyPassName(hottestPass) << " "
                            << hottestPassSec << " (" << hottestPassPct << "% of step8)\n";

            for (size_t passIdx = 0; passIdx < passes.size(); ++passIdx)
            {
                const double passSec = simplifyPassTicks[passIdx] / TIMEINTERVAL;
                const double passPct = step8Sec > 0.0 ? (100.0 * passSec / step8Sec) : 0.0;
                const u64_t passInv = simplifyPassInvocations[passIdx];
                const u64_t passReduceTotal = simplifyPassNodeReduceTotal[passIdx];
                const u64_t passReduceMax = simplifyPassNodeReduceMax[passIdx];
                const double passReduceAvg = passInv > 0
                    ? static_cast<double>(passReduceTotal) / static_cast<double>(passInv)
                    : 0.0;
                SVFUtil::outs() << "    step8_pass[" << passIdx << "] ["
                                << vdgSimplifyPassKey(passes[passIdx]) << "] "
                                << vdgSimplifyPassName(passes[passIdx]) << ": "
                                << passSec << " (" << passPct << "% of step8), "
                                << "node_reduce_sum=" << passReduceTotal << ", "
                                << "node_reduce_avg=" << passReduceAvg << ", "
                                << "node_reduce_max=" << passReduceMax << "\n";
            }
        }
        SVFUtil::outs() << "  step9_bind_stmt_reliance: " << step9Sec << " (" << pct(step9Sec) << "%)\n";
        SVFUtil::outs() << "    step9_assign_versions: " << step9AssignSec
                        << " (" << step9Pct(step9AssignSec) << "% of step9)\n";
        SVFUtil::outs() << "    step9_bind_stmt_only: " << step9BindOnlySec
                        << " (" << step9Pct(step9BindOnlySec) << "% of step9)\n";
    }

}
