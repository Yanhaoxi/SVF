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
#include <mutex>
#include <queue>
#include <thread>

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

            vWorklist.push(l);

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

                // Push into worklist because its consume == its yield.
                vWorklist.push(l);
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

void VersionedFlowSensitive::meldLabel(void)
{
    double start = stat->getClk(true);

    struct MeldLabelProfileTotals
    {
        u64_t processedObjects = 0;
        u64_t dedupSkippedObjects = 0;
        double setupTicks = 0.0;
        double step1Ticks = 0.0;
        double step1SeedTicks = 0.0;
        double step1SCCInitTicks = 0.0;
        double step1SCCVisitTicks = 0.0;
        double step1SCCSortTicks = 0.0;
        double step2Ticks = 0.0;
        double step3Ticks = 0.0;
        double step4Ticks = 0.0;
        double step5Ticks = 0.0;
        double step6Ticks = 0.0;
        double step7Ticks = 0.0;
        double finalizeTicks = 0.0;

        void addFrom(const MeldLabelProfileTotals &other)
        {
            processedObjects += other.processedObjects;
            dedupSkippedObjects += other.dedupSkippedObjects;
            step1Ticks += other.step1Ticks;
            step1SeedTicks += other.step1SeedTicks;
            step1SCCInitTicks += other.step1SCCInitTicks;
            step1SCCVisitTicks += other.step1SCCVisitTicks;
            step1SCCSortTicks += other.step1SCCSortTicks;
            step2Ticks += other.step2Ticks;
            step3Ticks += other.step3Ticks;
            step4Ticks += other.step4Ticks;
            step5Ticks += other.step5Ticks;
            step6Ticks += other.step6Ticks;
            step7Ticks += other.step7Ticks;
        }
    };

    const bool enableMeldProfile = Options::VDGStat();
    MeldLabelProfileTotals profileTotals;
    std::mutex profileMutex;
    const double setupStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

    assert(Options::VersioningThreads() > 0 && "VFS::meldLabel: number of versioning threads must be > 0!");

    // Nodes which have at least one object on them given a prelabel + the Andersen's points-to
    // set of interest so we don't keep calling getPts. For Store nodes, we'll fill that in, for
    // MR nodes, we won't as its getPointsTo is cheap.
    // TODO: preferably we cache both for ease and to avoid the dyn_cast/isa, but Andersen's points-to
    // sets are PointsTo and MR's sets are NodeBS, which are incompatible types. Maybe when we can
    // use std::option.
    std::vector<bool> isPrelabeled(svfg->getTotalNodeNum(), false);
    while (!vWorklist.empty())
    {
        const NodeID n = vWorklist.pop();
        isPrelabeled[n] = true;
    }

    // Delta, delta source, store, and load nodes, which require versions during
    // solving, unlike other nodes with which we can make do with the reliance map.
    std::vector<NodeID> nodesWhichNeedVersions;
    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID n = it->first;
        if (delta(n) || deltaSource(n) || isStore(n) || isLoad(n)) nodesWhichNeedVersions.push_back(n);
    }

    std::mutex *versionMutexes = new std::mutex[nodesWhichNeedVersions.size()];

    // Map of footprints to the canonical object "owning" the footprint.
    Map<std::vector<const IndirectSVFGEdge *>, NodeID> footprintOwner;

    std::queue<NodeID> objectQueue;
    for (const NodeID o : prelabeledObjects)
    {
        // "Touch" maps with o so we don't need to lock on them.
        versionReliance[o];
        stmtReliance[o];
        objectQueue.push(o);
    }

    std::mutex objectQueueMutex;
    std::mutex footprintOwnerMutex;

    if (enableMeldProfile)
        profileTotals.setupTicks = stat->getClk(true) - setupStartTicks;

    auto meldVersionWorker = [this, &footprintOwner, &objectQueue,
                                    &objectQueueMutex, &footprintOwnerMutex, &versionMutexes,
                                    &isPrelabeled, &nodesWhichNeedVersions,
                                    &profileMutex, &profileTotals, enableMeldProfile]
         (const unsigned thread)
    {
        (void)thread;
        MeldLabelProfileTotals localProfile;
        std::vector<int> partOf;
        std::vector<const IndirectSVFGEdge *> footprint;

        while (true)
        {
            NodeID o;
            {
                std::lock_guard<std::mutex> guard(objectQueueMutex);
                // No more objects? Done.
                if (objectQueue.empty()) break;
                o = objectQueue.front();
                objectQueue.pop();
            }

            if (enableMeldProfile)
                ++localProfile.processedObjects;

            // 1. Compute the SCCs for the nodes on the graph overlay of o.
            // For starting nodes, we only need those which did prelabeling for o specifically.
            const double step1StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            const double step1SeedStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            const Map<NodeID, NodeVector>::const_iterator startsIt = objStartingNodes.find(o);
            static const NodeVector emptyStartingNodes;
            const NodeVector &osStartingNodes
                = startsIt == objStartingNodes.end() ? emptyStartingNodes : startsIt->second;
            if (enableMeldProfile)
                localProfile.step1SeedTicks += stat->getClk(true) - step1SeedStartTicks;

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
                localProfile.step1Ticks += stat->getClk(true) - step1StartTicks;
                localProfile.step1SCCInitTicks += sccDetectProfile.initTicks;
                localProfile.step1SCCVisitTicks += sccDetectProfile.visitTicks;
                localProfile.step1SCCSortTicks += sccDetectProfile.sortTicks;
            }

            // 2. Skip any further processing of a footprint we have seen before.
            const double step2StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            bool isCanonicalFootprint = true;
            {
                std::lock_guard<std::mutex> guard(footprintOwnerMutex);
                const Map<std::vector<const IndirectSVFGEdge *>, NodeID>::const_iterator canonOwner
                    = footprintOwner.find(footprint);
                if (canonOwner == footprintOwner.end())
                {
                    this->equivalentObject[o] = o;
                    footprintOwner[footprint] = o;
                }
                else
                {
                    this->equivalentObject[o] = canonOwner->second;
                    this->recordRepeat(o, canonOwner->second);
                    isCanonicalFootprint = false;
                }
            }

            if (enableMeldProfile)
                localProfile.step2Ticks += stat->getClk(true) - step2StartTicks;

            if (!isCanonicalFootprint)
            {
                if (enableMeldProfile)
                    ++localProfile.dedupSkippedObjects;
                // Reliance maps are kept on canonical objects only and queried through
                // equivalentObject mapping at use sites.
                continue;
            }

            // 3. a. Initialise the MeldVersion of prelabeled nodes (SCCs).
            //    b. Initialise a todo list of all the nodes we need to version,
            //       sorted according to topological order.
            const double step3StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            // We will use a map of sccs to meld versions for what is consumed.
            std::vector<MeldVersion> sccToMeldVersion(numSCCs);
            // At stores, what is consumed is different to what is yielded, so we
            // maintain that separately.
            Map<NodeID, MeldVersion> storesYieldedMeldVersion;
            // SVFG nodes of interest -- those part of an SCC from the starting nodes.
            std::vector<NodeID> todoList;
            unsigned bit = 0;
            // To calculate reachable nodes, we can see what nodes n exist where
            // partOf[n] != -1. Since the SVFG can be large this can be expensive.
            // Instead, we can gather this from the edges in the footprint and
            // the starting nodes (incase such nodes have no edges).
            // TODO: should be able to do this better: too many redundant inserts.
            Set<NodeID> reachableNodes;
            for (const NodeID startNode : osStartingNodes) reachableNodes.insert(startNode);
            for (const SVFGEdge *se : footprint)
            {
                reachableNodes.insert(se->getSrcNode()->getId());
                reachableNodes.insert(se->getDstNode()->getId());
            }

            for (const NodeID n : reachableNodes)
            {
                if (isPrelabeled[n])
                {
                    if (this->isStore(n)) storesYieldedMeldVersion[n].set(bit);
                    else sccToMeldVersion[partOf[n]].set(bit);
                    ++bit;
                }

                todoList.push_back(n);
            }

            // Sort topologically so each nodes is only visited once.
            auto cmp = [&partOf](const NodeID a, const NodeID b)
            {
                return partOf[a] > partOf[b];
            };
            std::sort(todoList.begin(), todoList.end(), cmp);
            if (enableMeldProfile)
                localProfile.step3Ticks += stat->getClk(true) - step3StartTicks;

            // 4. a. Do meld versioning.
            //    b. Determine SCC reliances.
            //    c. Build a footprint for o (all edges which it is found on).
            //    d. Determine which SCCs belong to stores.
            const double step4StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

            // sccReliance[x] = { y_1, y_2, ... } if there exists an edge from a node
            // in SCC x to SCC y_i.
            std::vector<Set<int>> sccReliance(numSCCs);
            // Maps SCC to the store it corresponds to or -1 if it doesn't. TODO: unsigned vs signed -- nasty.
            std::vector<int> storeSCC(numSCCs, -1);
            for (size_t i = 0; i < todoList.size(); ++i)
            {
                const NodeID n = todoList[i];
                const SVFGNode *sn = this->svfg->getSVFGNode(n);
                const bool nIsStore = this->isStore(n);

                int nSCC = partOf[n];
                if (nIsStore) storeSCC[nSCC] = n;

                // Given n -> m, the yielded version of n will be melded into m.
                // For stores, that is in storesYieldedMeldVersion, otherwise, consume == yield and
                // we can just use sccToMeldVersion.
                const MeldVersion &nMV = nIsStore ? storesYieldedMeldVersion[n] : sccToMeldVersion[nSCC];
                for (const SVFGEdge *e : sn->getOutEdges())
                {
                    const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(e);
                    if (!ie) continue;

                    const NodeID m = ie->getDstNode()->getId();
                    // Ignoreedges which don't involve o.
                    if (!ie->getPointsTo().test(o)) continue;

                    int mSCC = partOf[m];

                    // There is an edge from the SCC n belongs to that m belongs to.
                    sccReliance[nSCC].insert(mSCC);

                    // Ignore edges to delta nodes (prelabeled consume).
                    // No point propagating when n's SCC == m's SCC (same meld version there)
                    // except when it is a store, because we are actually propagating n's yielded
                    // into m's consumed. Store nodes are in their own SCCs, so it is a self
                    // loop on a store node.
                    if (!this->delta(m) && (nSCC != mSCC || nIsStore))
                    {
                        sccToMeldVersion[mSCC] |= nMV;
                    }
                }
            }
            if (enableMeldProfile)
                localProfile.step4Ticks += stat->getClk(true) - step4StartTicks;

            // 5. Transform meld versions belonging to SCCs into versions.
            const double step5StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            Map<MeldVersion, Version> mvv;
            std::vector<Version> sccToVersion(numSCCs, invalidVersion);
            Version curVersion = 0;
            for (u32_t scc = 0; scc < sccToMeldVersion.size(); ++scc)
            {
                const MeldVersion &mv = sccToMeldVersion[scc];
                Map<MeldVersion, Version>::const_iterator foundVersion = mvv.find(mv);
                Version v = foundVersion == mvv.end() ? mvv[mv] = ++curVersion : foundVersion->second;
                sccToVersion[scc] = v;
            }

            sccToMeldVersion.clear();

            // Same for storesYieldedMeldVersion.
            Map<NodeID, Version> storesYieldedVersion;
            Map<NodeID, Version> loadsConsumedVersion;
            for (auto const& nmv : storesYieldedMeldVersion)
            {
                const NodeID n = nmv.first;
                const MeldVersion &mv = nmv.second;

                Map<MeldVersion, Version>::const_iterator foundVersion = mvv.find(mv);
                Version v = foundVersion == mvv.end() ? mvv[mv] = ++curVersion : foundVersion->second;
                storesYieldedVersion[n] = v;
            }

            storesYieldedMeldVersion.clear();

            mvv.clear();
            this->recordVersionForObj(o, curVersion);
            if (enableMeldProfile)
                localProfile.step5Ticks += stat->getClk(true) - step5StartTicks;

            // 6. From SCC reliance, determine version reliances.
            const double step6StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            Map<Version, std::vector<Version>> &osVersionReliance = this->versionReliance.at(o);
            for (u32_t scc = 0; scc < numSCCs; ++scc)
            {
                if (sccReliance[scc].empty()) continue;

                // Some consume relies on a yield. When it's a store, we need to pick whether to
                // use the consume or yield unlike when it is not because they are the same.
                const Version version
                    = storeSCC[scc] != -1 ? storesYieldedVersion[storeSCC[scc]] : sccToVersion[scc];

                std::vector<Version> &reliantVersions = osVersionReliance[version];
                for (const int reliantSCC : sccReliance[scc])
                {
                    const Version reliantVersion = sccToVersion[reliantSCC];
                    if (version != reliantVersion)
                    {
                        // sccReliance is a set, no need to worry about duplicates.
                        reliantVersions.push_back(reliantVersion);
                    }
                }
            }
            if (enableMeldProfile)
                localProfile.step6Ticks += stat->getClk(true) - step6StartTicks;

            // 7. a. Save versions for nodes which need them.
            //    b. Fill in stmtReliance.
            // TODO: maybe randomize iteration order for less contention? Needs profiling.
            const double step7StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            Map<Version, NodeBS> &osStmtReliance = this->stmtReliance.at(o);
            for (size_t i = 0; i < nodesWhichNeedVersions.size(); ++i)
            {
                const NodeID n = nodesWhichNeedVersions[i];
                std::mutex &mutex = versionMutexes[i];

                const int scc = partOf[n];
                if (scc == -1) continue;

                std::lock_guard<std::mutex> guard(mutex);

                const Version c = sccToVersion[scc];
                if (c != invalidVersion)
                {
                    this->setConsume(n, o, c);
                    // Version-change reprocessing is load-driven: keep only loads in stmt reliance.
                    if (this->isLoad(n)) osStmtReliance[c].set(n);
                }

                if (this->isStore(n))
                {
                    const Map<NodeID, Version>::const_iterator yIt = storesYieldedVersion.find(n);
                    if (yIt != storesYieldedVersion.end()) this->setYield(n, o, yIt->second);
                }
            }
            if (enableMeldProfile)
                localProfile.step7Ticks += stat->getClk(true) - step7StartTicks;
        }

        if (enableMeldProfile)
        {
            std::lock_guard<std::mutex> guard(profileMutex);
            profileTotals.addFrom(localProfile);
        }
    };

    std::vector<std::thread> workers;
    for (unsigned i = 0; i < Options::VersioningThreads(); ++i) workers.push_back(std::thread(meldVersionWorker, i));
    for (std::thread &worker : workers) worker.join();

    const double finalizeStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

    // Fill equivalent objects with references to canonical reliance maps.
    versionRelianceRef.clear();
    stmtRelianceRef.clear();
    for (const Map<NodeID, NodeID>::value_type &kv : equivalentObject)
    {
        const NodeID o = kv.first;
        const NodeID canon = kv.second;
        versionRelianceRef[o] = &versionReliance[canon];
        stmtRelianceRef[o] = &stmtReliance[canon];
    }

    if (enableMeldProfile)
        profileTotals.finalizeTicks = stat->getClk(true) - finalizeStartTicks;

    delete[] versionMutexes;

    double end = stat->getClk(true);
    meldLabelingTime = (end - start) / TIMEINTERVAL;

    if (enableMeldProfile)
    {
        const double setupSec = profileTotals.setupTicks / TIMEINTERVAL;
        const double step1Sec = profileTotals.step1Ticks / TIMEINTERVAL;
        const double step1SeedSec = profileTotals.step1SeedTicks / TIMEINTERVAL;
        const double step1SCCInitSec = profileTotals.step1SCCInitTicks / TIMEINTERVAL;
        const double step1SCCVisitSec = profileTotals.step1SCCVisitTicks / TIMEINTERVAL;
        const double step1SCCSortSec = profileTotals.step1SCCSortTicks / TIMEINTERVAL;
        const double step2Sec = profileTotals.step2Ticks / TIMEINTERVAL;
        const double step3Sec = profileTotals.step3Ticks / TIMEINTERVAL;
        const double step4Sec = profileTotals.step4Ticks / TIMEINTERVAL;
        const double step5Sec = profileTotals.step5Ticks / TIMEINTERVAL;
        const double step6Sec = profileTotals.step6Ticks / TIMEINTERVAL;
        const double step7Sec = profileTotals.step7Ticks / TIMEINTERVAL;
        const double finalizeSec = profileTotals.finalizeTicks / TIMEINTERVAL;

        const double accumulatedSec =
            setupSec + step1Sec + step2Sec + step3Sec + step4Sec + step5Sec + step6Sec + step7Sec + finalizeSec;
        auto pct = [accumulatedSec](double sec) -> double
        {
            return accumulatedSec > 0.0 ? (100.0 * sec / accumulatedSec) : 0.0;
        };
        auto step1Pct = [step1Sec](double sec) -> double
        {
            return step1Sec > 0.0 ? (100.0 * sec / step1Sec) : 0.0;
        };

        SVFUtil::outs() << "VFS meldLabel profiling:\n";
        SVFUtil::outs() << "  objects processed: " << profileTotals.processedObjects
                        << ", dedup skipped: " << profileTotals.dedupSkippedObjects << "\n";
        SVFUtil::outs() << "  wall total (sec): " << meldLabelingTime << "\n";
        SVFUtil::outs() << "  accumulated step total (sec): " << accumulatedSec << "\n";
        SVFUtil::outs() << "  setup: " << setupSec << " (" << pct(setupSec) << "%)\n";
        SVFUtil::outs() << "  step1_scc: " << step1Sec << " (" << pct(step1Sec) << "%)\n";
        SVFUtil::outs() << "    step1_seed_select: " << step1SeedSec
                        << " (" << step1Pct(step1SeedSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_scc_init: " << step1SCCInitSec
                        << " (" << step1Pct(step1SCCInitSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_scc_visit: " << step1SCCVisitSec
                        << " (" << step1Pct(step1SCCVisitSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_footprint_sort: " << step1SCCSortSec
                        << " (" << step1Pct(step1SCCSortSec) << "% of step1)\n";
        SVFUtil::outs() << "  step2_dedup: " << step2Sec << " (" << pct(step2Sec) << "%)\n";
        SVFUtil::outs() << "  step3_init: " << step3Sec << " (" << pct(step3Sec) << "%)\n";
        SVFUtil::outs() << "  step4_meld: " << step4Sec << " (" << pct(step4Sec) << "%)\n";
        SVFUtil::outs() << "  step5_versionize: " << step5Sec << " (" << pct(step5Sec) << "%)\n";
        SVFUtil::outs() << "  step6_reliance: " << step6Sec << " (" << pct(step6Sec) << "%)\n";
        SVFUtil::outs() << "  step7_assign: " << step7Sec << " (" << pct(step7Sec) << "%)\n";
        SVFUtil::outs() << "  finalize_refs: " << finalizeSec << " (" << pct(finalizeSec) << "%)\n";
    }
}

void VersionedFlowSensitive::newmeldLabel(void)
{
    double start = stat->getClk(true);

    struct MeldLabelProfileTotals
    {
        u64_t processedObjects = 0;
        u64_t dedupSkippedObjects = 0;
        double setupTicks = 0.0;
        double step1Ticks = 0.0;
        double step1SeedTicks = 0.0;
        double step1SCCInitTicks = 0.0;
        double step1SCCVisitTicks = 0.0;
        double step1SCCSortTicks = 0.0;
        double step2Ticks = 0.0;
        double step3Ticks = 0.0;
        double step4Ticks = 0.0;
        double step5Ticks = 0.0;
        double step6Ticks = 0.0;
        double step7Ticks = 0.0;
        double finalizeTicks = 0.0;

        void addFrom(const MeldLabelProfileTotals &other)
        {
            processedObjects += other.processedObjects;
            dedupSkippedObjects += other.dedupSkippedObjects;
            step1Ticks += other.step1Ticks;
            step1SeedTicks += other.step1SeedTicks;
            step1SCCInitTicks += other.step1SCCInitTicks;
            step1SCCVisitTicks += other.step1SCCVisitTicks;
            step1SCCSortTicks += other.step1SCCSortTicks;
            step2Ticks += other.step2Ticks;
            step3Ticks += other.step3Ticks;
            step4Ticks += other.step4Ticks;
            step5Ticks += other.step5Ticks;
            step6Ticks += other.step6Ticks;
            step7Ticks += other.step7Ticks;
        }
    };

    const bool enableMeldProfile = Options::VDGStat();
    const bool enableEquiMergeDump = false;
    const u64_t equiMergeDumpLimit = 2000;
    MeldLabelProfileTotals profileTotals;
    std::mutex profileMutex;
    std::mutex equiMergeDumpMutex;
    u64_t equiMergeDumpEmitted = 0;
    u64_t equiMergeDumpSuppressed = 0;
    const double setupStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

    assert(Options::VersioningThreads() > 0 && "VFS::meldLabel: number of versioning threads must be > 0!");

    // Nodes requiring explicit consume/yield assignment during solving.
    std::vector<NodeID> nodesWhichNeedVersions;
    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID n = it->first;
        if (delta(n) || deltaSource(n) || isStore(n) || isLoad(n)) nodesWhichNeedVersions.push_back(n);
    }

    std::mutex *versionMutexes = new std::mutex[nodesWhichNeedVersions.size()];

    // Map of footprints to the canonical object "owning" the footprint.
    Map<std::vector<const IndirectSVFGEdge *>, NodeID> footprintOwner;

    std::queue<NodeID> objectQueue;
    for (const NodeID o : prelabeledObjects)
    {
        // "Touch" maps with o so we don't need to lock on them.
        versionReliance[o];
        stmtReliance[o];
        objectQueue.push(o);
    }

    std::mutex objectQueueMutex;
    std::mutex footprintOwnerMutex;

    if (enableMeldProfile)
        profileTotals.setupTicks = stat->getClk(true) - setupStartTicks;

    auto meldVersionWorker = [this, &footprintOwner, &objectQueue,
                                    &objectQueueMutex, &footprintOwnerMutex, &versionMutexes,
                                    &nodesWhichNeedVersions,
                                    &profileMutex, &profileTotals,
                                    &equiMergeDumpMutex, &equiMergeDumpEmitted, &equiMergeDumpSuppressed,
                                    enableMeldProfile]
         (const unsigned thread)
    {
        (void)thread;
        MeldLabelProfileTotals localProfile;
        std::vector<int> partOf;
        std::vector<const IndirectSVFGEdge *> footprint;
        auto nodeKind = [this](const NodeID id) -> std::string
        {
            std::string kinds;
            if (this->isLoad(id)) kinds += "load|";
            if (this->delta(id)) kinds += "delta|";
            if (this->deltaSource(id)) kinds += "deltasource|";
            if (this->isStore(id)) kinds += "store|";
            if (!kinds.empty())
            {
                kinds.pop_back();
                return kinds;
            }
            return "other";
        };

        while (true)
        {
            NodeID o;
            {
                std::lock_guard<std::mutex> guard(objectQueueMutex);
                // No more objects? Done.
                if (objectQueue.empty()) break;
                o = objectQueue.front();
                objectQueue.pop();
            }

            if (enableMeldProfile)
                ++localProfile.processedObjects;

            // 1. Compute the SCCs for the nodes on the graph overlay of o.
            // For starting nodes, we only need those which did prelabeling for o specifically.
            const double step1StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            const double step1SeedStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            const Map<NodeID, NodeVector>::const_iterator startsIt = objStartingNodes.find(o);
            static const NodeVector emptyStartingNodes;
            const NodeVector &osStartingNodes
                = startsIt == objStartingNodes.end() ? emptyStartingNodes : startsIt->second;
            if (enableMeldProfile)
                localProfile.step1SeedTicks += stat->getClk(true) - step1SeedStartTicks;

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
                localProfile.step1Ticks += stat->getClk(true) - step1StartTicks;
                localProfile.step1SCCInitTicks += sccDetectProfile.initTicks;
                localProfile.step1SCCVisitTicks += sccDetectProfile.visitTicks;
                localProfile.step1SCCSortTicks += sccDetectProfile.sortTicks;
            }

            // 2. Skip any further processing of a footprint we have seen before.
            const double step2StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            bool isCanonicalFootprint = true;
            {
                std::lock_guard<std::mutex> guard(footprintOwnerMutex);
                const Map<std::vector<const IndirectSVFGEdge *>, NodeID>::const_iterator canonOwner
                    = footprintOwner.find(footprint);
                if (canonOwner == footprintOwner.end())
                {
                    this->equivalentObject[o] = o;
                    footprintOwner[footprint] = o;
                }
                else
                {
                    this->equivalentObject[o] = canonOwner->second;
                    this->recordRepeat(o, canonOwner->second);
                    isCanonicalFootprint = false;
                }
            }

            if (enableMeldProfile)
                localProfile.step2Ticks += stat->getClk(true) - step2StartTicks;

            if (!isCanonicalFootprint)
            {
                if (enableMeldProfile)
                    ++localProfile.dedupSkippedObjects;
                // Reliance maps are kept on canonical objects only and queried through
                // equivalentObject mapping at use sites.
                continue;
            }

            // 3. Initialize DSU-based equivalence classes for SCC consume versions,
            // and allocate dedicated yield ids for store nodes.
            const double step3StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
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

            if (enableMeldProfile)
                localProfile.step3Ticks += stat->getClk(true) - step3StartTicks;

            // 4. Build SCC reliance and propagate SCC equivalence rules.
            const double step4StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

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
                const size_t rawPredNum = inIt->second.size();
                size_t uniquePredNum = rawPredNum;
                NodeID uniquePred = 0;
                if (enableEquiMergeDump && rawPredNum > 1)
                {
                    NodeVector uniquePreds = inIt->second;
                    std::sort(uniquePreds.begin(), uniquePreds.end());
                    uniquePreds.erase(std::unique(uniquePreds.begin(), uniquePreds.end()), uniquePreds.end());
                    uniquePredNum = uniquePreds.size();
                    if (uniquePredNum == 1)
                        uniquePred = uniquePreds.front();
                }
                if (enableEquiMergeDump && rawPredNum > 1 && uniquePredNum == 1)
                {
                    std::lock_guard<std::mutex> dumpGuard(equiMergeDumpMutex);
                    if (equiMergeDumpEmitted < equiMergeDumpLimit)
                    {
                        SVFUtil::outs() << "VFS[newmeldLabel][merge-dump] duplicate footprint preds:"
                                        << " obj " << o
                                        << " n " << n << "(" << nodeKind(n) << ",scc " << nSCC << ")"
                                        << " raw_preds " << rawPredNum
                                        << " uniq_preds " << uniquePredNum
                                        << " uniq_pred " << uniquePred << "(" << nodeKind(uniquePred) << ")\n";
                        ++equiMergeDumpEmitted;
                    }
                    else
                    {
                        ++equiMergeDumpSuppressed;
                    }
                }
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
                        const bool merged = VersionManager.unite(mEquiVersion, nEquiVersion);
                        if (enableEquiMergeDump)
                        {
                            std::lock_guard<std::mutex> dumpGuard(equiMergeDumpMutex);
                            if (equiMergeDumpEmitted < equiMergeDumpLimit)
                            {
                                SVFUtil::outs() << "VFS[newmeldLabel][merge-dump] merge candidate:"
                                                << " obj " << o
                                                << " m " << m << "(" << nodeKind(m) << ",scc " << mSCC << ")"
                                                << " -> n " << n << "(" << nodeKind(n) << ",scc " << nSCC << ")"
                                                << " raw_preds " << rawPredNum
                                                << " uniq_preds " << uniquePredNum
                                                << " merged " << (merged ? 1 : 0) << "\n";
                                ++equiMergeDumpEmitted;
                            }
                            else
                            {
                                ++equiMergeDumpSuppressed;
                            }
                        }
                    }
                }
            }
            if (enableMeldProfile)
                localProfile.step4Ticks += stat->getClk(true) - step4StartTicks;

            // 5. Compress DSU reps into dense Version ids.
            const double step5StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
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
            Map<NodeID, Version> loadsConsumedVersion;
            for (auto const& nmv : storesYieldedEquiVersion)
            {
                const NodeID n = nmv.first;
                const EquiVersion &mv = nmv.second;
                const EquiVersion rep = VersionManager.find(mv);

                Map<EquiVersion, Version>::const_iterator foundVersion = mvv.find(rep);
                Version v = foundVersion == mvv.end() ? mvv[rep] = ++curVersion : foundVersion->second;
                storesYieldedVersion[n] = v;
            }

            storesYieldedEquiVersion.clear();

            mvv.clear();
            this->recordVersionForObj(o, curVersion);
            if (enableMeldProfile)
                localProfile.step5Ticks += stat->getClk(true) - step5StartTicks;

            // 6. From SCC reliance, determine version reliances.
            const double step6StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            Map<Version, std::vector<Version>> &osVersionReliance = this->versionReliance.at(o);
            for (u32_t scc = 0; scc < numSCCs; ++scc)
            {
                if (sccReliance[scc].empty()) continue;

                // Reliance source uses store-yield Version when the predecessor SCC is store-backed;
                // otherwise it uses the SCC consume Version.
                const Version version
                    = storeSCC[scc] != -1 ? storesYieldedVersion[storeSCC[scc]] : sccToVersion[scc];

                std::vector<Version> &reliantVersions = osVersionReliance[version];
                for (const int reliantSCC : sccReliance[scc])
                {
                    const Version reliantVersion = sccToVersion[reliantSCC];
                    if (version != reliantVersion)
                    {
                        // sccReliance is a set, no need to worry about duplicates.
                        reliantVersions.push_back(reliantVersion);
                    }
                }
            }
            if (enableMeldProfile)
                localProfile.step6Ticks += stat->getClk(true) - step6StartTicks;

            // 7. a. Save versions for nodes which need them.
            //    b. Fill in stmtReliance.
            // TODO: maybe randomize iteration order for less contention? Needs profiling.
            const double step7StartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;
            Map<Version, NodeBS> &osStmtReliance = this->stmtReliance.at(o);
            for (size_t i = 0; i < nodesWhichNeedVersions.size(); ++i)
            {
                const NodeID n = nodesWhichNeedVersions[i];
                std::mutex &mutex = versionMutexes[i];

                const int scc = partOf[n];
                if (scc == -1) continue;

                std::lock_guard<std::mutex> guard(mutex);

                const Version c = sccToVersion[scc];
                if (c != invalidVersion)
                {
                    this->setConsume(n, o, c);
                    // Version-change reprocessing is load-driven: keep only loads in stmt reliance.
                    if (this->isLoad(n)) osStmtReliance[c].set(n);
                }

                if (this->isStore(n))
                {
                    const Map<NodeID, Version>::const_iterator yIt = storesYieldedVersion.find(n);
                    if (yIt != storesYieldedVersion.end()) this->setYield(n, o, yIt->second);
                }
            }
            if (enableMeldProfile)
                localProfile.step7Ticks += stat->getClk(true) - step7StartTicks;
        }

        if (enableMeldProfile)
        {
            std::lock_guard<std::mutex> guard(profileMutex);
            profileTotals.addFrom(localProfile);
        }
    };

    std::vector<std::thread> workers;
    for (unsigned i = 0; i < Options::VersioningThreads(); ++i) workers.push_back(std::thread(meldVersionWorker, i));
    for (std::thread &worker : workers) worker.join();
    if (enableEquiMergeDump)
    {
        SVFUtil::outs() << "VFS[newmeldLabel][merge-dump] emitted: " << equiMergeDumpEmitted
                        << ", suppressed: " << equiMergeDumpSuppressed
                        << ", limit: " << equiMergeDumpLimit << "\n";
    }

    const double finalizeStartTicks = enableMeldProfile ? stat->getClk(true) : 0.0;

    // Fill equivalent objects with references to canonical reliance maps.
    versionRelianceRef.clear();
    stmtRelianceRef.clear();
    for (const Map<NodeID, NodeID>::value_type &kv : equivalentObject)
    {
        const NodeID o = kv.first;
        const NodeID canon = kv.second;
        versionRelianceRef[o] = &versionReliance[canon];
        stmtRelianceRef[o] = &stmtReliance[canon];
    }

    if (enableMeldProfile)
        profileTotals.finalizeTicks = stat->getClk(true) - finalizeStartTicks;

    delete[] versionMutexes;

    double end = stat->getClk(true);
    meldLabelingTime = (end - start) / TIMEINTERVAL;

    if (enableMeldProfile)
    {
        const double setupSec = profileTotals.setupTicks / TIMEINTERVAL;
        const double step1Sec = profileTotals.step1Ticks / TIMEINTERVAL;
        const double step1SeedSec = profileTotals.step1SeedTicks / TIMEINTERVAL;
        const double step1SCCInitSec = profileTotals.step1SCCInitTicks / TIMEINTERVAL;
        const double step1SCCVisitSec = profileTotals.step1SCCVisitTicks / TIMEINTERVAL;
        const double step1SCCSortSec = profileTotals.step1SCCSortTicks / TIMEINTERVAL;
        const double step2Sec = profileTotals.step2Ticks / TIMEINTERVAL;
        const double step3Sec = profileTotals.step3Ticks / TIMEINTERVAL;
        const double step4Sec = profileTotals.step4Ticks / TIMEINTERVAL;
        const double step5Sec = profileTotals.step5Ticks / TIMEINTERVAL;
        const double step6Sec = profileTotals.step6Ticks / TIMEINTERVAL;
        const double step7Sec = profileTotals.step7Ticks / TIMEINTERVAL;
        const double finalizeSec = profileTotals.finalizeTicks / TIMEINTERVAL;

        const double accumulatedSec =
            setupSec + step1Sec + step2Sec + step3Sec + step4Sec + step5Sec + step6Sec + step7Sec + finalizeSec;
        auto pct = [accumulatedSec](double sec) -> double
        {
            return accumulatedSec > 0.0 ? (100.0 * sec / accumulatedSec) : 0.0;
        };
        auto step1Pct = [step1Sec](double sec) -> double
        {
            return step1Sec > 0.0 ? (100.0 * sec / step1Sec) : 0.0;
        };

        SVFUtil::outs() << "VFS meldLabel profiling:\n";
        SVFUtil::outs() << "  objects processed: " << profileTotals.processedObjects
                        << ", dedup skipped: " << profileTotals.dedupSkippedObjects << "\n";
        SVFUtil::outs() << "  wall total (sec): " << meldLabelingTime << "\n";
        SVFUtil::outs() << "  accumulated step total (sec): " << accumulatedSec << "\n";
        SVFUtil::outs() << "  setup: " << setupSec << " (" << pct(setupSec) << "%)\n";
        SVFUtil::outs() << "  step1_scc: " << step1Sec << " (" << pct(step1Sec) << "%)\n";
        SVFUtil::outs() << "    step1_seed_select: " << step1SeedSec
                        << " (" << step1Pct(step1SeedSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_scc_init: " << step1SCCInitSec
                        << " (" << step1Pct(step1SCCInitSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_scc_visit: " << step1SCCVisitSec
                        << " (" << step1Pct(step1SCCVisitSec) << "% of step1)\n";
        SVFUtil::outs() << "    step1_footprint_sort: " << step1SCCSortSec
                        << " (" << step1Pct(step1SCCSortSec) << "% of step1)\n";
        SVFUtil::outs() << "  step2_dedup: " << step2Sec << " (" << pct(step2Sec) << "%)\n";
        SVFUtil::outs() << "  step3_init: " << step3Sec << " (" << pct(step3Sec) << "%)\n";
        SVFUtil::outs() << "  step4_meld: " << step4Sec << " (" << pct(step4Sec) << "%)\n";
        SVFUtil::outs() << "  step5_versionize: " << step5Sec << " (" << pct(step5Sec) << "%)\n";
        SVFUtil::outs() << "  step6_reliance: " << step6Sec << " (" << pct(step6Sec) << "%)\n";
        SVFUtil::outs() << "  step7_assign: " << step7Sec << " (" << pct(step7Sec) << "%)\n";
        SVFUtil::outs() << "  finalize_refs: " << finalizeSec << " (" << pct(finalizeSec) << "%)\n";
    }
}

void VersionedFlowSensitive::expandEquivalentObjectVersions(void)
{
    // Share canonical o:l:v maps by reference for equivalent objects.
    for (const Map<NodeID, NodeID>::value_type &kv : equivalentObject)
    {
        const NodeID o = kv.first;
        const NodeID canonObj = kv.second;
        if (o == canonObj) continue;

        const ObjToLocVersionMap::const_iterator cIt = consume.find(canonObj);
        if (cIt != consume.end())
            consume[o] = cIt->second;

        const ObjToLocVersionMap::const_iterator yIt = yield.find(canonObj);
        if (yIt != yield.end())
            yield[o] = yIt->second;
    }
}

void VersionedFlowSensitive::buildVersionDependencyGraphs(void)
{
    double start = stat->getClk(true);

    vdgManager.clear();
    // Store sites whose consume->yield relation is still deferred because they are
    // currently strong-update singleton stores.
    pendingStoreObjsByLoc.clear();

    std::vector<int8_t> nonSingletonCache(pag->getTotalNodeNum(), -1);
    auto isNonSingletonObj = [&](const NodeID o) -> bool
    {
        int8_t &cached = nonSingletonCache[o];
        if (cached >= 0) return cached != 0;
        const bool nonSingleton = isHeapMemObj(o) || isArrayMemObj(o)
            || pag->getBaseObject(o)->isFieldInsensitive()
            || isLocalVarInRecursiveFun(o);
        cached = nonSingleton ? 1 : 0;
        return nonSingleton;
    };

    std::vector<VDGSimplifyPass> passes;
    buildVDGSimplifyPassPipeline(passes, Options::VDGPassOrder());

    auto addVirtualIndCallEdgeForObj =
        [this](NodeID srcId, NodeID dstId, NodeID o, VDG &graph)
    {
        const SVFGNode *srcNode = svfg->getSVFGNode(srcId);
        const SVFGNode *dstNode = svfg->getSVFGNode(dstId);
        const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
        const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dstNode);
        if (!srcMR || !dstMR) return;
        if (!srcMR->getPointsTo().test(o) || !dstMR->getPointsTo().test(o)) return;

        assert(delta(dstId) && "VFS::updateConnectedNodes: new edges should be to delta nodes!");
        assert(deltaSource(srcId) && "VFS::updateConnectedNodes: new indirect edges should be from delta source nodes!");

        const Version srcY = getYield(srcId, o);
        if (srcY == invalidVersion) return;
        const Version dstC = getConsume(dstId, o);
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

    std::vector<NodeID> objects;
    objects.reserve(equivalentObject.size());
    for (const Map<NodeID, NodeID>::value_type &kv : equivalentObject)
        objects.push_back(kv.first);
    std::sort(objects.begin(), objects.end());

    // Object-major pipeline:
    // 1) materialize edges/nodes for one object
    // 2) simplify that object's VDG immediately
    // This limits the number of large unsimplified VDGs resident at once.
    for (const NodeID o : objects)
    {
        const VersionRelianceRefMap::const_iterator relIt = versionRelianceRef.find(o);
        const Map<Version, std::vector<Version>> *osVersionReliance =
            (relIt == versionRelianceRef.end()) ? nullptr : relIt->second;

        const ObjToLocVersionMap::const_iterator cIt = consume.find(o);
        const LocToVersionMap *consumeMap =
            (cIt == consume.end() || !cIt->second) ? nullptr : cIt->second.get();

        const ObjToLocVersionMap::const_iterator yIt = yield.find(o);
        const LocToVersionMap *yieldMap =
            (yIt == yield.end() || !yIt->second) ? nullptr : yIt->second.get();

        const bool hasVersionReliance = (osVersionReliance != nullptr && !osVersionReliance->empty());
        const bool hasConsume = (consumeMap != nullptr && !consumeMap->empty());
        if (!hasVersionReliance && !hasConsume)
            continue;

        VDG &graph = *vdgManager.getOrCreateVDG(o);

        if (hasVersionReliance)
        {
            for (const Map<Version, std::vector<Version>>::value_type &vrv : *osVersionReliance)
            {
                const Version v = vrv.first;
                if (v == invalidVersion) continue;
                for (const Version rv : vrv.second)
                {
                    if (rv == invalidVersion || rv == v) continue;
                    graph.getOrAddNode(v, false, false);
                    graph.getOrAddNode(rv, false, false);
                    graph.addEdge(v, rv, false);
                }
            }
        }

        if (hasConsume)
        {
            for (const LocToVersionMap::value_type &lv : *consumeMap)
            {
                const NodeID l = lv.first;
                const Version c = lv.second;
                if (c == invalidVersion) continue;

                graph.getOrAddNode(c, isLoad(l), false);

                if (isStore(l))
                {
                    const StoreSVFGNode *store = SVFUtil::dyn_cast<StoreSVFGNode>(svfg->getSVFGNode(l));
                    if (store == nullptr)
                        continue;

                    const NodeID p = store->getPAGDstNodeID();
                    const PointsTo &dstPts = ander->getPts(p);
                    if (dstPts.count() == 0)
                        continue;

                    if (!yieldMap) continue;
                    const LocToVersionMap::const_iterator bIt = yieldMap->find(l);
                    if (bIt == yieldMap->end()) continue;
                    const Version b = bIt->second;
                    if (b == invalidVersion) continue;

                    if (c == b)
                    {
                        graph.getOrAddNode(c, false, true);
                        continue;
                    }

                    graph.getOrAddNode(c, false, false);
                    const NodeID q = store->getPAGSrcNodeID();
                    graph.getOrAddNode(b, false, !ander->getPts(q).empty());

                    const bool nonSingletonObj = isNonSingletonObj(o);
                    graph.addEdge(c, b, !nonSingletonObj);
                    if (!nonSingletonObj)
                        pendingStoreObjsByLoc[l].push_back(o);
                }
                else
                {
                    // Delta virtual edges (formal-in / actual-out) for this object only.
                    const NodeVector &indirectSrcs = getIndirectSourcesForDst(l);
                    for (const NodeID srcId : indirectSrcs)
                        addVirtualIndCallEdgeForObj(srcId, l, o, graph);
                }
            }
        }

        for (VDGSimplifyPass pass : passes)
            pass(graph);
    }

    // Version reliance map is no longer needed once dependence edges are materialized.
    versionRelianceRef.clear();
    VersionRelianceMap().swap(versionReliance);

    double end = stat->getClk(true);
    vdgBuildTime = (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::bindStmtRelianceToVDGNodes(void)
{
    // Bind stmt reliance only after VDG simplification/merges to avoid repeated
    // reliance set merges during structural graph transformations.
    for (const StmtRelianceRefMap::value_type &ovssRef : stmtRelianceRef)
    {
        const NodeID o = ovssRef.first;
        const Map<Version, NodeBS> *osStmtReliance = ovssRef.second;
        if (osStmtReliance == nullptr) continue;

        VDG *graph = vdgManager.tryGetVDG(o);
        if (graph == nullptr) continue;

        // Aggregate by current rep version so each rep is materialized once.
        Map<Version, NodeBS> repStmtReliance;
        for (const Map<Version, NodeBS>::value_type &vss : *osStmtReliance)
        {
            const Version v = vss.first;
            if (v == invalidVersion) continue;
            const Version repV = vdgManager.getRepVersionOrInvalid(o, v);
            if (repV == invalidVersion) continue;
            repStmtReliance[repV] |= vss.second;
        }

        for (const Map<Version, NodeBS>::value_type &repVss : repStmtReliance)
        {
            if (!repVss.second.empty())
                graph->bindStmtReliance(repVss.first, repVss.second);
        }
    }

    // Stmt reliance maps are no longer needed after being materialized to VDG nodes.
    stmtRelianceRef.clear();
    decltype(stmtReliance)().swap(stmtReliance);
}
