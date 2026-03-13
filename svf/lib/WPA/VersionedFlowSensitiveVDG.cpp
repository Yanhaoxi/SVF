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
                }

                // Push into worklist because its consume == its yield.
                vWorklist.push(l);
                if (mr->getPointsTo().count() != 0) ++numPrelabeledNodes;
            }
        }
    }

    double end = stat->getClk(true);
    prelabelingTime = (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::meldLabel(void)
{
    double start = stat->getClk(true);

    assert(Options::VersioningThreads() > 0 && "VFS::meldLabel: number of versioning threads must be > 0!");

    // Nodes which have at least one object on them given a prelabel + the Andersen's points-to
    // set of interest so we don't keep calling getPts. For Store nodes, we'll fill that in, for
    // MR nodes, we won't as its getPointsTo is cheap.
    // TODO: preferably we cache both for ease and to avoid the dyn_cast/isa, but Andersen's points-to
    // sets are PointsTo and MR's sets are NodeBS, which are incompatible types. Maybe when we can
    // use std::option.
    std::vector<std::pair<const SVFGNode *, const PointsTo *>> prelabeledNodes;
    // Fast query for the above.
    std::vector<bool> isPrelabeled(svfg->getTotalNodeNum(), false);
    while (!vWorklist.empty())
    {
        const NodeID n = vWorklist.pop();
        isPrelabeled[n] = true;

        const SVFGNode *sn = svfg->getSVFGNode(n);
        const PointsTo *nPts = nullptr;
        if (const StoreSVFGNode *store = SVFUtil::dyn_cast<StoreSVFGNode>(sn))
        {
            const NodeID p = store->getPAGDstNodeID();
            nPts = &(this->ander->getPts(p));
        }

        prelabeledNodes.push_back(std::make_pair(sn, nPts));
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

    auto meldVersionWorker = [this, &footprintOwner, &objectQueue,
                                    &objectQueueMutex, &footprintOwnerMutex, &versionMutexes,
                                    &prelabeledNodes, &isPrelabeled, &nodesWhichNeedVersions]
         (const unsigned thread)
    {
        while (true)
        {
            NodeID o;
            {
                std::lock_guard<std::mutex> guard(objectQueueMutex);
                // No more objects? Done.
                if (objectQueue.empty()) return;
                o = objectQueue.front();
                objectQueue.pop();
            }

            // 1. Compute the SCCs for the nodes on the graph overlay of o.
            // For starting nodes, we only need those which did prelabeling for o specifically.
            // TODO: maybe we should move this to prelabel with a map (o -> starting nodes).
            std::vector<const SVFGNode *> osStartingNodes;
            for (std::pair<const SVFGNode *, const PointsTo *> snPts : prelabeledNodes)
            {
                const SVFGNode *sn = snPts.first;
                const PointsTo *pts = snPts.second;
                if (pts != nullptr)
                {
                    if (pts->test(o)) osStartingNodes.push_back(sn);
                }
                else if (const MRSVFGNode *mr = SVFUtil::dyn_cast<MRSVFGNode>(sn))
                {
                    if (mr->getPointsTo().test(o)) osStartingNodes.push_back(sn);
                }
                else
                {
                    assert(false && "VFS::meldLabel: unexpected prelabeled node!");
                }
            }

            std::vector<int> partOf;
            std::vector<const IndirectSVFGEdge *> footprint;
            unsigned numSCCs = SCC::detectSCCs(this, this->svfg, o, osStartingNodes, partOf, footprint);
            this->recordStmt(footprint.size());

            // 2. Skip any further processing of a footprint we have seen before.
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
                    // Reliance maps are kept on canonical objects only and queried through
                    // equivalentObject mapping at use sites.
                    continue;
                }
            }

            // 3. a. Initialise the MeldVersion of prelabeled nodes (SCCs).
            //    b. Initialise a todo list of all the nodes we need to version,
            //       sorted according to topological order.
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
            for (const SVFGNode *sn : osStartingNodes) reachableNodes.insert(sn->getId());
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

            // 4. a. Do meld versioning.
            //    b. Determine SCC reliances.
            //    c. Build a footprint for o (all edges which it is found on).
            //    d. Determine which SCCs belong to stores.

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

            // 5. Transform meld versions belonging to SCCs into versions.
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
            this->recordVersion(curVersion);

            // 6. From SCC reliance, determine version reliances.
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

            // 7. a. Save versions for nodes which need them.
            //    b. Fill in stmtReliance.
            // TODO: maybe randomize iteration order for less contention? Needs profiling.
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
        }
    };

    std::vector<std::thread> workers;
    for (unsigned i = 0; i < Options::VersioningThreads(); ++i) workers.push_back(std::thread(meldVersionWorker, i));
    for (std::thread &worker : workers) worker.join();

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

    delete[] versionMutexes;

    double end = stat->getClk(true);
    meldLabelingTime = (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::newmeldLabel(void)
{
    double start = stat->getClk(true);

    assert(Options::VersioningThreads() > 0 && "VFS::meldLabel: number of versioning threads must be > 0!");

    // Nodes which have at least one object on them given a prelabel + the Andersen's points-to
    // set of interest so we don't keep calling getPts. For Store nodes, we'll fill that in, for
    // MR nodes, we won't as its getPointsTo is cheap.
    // TODO: preferably we cache both for ease and to avoid the dyn_cast/isa, but Andersen's points-to
    // sets are PointsTo and MR's sets are NodeBS, which are incompatible types. Maybe when we can
    // use std::option.
    std::vector<std::pair<const SVFGNode *, const PointsTo *>> prelabeledNodes;
    // Fast query for the above.
    std::vector<bool> isPrelabeled(svfg->getTotalNodeNum(), false);
    while (!vWorklist.empty())
    {
        const NodeID n = vWorklist.pop();
        isPrelabeled[n] = true;

        const SVFGNode *sn = svfg->getSVFGNode(n);
        const PointsTo *nPts = nullptr;
        if (const StoreSVFGNode *store = SVFUtil::dyn_cast<StoreSVFGNode>(sn))
        {
            const NodeID p = store->getPAGDstNodeID();
            nPts = &(this->ander->getPts(p));
        }

        prelabeledNodes.push_back(std::make_pair(sn, nPts));
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

    auto meldVersionWorker = [this, &footprintOwner, &objectQueue,
                                    &objectQueueMutex, &footprintOwnerMutex, &versionMutexes,
                                    &prelabeledNodes, &isPrelabeled, &nodesWhichNeedVersions]
         (const unsigned thread)
    {
        while (true)
        {
            NodeID o;
            {
                std::lock_guard<std::mutex> guard(objectQueueMutex);
                // No more objects? Done.
                if (objectQueue.empty()) return;
                o = objectQueue.front();
                objectQueue.pop();
            }

            // 1. Compute the SCCs for the nodes on the graph overlay of o.
            // For starting nodes, we only need those which did prelabeling for o specifically.
            // TODO: maybe we should move this to prelabel with a map (o -> starting nodes).
            std::vector<const SVFGNode *> osStartingNodes;
            for (std::pair<const SVFGNode *, const PointsTo *> snPts : prelabeledNodes)
            {
                const SVFGNode *sn = snPts.first;
                const PointsTo *pts = snPts.second;
                if (pts != nullptr)
                {
                    if (pts->test(o)) osStartingNodes.push_back(sn);
                }
                else if (const MRSVFGNode *mr = SVFUtil::dyn_cast<MRSVFGNode>(sn))
                {
                    if (mr->getPointsTo().test(o)) osStartingNodes.push_back(sn);
                }
                else
                {
                    assert(false && "VFS::meldLabel: unexpected prelabeled node!");
                }
            }

            std::vector<int> partOf;
            std::vector<const IndirectSVFGEdge *> footprint;
            unsigned numSCCs = SCC::detectSCCs(this, this->svfg, o, osStartingNodes, partOf, footprint);
            this->recordStmt(footprint.size());

            // 2. Skip any further processing of a footprint we have seen before.
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
                    // Reliance maps are kept on canonical objects only and queried through
                    // equivalentObject mapping at use sites.
                    continue;
                }
            }

            // 3. a. Initialise the MeldVersion of prelabeled nodes (SCCs).
            //    b. Initialise a todo list of all the nodes we need to version,
            //       sorted according to topological order.
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
            for (const SVFGNode *sn : osStartingNodes) reachableNodes.insert(sn->getId());
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

            // 4. a. Do meld versioning.
            //    b. Determine SCC reliances.
            //    c. Build a footprint for o (all edges which it is found on).
            //    d. Determine which SCCs belong to stores.

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

            // 5. Transform meld versions belonging to SCCs into versions.
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
            this->recordVersion(curVersion);

            // 6. From SCC reliance, determine version reliances.
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

            // 7. a. Save versions for nodes which need them.
            //    b. Fill in stmtReliance.
            // TODO: maybe randomize iteration order for less contention? Needs profiling.
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
        }
    };

    std::vector<std::thread> workers;
    for (unsigned i = 0; i < Options::VersioningThreads(); ++i) workers.push_back(std::thread(meldVersionWorker, i));
    for (std::thread &worker : workers) worker.join();

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

    delete[] versionMutexes;

    double end = stat->getClk(true);
    meldLabelingTime = (end - start) / TIMEINTERVAL;
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
