//===- VersionedFlowSensitive.cpp -- Versioned flow-sensitive pointer analysis------------//

/*
 * VersionedFlowSensitive.cpp
 *
 *  Created on: Jun 26, 2020
 *      Author: Mohamad Barbar
 */

#include "Util/GeneralType.h"
#include "WPA/Andersen.h"
#include "WPA/VersionedFlowSensitive.h"
#include "Util/Options.h"
#include "MemoryModel/PointsTo.h"
#include <algorithm>
#include <cassert>
#include <cstddef>
#include <fstream>
#include <iostream>
#include <limits>
#include <memory>
#include <queue>
#include <thread>
#include <mutex>

using namespace SVF;

const Version VersionedFlowSensitive::invalidVersion = 0;
VersionedFlowSensitive *VersionedFlowSensitive::vfspta = nullptr;

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
}

VersionedVar VersionedFlowSensitive::atKey(NodeID var, Version version)
{
    assert(version != invalidVersion && "VersionedFlowSensitive::atKey: trying to use an invalid version!");
    return std::make_pair(var, version);
}

VersionedFlowSensitive::VersionedFlowSensitive(SVFIR *_pag, PTATY type)
    : FlowSensitive(_pag, type)
{
    numPrelabeledNodes = numPrelabelVersions = 0;
    prelabelingTime = meldLabelingTime = versionPropTime = vdgBuildTime = 0.0;
    memRSSBeforePrelabel = memSizeBeforePrelabel = 0;
    memRSSAfterVDGBuild = memSizeAfterVDGBuild = 0;
    memRSSAfterVDGSimplify = memSizeAfterVDGSimplify = 0;
    memRSSAfterRun = memSizeAfterRun = 0;
    // We'll grab vPtD in initialize.

    for (SVFIR::const_iterator it = pag->begin(); it != pag->end(); ++it)
    {
        if (SVFUtil::isa<ObjVar>(it->second)) equivalentObject[it->first] = it->first;
    }

    assert(!Options::OPTSVFG() && "VFS: -opt-svfg not currently supported with VFS.");
}

void VersionedFlowSensitive::initialize()
{
    auto captureMemUsage = [](u32_t &vmrss, u32_t &vmsize)
    {
        vmrss = 0;
        vmsize = 0;
        SVFUtil::getMemoryUsageKB(&vmrss, &vmsize);
    };

    FlowSensitive::initialize();
    // Overwrite the stat FlowSensitive::initialize gave us.
    delete stat;
    stat = new VersionedFlowSensitiveStat(this);

    vPtD = getVersionedPTDataTy();

    buildIsStoreLoadMaps();
    buildDeltaMaps();
    stmtPtsCache.clear();
    stmtPtsCache.resize(svfg->getTotalNodeNum());

    captureMemUsage(memRSSBeforePrelabel, memSizeBeforePrelabel);
    prelabel();
    meldLabel();
    expandEquivalentObjectVersions();
    // Build VDGs in object-major streaming mode and simplify each graph in-place.
    // As a result, "after build" already reflects post-simplification footprint.
    buildVersionDependencyGraphs();
    captureMemUsage(memRSSAfterVDGBuild, memSizeAfterVDGBuild);
    // Kept for stat/output compatibility with older runs where simplify was separated.
    captureMemUsage(memRSSAfterVDGSimplify, memSizeAfterVDGSimplify);
    bindStmtRelianceToVDGNodes();

    if (Options::DumpVDG())
    {
        std::string outName = Options::VDGOutput();
        outName += "_simplified";
        vdgManager.writeToFile(outName);
    }
    if (Options::VDGStat())
        vdgManager.dumpStats();

    removeAllIndirectSVFGEdges();
}

void VersionedFlowSensitive::finalize()
{
    SVFUtil::getMemoryUsageKB(&memRSSAfterRun, &memSizeAfterRun);
    FlowSensitive::finalize();
    // vPtD->dumpPTData();
    // dumpReliances();
    // dumpLocVersionMaps();
    if (Options::DumpVDG())
    {
        std::string outName = Options::VDGOutput();
        outName += "_final";
        vdgManager.writeToFile(outName);
    }
    if (Options::VDGStat())
        vdgManager.dumpStats();
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
                    // include store stmt for version between store is lack of connected edges
                    if (this->isStore(n) || this->isLoad(n)) osStmtReliance[c].set(n);
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

bool VersionedFlowSensitive::meld(MeldVersion &mv1, const MeldVersion &mv2)
{
    // Meld operator is union of bit vectors.
    return mv1 |= mv2;
}

bool VersionedFlowSensitive::delta(const NodeID l) const
{
    assert(l < deltaMap.size() && "VFS::delta: deltaMap is missing SVFG nodes!");
    return deltaMap[l];
}

bool VersionedFlowSensitive::deltaSource(const NodeID l) const
{
    assert(l < deltaSourceMap.size() && "VFS::delta: deltaSourceMap is missing SVFG nodes!");
    return deltaSourceMap[l];
}

void VersionedFlowSensitive::buildIsStoreLoadMaps(void)
{
    isStoreMap.resize(svfg->getTotalNodeNum(), false);
    isLoadMap.resize(svfg->getTotalNodeNum(), false);
    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        if (SVFUtil::isa<StoreSVFGNode>(it->second)) isStoreMap[it->first] = true;
        else if (SVFUtil::isa<LoadSVFGNode>(it->second)) isLoadMap[it->first] = true;
    }
}

bool VersionedFlowSensitive::isStore(const NodeID l) const
{
    assert(l < isStoreMap.size() && "VFS::isStore: isStoreMap is missing SVFG nodes!");
    return isStoreMap[l];
}

bool VersionedFlowSensitive::isLoad(const NodeID l) const
{
    assert(l < isLoadMap.size() && "VFS::isLoad: isLoadMap is missing SVFG nodes!");
    return isLoadMap[l];
}

void VersionedFlowSensitive::buildDeltaMaps(void)
{
    deltaMap.resize(svfg->getTotalNodeNum(), false);

    // Call block nodes corresponding to all delta nodes.
    Set<const CallICFGNode *> deltaCBNs;

    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID l = it->first;
        const SVFGNode *s = it->second;

        // Cases:
        //  * Function entry: can get new incoming indirect edges through ind. callsites.
        //  * Callsite returns: can get new incoming indirect edges if the callsite is indirect.
        //  * Otherwise: static.
        bool isDelta = false;
        if (const FunObjVar *fn = svfg->isFunEntrySVFGNode(s))
        {
            CallGraphEdge::CallInstSet callsites;
            /// use pre-analysis call graph to approximate all potential callsites
            ander->getCallGraph()->getIndCallSitesInvokingCallee(fn, callsites);
            isDelta = !callsites.empty();

            if (isDelta)
            {
                // TODO: could we use deltaCBNs in the call above, avoiding this loop?
                for (const CallICFGNode *cbn : callsites) deltaCBNs.insert(cbn);
            }
        }
        else if (const CallICFGNode *cbn = svfg->isCallSiteRetSVFGNode(s))
        {
            isDelta = cbn->isIndirectCall();
            if (isDelta) deltaCBNs.insert(cbn);
        }

        deltaMap[l] = isDelta;
    }

    deltaSourceMap.resize(svfg->getTotalNodeNum(), false);

    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID l = it->first;
        const SVFGNode *s = it->second;

        if (const CallICFGNode *cbn = SVFUtil::dyn_cast<CallICFGNode>(s->getICFGNode()))
        {
            if (deltaCBNs.find(cbn) != deltaCBNs.end()) deltaSourceMap[l] = true;
        }

        // TODO: this is an over-approximation but it sound, marking every formal out as
        //       a delta-source.
        if (SVFUtil::isa<FormalOUTSVFGNode>(s)) deltaSourceMap[l] = true;
    }
}

void VersionedFlowSensitive::removeAllIndirectSVFGEdges(void)
{
    for (SVFG::iterator nodeIt = svfg->begin(); nodeIt != svfg->end(); ++nodeIt)
    {
        SVFGNode *sn = nodeIt->second;

        const SVFGEdgeSetTy &inEdges = sn->getInEdges();
        std::vector<SVFGEdge *> toDeleteFromIn;
        for (SVFGEdge *e : inEdges)
        {
            if (SVFUtil::isa<IndirectSVFGEdge>(e)) toDeleteFromIn.push_back(e);
        }

        for (SVFGEdge *e : toDeleteFromIn) svfg->removeSVFGEdge(e);

        // Only need to iterate over incoming edges for each node because edges
        // will be deleted from in/out through removeSVFGEdge.
    }

    setGraph(svfg);
}

void VersionedFlowSensitive::solveWorklist()
{
    // Main solving loop: alternate between stmt worklist and version propagation
    // Uses priority-based processing: addr/load nodes first, then others, then stores last
    bool changed = true;
    while (changed)
    {
        changed = false;
        
        // Process priority worklist in order: addr/load (0) -> other (1) -> store (2)
        while (!isWorklistEmpty())
        {
            NodeID nodeId = popFromWorklist();
            processNode(nodeId);
            collapseFields();
        }
        
        // After stmt worklist is empty, do batch version propagation on all updated VDGs
        propagateAllVersions();
        
        // Check if any stmt was added back to worklist during propagation
        if (!isWorklistEmpty())
        {
            changed = true;
        }
    }
}


void VersionedFlowSensitive::propagateAllVersions()
{
    double start = stat->getClk();

    // Only process VDGs that have pending updates
    while (vdgManager.hasPendingVDGs())
    {
        const NodeID obj = vdgManager.popPendingVDG();
        VDG *graph = vdgManager.getVDG(obj);
        
        assert(graph->hasPendingUpdates() && "VFS::propagateAllVersions: pending VDG should have updates!");
        
        // Define propagation callback: union pts from srcV to dstV
        auto propagateCallback = [this, obj](Version srcV, Version dstV) -> bool
        {
            const VersionedVar srcVar = atKey(obj, srcV);
            const VersionedVar dstVar = atKey(obj, dstV);
            return vPtD->unionPts(dstVar, srcVar);
        };
        
        // Define stmt reliance callback: push related stmts to worklist and clear load cache.
        // Reliance is bound onto rep nodes and merged during VDG node merges.
        auto stmtRelianceCallback = [this, obj, graph](Version v)
        {
            const NodeBS& stmts = graph->getStmtReliance(v);
            for (NodeID s : stmts)
            {
                // stmtReliance contains both loads and stores (set in meldLabel).
                // For loads: clear the specific object bit so processLoad's delta includes it.
                if (isLoad(s))
                {
                    assert(s < stmtPtsCache.size() && "stmtPtsCache must be pre-sized to SVFG node count");
                    stmtPtsCache[s].reset(obj);
                }
                pushIntoWorklist(s);
            }
        };
        
        // Use VDG's propagation API
        graph->propagateInTopoOrder(propagateCallback, stmtRelianceCallback);
    }

    double end = stat->getClk();
    versionPropTime += (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::processNode(NodeID n)
{
    SVFGNode* sn = svfg->getSVFGNode(n);
    if (processSVFGNode(sn))
    {
        propagate(&sn);
    }
}

void VersionedFlowSensitive::updateConnectedNodes(const SVFGEdgeSetTy& newEdges)
{
    for (const SVFGEdge *e : newEdges)
    {
        SVFGNode *srcNode = e->getSrcNode();
        SVFGNode *dstNode = e->getDstNode();
        NodeID src = srcNode->getId();
        NodeID dst = dstNode->getId();

        if (SVFUtil::isa<PHISVFGNode>(dstNode)
                || SVFUtil::isa<FormalParmSVFGNode>(dstNode)
                || SVFUtil::isa<ActualRetSVFGNode>(dstNode))
        {
            /// Push src so that when src is processed, its propagate() will:
            /// 1. For AP->FP/FR->AR: call propagateFromAPToFP/propagateFromFRToAR to push pts
            /// 2. For PHI dst: propAlongDirectEdge returns true, pushing dst into worklist
            pushIntoWorklist(src);
        }
        else
        {
            const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(e);
            assert(ie != nullptr && "VFS::updateConnectedNodes: given direct edge?");

            assert(delta(dst) && "VFS::updateConnectedNodes: new edges should be to delta nodes!");
            assert(deltaSource(src) && "VFS::updateConnectedNodes: new indirect edges should be from delta source nodes!");

            const NodeBS &ept = ie->getPointsTo();
            // For every o, such that src --o--> dst, we need to set up reliance (and mark for propagation).
            for (const NodeID o : ept)
            {
                Version srcY = getYield(src, o);
                if (srcY == invalidVersion) continue;
                Version dstC = getConsume(dst, o);
                if (dstC == invalidVersion) continue;
                if(srcY==dstC) continue; // no self-loop

                // 间接调用触发，加入结构边（VDG不再记录边来源 kind）
                VDG *graph = vdgManager.tryGetVDG(o);
                if (!graph) continue;
                // Skip if either version was pruned during VDG simplification
                if (!graph->hasVersion(srcY) || !graph->hasVersion(dstC)) continue;
                // Use addEdge with version (auto-converts to rep)
                if(graph->addEdge(srcY, dstC, false)){
                    // Mark source as updated for batch propagation
                    vdgManager.markEdgeAdded(o, srcY);
                }
            }
        }
    }
}

bool VersionedFlowSensitive::processLoad(const LoadSVFGNode* load)
{
    double start = stat->getClk();

    bool changed = false;

    // l: p = *q
    NodeID l = load->getId();
    NodeID p = load->getPAGDstNodeID();
    NodeID q = load->getPAGSrcNodeID();

    // Load cache: stmtPtsCache[l] tracks which objects have been processed.
    // stmtRelianceCallback clears specific obj bits when versioned pts change.
    // Delta is handled on-the-fly via test_and_set (no temporary points-to diff set).
    const PointsTo& qpt = getPts(q);
    assert(l < stmtPtsCache.size() && "stmtPtsCache must be pre-sized to SVFG node count");
    PointsTo& cachedQPts = stmtPtsCache[l];
    bool hasDeltaQpt = false;
    const bool dstIsPointer = load->getPAGDstNode()->isPointer();

    // Iterate only newly-seen/invalidated objects for this load.
    for (NodeID o : qpt)
    {
        if (!cachedQPts.test_and_set(o))
            continue;

        hasDeltaQpt = true;
        // p = *q, the type of p must be a pointer
        if (!dstIsPointer)
            continue;

        if (isConstantObjCached(o)) continue;

        const Version c = getConsume(l, o);
        if (c != invalidVersion){
            VersionedVar repKey;
            if (vdgManager.tryAtRepKey(o, c, repKey) && vPtD->unionPts(p, repKey))
            {
                changed = true;
            }
        }

        if (isFieldInsensitive(o))
        {
            /// If o is a field-insensitive object, we should also get all field nodes'
            /// points-to sets and pass them to p.
            const NodeBS& fields = getAllFieldsObjVars(o);
            for (NodeID of : fields)
            {
                const Version c = getConsume(l, of);
                if (c == invalidVersion) continue;
                VersionedVar repKey;
                if (vdgManager.tryAtRepKey(of, c, repKey) && vPtD->unionPts(p, repKey))
                {
                    changed = true;
                }
            }
        }
    }
    if (!hasDeltaQpt)
    {
        double end = stat->getClk();
        loadTime += (end - start) / TIMEINTERVAL;
        return false;
    }
    double end = stat->getClk();
    loadTime += (end - start) / TIMEINTERVAL;

    return changed;
}

// 1.yield version get store content 2.yield version get consume version 3.propagate further
bool VersionedFlowSensitive::processStore(const StoreSVFGNode* store)
{
    NodeID p = store->getPAGDstNodeID();
    const PointsTo &ppt = getPts(p);

    if (ppt.empty()) return false;

    NodeID q = store->getPAGSrcNodeID();
    const PointsTo &qpt = getPts(q);

    NodeID l = store->getId();
    // l: *p = q

    double start = stat->getClk();

    if (!qpt.empty())
    {
        // *p = q, the type of q must be a pointer
        if (store->getPAGSrcNode()->isPointer())
        {
            for (NodeID o : ppt)
            {
                if (isConstantObjCached(o)) continue;

                const Version y = getYield(l, o);
                if (y == invalidVersion) continue;

                // Combined hasVersion + atRepKey: skip if version was pruned
                VersionedVar repKey;
                if (!vdgManager.tryAtRepKey(o, y, repKey)) continue;

                if (vPtD->unionPts(repKey, q))
                {
                    // Mark version as updated for batch propagation through VDG edges
                    vdgManager.markVersionUpdated(o, y);
                }
            }
        }
    }

    double end = stat->getClk();
    storeTime += (end - start) / TIMEINTERVAL;

    double updateStart = stat->getClk();

    auto pendingIt = pendingStoreObjsByLoc.find(l);
    if (pendingIt != pendingStoreObjsByLoc.end() && !pendingIt->second.empty())
    {
        const PointsTo& dstCPSet = ppt;
        NodeID singleton = 0;
        bool isSU = false;

        if (dstCPSet.count() == 1)
        {
            singleton = *dstCPSet.begin();
            if (!isHeapMemObj(singleton) && !isArrayMemObj(singleton)
                && !pag->getBaseObject(singleton)->isFieldInsensitive()
                && !isLocalVarInRecursiveFun(singleton))
            {
                isSU = true;
            }
        }

        NodeVector& pendingObjs = pendingIt->second;
        NodeVector survivors;
        survivors.reserve(pendingObjs.size());

        for (const NodeID o : pendingObjs)
        {
            // Keep the strong-updated singleton pending until it stops being strong-update.
            if (isSU && o == singleton)
            {
                survivors.push_back(o);
                continue;
            }

            const Version c = getConsume(l, o);
            const Version y = getYield(l, o);
            VDG *graph = vdgManager.tryGetVDG(o);

            if (c != invalidVersion && y != invalidVersion
                && graph && graph->hasVersion(c) && graph->hasVersion(y))
            {
                if (graph->addEdge(c, y, false))
                    vdgManager.markEdgeAdded(o, c);
            }
        }

        pendingObjs.swap(survivors);

        if (pendingObjs.empty())
            pendingStoreObjsByLoc.erase(pendingIt);
    }

    double updateEnd = stat->getClk();
    updateTime += (updateEnd - updateStart) / TIMEINTERVAL;

    return false;
}

bool VersionedFlowSensitive::processGep(const GepSVFGNode* edge)
{
    double start = stat->getClk();
    bool changed = false;

    NodeID gepId = edge->getId();
    const PointsTo& srcPts = getPts(edge->getPAGSrcNodeID());

    // Delta cache: stmtPtsCache[gepId] tracks which src objects have been processed.
    // Only iterate newly added objects via test_and_set (no temporary points-to diff set).
    assert(gepId < stmtPtsCache.size() && "stmtPtsCache must be pre-sized to SVFG node count");
    PointsTo& cachedSrcPts = stmtPtsCache[gepId];
    PointsTo tmpDstPts;
    const GepStmt* gepStmt = SVFUtil::cast<GepStmt>(edge->getPAGEdge());
    bool hasDeltaSrcPts = false;
    if (gepStmt->isVariantFieldGep())
    {
        for (NodeID o : srcPts)
        {
            if (!cachedSrcPts.test_and_set(o))
                continue;
            hasDeltaSrcPts = true;
            if (isBlkObjOrConstantObj(o))
            {
                tmpDstPts.set(o);
                continue;
            }
            setObjFieldInsensitive(o);
            tmpDstPts.set(getFIObjVar(o));
        }
    }
    else
    {
        for (NodeID o : srcPts)
        {
            if (!cachedSrcPts.test_and_set(o))
                continue;
            hasDeltaSrcPts = true;
            if (isBlkObjOrConstantObj(o) || isFieldInsensitive(o))
            {
                tmpDstPts.set(o);
                continue;
            }
            NodeID fieldSrcPtdNode = getGepObjVar(o, gepStmt->getAccessPath().getConstantStructFldIdx());
            tmpDstPts.set(fieldSrcPtdNode);
        }
    }
    if (!hasDeltaSrcPts)
    {
        double end = stat->getClk();
        gepTime += (end - start) / TIMEINTERVAL;
        return false;
    }

    if (unionPts(edge->getPAGDstNodeID(), tmpDstPts))
        changed = true;

    double end = stat->getClk();
    gepTime += (end - start) / TIMEINTERVAL;
    return changed;
}

void VersionedFlowSensitive::cluster(void)
{
    std::vector<std::pair<unsigned, unsigned>> keys;
    for (SVFIR::iterator pit = pag->begin(); pit != pag->end(); ++pit)
    {
        unsigned occ = 1;
        //ABTest
        unsigned v = pit->first;
        if (Options::PredictPtOcc() && pag->getBaseObject(v) != nullptr)
        {
            const StmtRelianceRefMap::const_iterator relIt = stmtRelianceRef.find(v);
            occ = (relIt == stmtRelianceRef.end() ? stmtReliance[v].size() : relIt->second->size()) + 1;
        }
        assert(occ != 0);
        keys.push_back(std::make_pair(v, occ));
    }

    PointsTo::MappingPtr nodeMapping =
        std::make_shared<std::vector<NodeID>>(NodeIDAllocator::Clusterer::cluster(ander, keys, candidateMappings, "aux-ander"));
    PointsTo::MappingPtr reverseNodeMapping =
        std::make_shared<std::vector<NodeID>>(NodeIDAllocator::Clusterer::getReverseNodeMapping(*nodeMapping));

    PointsTo::setCurrentBestNodeMapping(nodeMapping, reverseNodeMapping);
}

Version VersionedFlowSensitive::getVersion(const NodeID l, const NodeID o, const ObjToLocVersionMap &lvm) const
{
    // Fast path: maps for equivalent objects are already expanded/shared by pointer.
    const ObjToLocVersionMap::const_iterator oIt = lvm.find(o);
    if (oIt == lvm.end() || !oIt->second)
        return invalidVersion;

    const LocToVersionMap &lvmByObj = *(oIt->second);
    const LocToVersionMap::const_iterator foundVersion = lvmByObj.find(l);
    return foundVersion == lvmByObj.end() ? invalidVersion : foundVersion->second;
}

Version VersionedFlowSensitive::getConsume(const NodeID l, const NodeID o) const
{
    return getVersion(l, o, consume);
}

Version VersionedFlowSensitive::getYield(const NodeID l, const NodeID o) const
{
    // Non-store: consume == yield.
    if (isStore(l)) return getVersion(l, o, yield);
    else return getVersion(l, o, consume);
}

void VersionedFlowSensitive::setVersion(const NodeID l, const NodeID o, const Version v, ObjToLocVersionMap &lvm)
{
    // Canonical object owns storage; equivalent objects alias the same shared map.
    // This avoids materializing duplicate l->v maps for equivalent object classes.
    const NodeID canon = canonicalObject(o);
    LocToVersionMapPtr &canonMapPtr = lvm[canon];
    if (!canonMapPtr)
        canonMapPtr = std::make_shared<LocToVersionMap>();

    (*canonMapPtr)[l] = v;
    if (o != canon)
        lvm[o] = canonMapPtr;
}

void VersionedFlowSensitive::setConsume(const NodeID l, const NodeID o, const Version v)
{
    setVersion(l, o, v, consume);
}

void VersionedFlowSensitive::setYield(const NodeID l, const NodeID o, const Version v)
{
    // Non-store: consume == yield.
    if (isStore(l)) setVersion(l, o, v, yield);
    else setVersion(l, o, v, consume);
}

NodeBS &VersionedFlowSensitive::getStmtReliance(const NodeID o, const Version v)
{
    const StmtRelianceRefMap::const_iterator relIt = stmtRelianceRef.find(o);
    Map<Version, NodeBS> *relMap = relIt == stmtRelianceRef.end() ? &stmtReliance[o] : relIt->second;
    return (*relMap)[v];
}

void VersionedFlowSensitive::dumpReliances(void) const
{
    SVFUtil::outs() << "# Version reliances\n";
    for (const Map<NodeID, Map<Version, std::vector<Version>>>::value_type &ovrv : versionReliance)
    {
        NodeID o = ovrv.first;
        SVFUtil::outs() << "  Object " << o << "\n";
        for (const Map<Version, std::vector<Version>>::value_type& vrv : ovrv.second)
        {
            Version v = vrv.first;
            SVFUtil::outs() << "    Version " << v << " is a reliance for: ";

            bool first = true;
            for (Version rv : vrv.second)
            {
                if (!first)
                {
                    SVFUtil::outs() << ", ";
                }

                SVFUtil::outs() << rv;
                first = false;
            }

            SVFUtil::outs() << "\n";
        }
    }

    SVFUtil::outs() << "# Statement reliances\n";
    for (const Map<NodeID, Map<Version, NodeBS>>::value_type &ovss : stmtReliance)
    {
        NodeID o = ovss.first;
        SVFUtil::outs() << "  Object " << o << "\n";

        for (const Map<Version, NodeBS>::value_type &vss : ovss.second)
        {
            Version v = vss.first;
            SVFUtil::outs() << "    Version " << v << " is a reliance for statements: ";

            const NodeBS &ss = vss.second;
            bool first = true;
            for (NodeID s : ss)
            {
                if (!first)
                {
                    SVFUtil::outs() << ", ";
                }

                SVFUtil::outs() << s;
                first = false;
            }

            SVFUtil::outs() << "\n";
        }
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
    registerVDGSimplifyPass(passes, vdgSimplifySCCMerge);
    registerVDGSimplifyPass(passes, vdgSimplifyPrune);
    registerVDGSimplifyPass(passes, vdgSimplifyTransRedundancy);
    registerVDGSimplifyPass(passes, vdgSimplifyChainContraction);

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

void VersionedFlowSensitive::drawVersionDependencyGraph(const std::string& filename) const
{
    if (filename.empty())
        return;

    vdgManager.writeToFile(filename);
}

void VersionedFlowSensitive::dumpLocVersionMaps(void) const
{
    SVFUtil::outs() << "# LocVersion Maps\n";
    for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID loc = it->first;
        bool locPrinted = false;

        auto dumpAtLoc = [&](const bool useYield)
        {
            bool first = true;
            for (const Map<NodeID, NodeID>::value_type &kv : equivalentObject)
            {
                const NodeID o = kv.first;
                const Version v = useYield ? getYield(loc, o) : getConsume(loc, o);
                if (v == invalidVersion) continue;
                if (!locPrinted)
                {
                    SVFUtil::outs() << "  " << "SVFG node " << loc << "\n";
                    locPrinted = true;
                }
                if (first)
                {
                    SVFUtil::outs() << "    " << (useYield ? "Yield   " : "Consume ") << ": ";
                }
                SVFUtil::outs() << (first ? "" : ", ") << "<" << o << ", " << v << ">";
                first = false;
            }
            if (!first) SVFUtil::outs() << "\n";
        };

        dumpAtLoc(false);
        dumpAtLoc(true);
    }
}

void VersionedFlowSensitive::dumpMeldVersion(MeldVersion &v)
{
    SVFUtil::outs() << "[ ";
    bool first = true;
    for (unsigned e : v)
    {
        if (!first)
        {
            SVFUtil::outs() << ", ";
        }

        SVFUtil::outs() << e;
        first = false;
    }

    SVFUtil::outs() << " ]";
}

void VersionedFlowSensitive::readPtsFromFile(const std::string& filename)
{
    /// Initialization for the Solver
    initialize();
    /// Load the pts from file
    if(!filename.empty())
    {
        SVFUtil::outs() << "Loading versioned pointer analysis results from '" << filename << "'...";

        std::ifstream F(filename.c_str());
        if (!F.is_open())
        {
            SVFUtil::outs() << "  error opening file for reading!\n";
            return ;
        }
        readAndSetObjFieldSensitivity(F,"------");

        readVersionedAnalysisResultFromFile(F);

        readPtsResultFromFile(F);

        readGepObjVarMapFromFile(F);

        readAndSetObjFieldSensitivity(F,"");

        // Update callgraph
        updateCallGraph(pag->getIndirectCallsites());

        F.close();
        SVFUtil::outs() << "\n";
    }

    /// finalize the analysis
    finalize();
}

void VersionedFlowSensitive::solveAndwritePtsToFile(const std::string& filename)
{
    /// Initialization for the Solver
    initialize();
    if(!filename.empty())
        writeObjVarToFile(filename);
    solveConstraints();
    if(!filename.empty())
    {
        writeVersionedAnalysisResultToFile(filename);
        writeToFile(filename);
    }
    /// finalize the analysis
    finalize();
}

void VersionedFlowSensitive::writeVersionedAnalysisResultToFile(const std::string& filename)
{
    SVFUtil::outs() << "Storing Versioned Analysis Result to '" << filename << "'...";
    std::error_code err;
    std::fstream f(filename.c_str(), std::ios_base::app);
    if (!f.good())
    {
        SVFUtil::outs() << "  error opening file for writing!\n";
        return;
    }

    for (const VersionedFlowSensitive::ObjToLocVersionMap *lvm :
         {
             &this->consume, &this->yield
         })
    {
        for (const VersionedFlowSensitive::ObjToLocVersionMap::value_type &ovm : *lvm)
        {
            const NodeID o = ovm.first;
            if (!ovm.second) continue;
            for (const VersionedFlowSensitive::LocToVersionMap::value_type &lv : *(ovm.second))
            {
                const Version v = lv.second;
                if (vPtD->getPts(atKey(o, v)).empty()) continue;

                f <<"[ " <<o <<" " <<v<<" ]"<< " -> { ";
                const PointsTo &ovPts = vPtD->getPts(atKey(o, v));
                if (!ovPts.empty())
                {
                    for (NodeID n: ovPts)
                    {
                        f << n << " ";
                    }
                }
                else
                {
                    f << " ";
                }
                f << "}\n";
            }
        }
    }

    f << "---VERSIONED---\n";

    f.close();
    if (f.good())
    {
        SVFUtil::outs() << "\n";
        return;
    }
}

void VersionedFlowSensitive::readVersionedAnalysisResultFromFile(std::ifstream& F)
{
    std::string line;
    std::string delimiter1 = " -> { ";
    std::string delimiter2 = " }";
    while (F.good())
    {
        // Parse a single line in the form of "[ var version ] -> { obj1 obj2 obj3 }"
        getline(F, line);
        if (line == "---VERSIONED---")     break;
        std::string pair = line.substr(line.find("[ ")+1, line.find(" ]"));

        // Parse VersionKey
        std::istringstream ss(pair);
        NodeID nodeID;
        Version nodeVersion;
        ss>> nodeID >> nodeVersion;
        VersionedVar keyPair = atKey(nodeID,nodeVersion);

        // Parse Point-to set
        size_t pos = line.find(delimiter1);
        if (pos == std::string::npos)    break;
        if (line.back() != '}')     break;
        pos = pos + delimiter1.length();
        size_t len = line.length() - pos - delimiter2.length();
        std::string objs = line.substr(pos, len);
        PointsTo dstPts;
        if (!objs.empty())
        {
            std::istringstream pt(objs);
            NodeID obj;
            while (pt.good())
            {
                pt >> obj;
                dstPts.set(obj);
            }
        }

        // union point-to reuslt
        vPtD->unionPts(keyPair, dstPts);
    }

}

unsigned VersionedFlowSensitive::SCC::detectSCCs(VersionedFlowSensitive *vfs,
        const SVFG *svfg, const NodeID object,
        const std::vector<const SVFGNode *> &startingNodes,
        std::vector<int> &partOf,
        std::vector<const IndirectSVFGEdge *> &footprint)
{
    partOf.resize(svfg->getTotalNodeNum());
    std::fill(partOf.begin(), partOf.end(), -1);
    footprint.clear();

    std::vector<NodeData> nodeData(svfg->getTotalNodeNum(), { -1, -1, false});
    std::stack<const SVFGNode *> stack;

    int index = 0;
    int currentSCC = 0;

    for (const SVFGNode *v : startingNodes)
    {
        if (nodeData[v->getId()].index == -1)
        {
            visit(vfs, object, partOf, footprint, nodeData, stack, index, currentSCC, v);
        }
    }

    // Make sure footprints with the same edges pass ==/hash the same.
    std::sort(footprint.begin(), footprint.end());

    return currentSCC;
}

void VersionedFlowSensitive::SCC::visit(VersionedFlowSensitive *vfs,
                                        const NodeID object,
                                        std::vector<int> &partOf,
                                        std::vector<const IndirectSVFGEdge *> &footprint,
                                        std::vector<NodeData> &nodeData,
                                        std::stack<const SVFGNode *> &stack,
                                        int &index,
                                        int &currentSCC,
                                        const SVFGNode *v)
{
    const NodeID vId = v->getId();

    nodeData[vId].index = index;
    nodeData[vId].lowlink = index;
    ++index;

    stack.push(v);
    nodeData[vId].onStack = true;

    for (const SVFGEdge *e : v->getOutEdges())
    {
        const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(e);
        if (!ie) continue;

        const SVFGNode *w = ie->getDstNode();
        const NodeID wId = w->getId();

        // If object is not part of the edge, there is no edge from v to w.
        if (!ie->getPointsTo().test(object)) continue;

        // Even if we don't count edges to stores and deltas for SCCs' sake, they
        // are relevant to the footprint as a propagation still occurs over such edges.
        footprint.push_back(ie);

        // Ignore edges to delta nodes because they are prelabeled so cannot
        // be part of the SCC v is in (already in nodesTodo from the prelabeled set).
        // Similarly, store nodes.
        if (vfs->delta(wId) || vfs->isStore(wId)) continue;

        if (nodeData[wId].index == -1)
        {
            visit(vfs, object, partOf, footprint, nodeData, stack, index, currentSCC, w);
            nodeData[vId].lowlink = std::min(nodeData[vId].lowlink, nodeData[wId].lowlink);
        }
        else if (nodeData[wId].onStack)
        {
            nodeData[vId].lowlink = std::min(nodeData[vId].lowlink, nodeData[wId].index);
        }
    }

    if (nodeData[vId].lowlink == nodeData[vId].index)
    {
        const SVFGNode *w = nullptr;
        do
        {
            w = stack.top();
            stack.pop();
            const NodeID wId = w->getId();
            nodeData[wId].onStack = false;
            partOf[wId] = currentSCC;
        }
        while (w != v);

        // For the next SCC.
        ++currentSCC;
    }
}
