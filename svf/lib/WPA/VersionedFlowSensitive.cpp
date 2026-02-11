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
#include <queue>
#include <thread>
#include <mutex>

// Uncomment the following line to enable verbose debug logging for VFS solving
// #define VFS_DEBUG

#ifdef VFS_DEBUG
#define VFS_DEBUG_LOG(msg) do { SVFUtil::outs() << "[VFS-DBG] " << msg << "\n"; } while(0)
#else
#define VFS_DEBUG_LOG(msg) do {} while(0)
#endif

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

    // void vdgSimplifyPrune(VDG &graph)
    // {
    //     graph.pruneUnreachableToLoadConsume();
    //     graph.pruneUnreachableFromStoreYield();
    // }

    void vdgSimplifyStableReach(VDG &graph)
    {
        graph.reduceByStableDstReachability();
        graph.reduceByStableSrcReachability();
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
    // We'll grab vPtD in initialize.

    for (SVFIR::const_iterator it = pag->begin(); it != pag->end(); ++it)
    {
        if (SVFUtil::isa<ObjVar>(it->second)) equivalentObject[it->first] = it->first;
    }

    assert(!Options::OPTSVFG() && "VFS: -opt-svfg not currently supported with VFS.");
}

void VersionedFlowSensitive::initialize()
{
    FlowSensitive::initialize();
    // Overwrite the stat FlowSensitive::initialize gave us.
    delete stat;
    stat = new VersionedFlowSensitiveStat(this);

    vPtD = getVersionedPTDataTy();

    buildIsStoreLoadMaps();
    buildDeltaMaps();
    consume.resize(svfg->getTotalNodeNum());
    yield.resize(svfg->getTotalNodeNum());

    prelabel();
    meldLabel();
    expandEquivalentObjectVersions();
    buildVersionDependencyGraphs();
    if (Options::DumpVDG())
    {
        std::string outName = Options::VDGOutput();
        outName += "_init";
        vdgManager.writeToFile(outName);
    }
    if (Options::VDGStat())
        vdgManager.dumpStats();

    simplifyVDGGraphs();

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
                    // Same version and stmt reliance as the canonical. During solving we cannot just reuse
                    // the canonical object's reliance because it may change due to on-the-fly call graph
                    // construction. Something like copy-on-write could be good... probably negligible.
                    this->versionReliance.at(o) = this->versionReliance.at(canonOwner->second);
                    this->stmtReliance.at(o) = this->stmtReliance.at(canonOwner->second);
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

    delete[] versionMutexes;

    double end = stat->getClk(true);
    meldLabelingTime = (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::expandEquivalentObjectVersions(void)
{
    // 将规范对象的版本信息扩展到所有等价类成员

    // 收集需要扩展的对象映射：非规范对象 -> 规范对象
    std::vector<std::pair<NodeID, NodeID>> toExpand;
    for (const Map<NodeID, NodeID>::value_type &kv : equivalentObject)
    {
        const NodeID o = kv.first;
        const NodeID canonObj = kv.second;
        // 只处理非规范对象（o 映射到其他对象）
        if (o != canonObj)
        {
            toExpand.push_back(std::make_pair(o, canonObj));
        }
    }

    // 扩展 consume 映射
    for (NodeID l = 0; l < consume.size(); ++l)
    {
        ObjToVersionMap &consumeMap = consume[l];
        for (const std::pair<NodeID, NodeID> &oc : toExpand)
        {
            const NodeID o = oc.first;
            const NodeID canonObj = oc.second;
            // 查找规范对象的版本
            ObjToVersionMap::const_iterator canonIt = consumeMap.find(canonObj);
            if (canonIt != consumeMap.end())
            {
                // 将规范对象的版本复制给当前对象
                consumeMap[o] = canonIt->second;
            }
        }
    }

    // 扩展 yield 映射
    for (NodeID l = 0; l < yield.size(); ++l)
    {
        ObjToVersionMap &yieldMap = yield[l];
        for (const std::pair<NodeID, NodeID> &oc : toExpand)
        {
            const NodeID o = oc.first;
            const NodeID canonObj = oc.second;
            // 查找规范对象的版本
            ObjToVersionMap::const_iterator canonIt = yieldMap.find(canonObj);
            if (canonIt != yieldMap.end())
            {
                // 将规范对象的版本复制给当前对象
                yieldMap[o] = canonIt->second;
            }
        }
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
    bool changed = true;
#ifdef VFS_DEBUG
    unsigned solveIter = 0;
    unsigned long totalProcessed = 0;
#endif
    while (changed)
    {
        changed = false;
#ifdef VFS_DEBUG
        ++solveIter;
        unsigned iterProcessed = 0;
        VFS_DEBUG_LOG("=== solveWorklist iteration " << solveIter << " ===");
#endif
        
        // Process statement worklist until empty
        while (!isWorklistEmpty())
        {
            NodeID nodeId = popFromWorklist();
            processNode(nodeId);
            collapseFields();
#ifdef VFS_DEBUG
            ++iterProcessed;
            ++totalProcessed;
#endif
        }

#ifdef VFS_DEBUG
        VFS_DEBUG_LOG("  stmt worklist drained: processed " << iterProcessed << " nodes (total so far: " << totalProcessed << ")");
#endif
        
        // After stmt worklist is empty, do batch version propagation on all updated VDGs
        propagateAllVersions();
        
        // Check if any stmt was added back to worklist during propagation
        if (!isWorklistEmpty())
        {
            changed = true;
#ifdef VFS_DEBUG
            VFS_DEBUG_LOG("  worklist refilled after propagation, continuing...");
#endif
        }
    }
#ifdef VFS_DEBUG
    VFS_DEBUG_LOG("=== solveWorklist done: " << solveIter << " iterations, " << totalProcessed << " total nodes processed ===");
#endif
}

void VersionedFlowSensitive::propagateAllVersions()
{
    double start = stat->getClk();
    
#ifdef VFS_DEBUG
    unsigned vdgCount = 0;
#endif
    // Only process VDGs that have pending updates
    while (vdgManager.hasPendingVDGs())
    {
        const NodeID obj = vdgManager.popPendingVDG();
        VDG *graph = vdgManager.getVDG(obj);
        
        assert(graph->hasPendingUpdates() && "VFS::propagateAllVersions: pending VDG should have updates!");

#ifdef VFS_DEBUG
        ++vdgCount;
        unsigned propEdges = 0;
        unsigned changedEdges = 0;
        VFS_DEBUG_LOG("  propagate VDG obj=" << obj
                      << " nodes=" << graph->getTotalNodeNum()
                      << " edges=" << graph->getTotalEdgeNum()
                      << " updated=" << graph->getUpdatedNodes().size());
#endif
        
        // Define propagation callback: union pts from srcV to dstV
        auto propagateCallback = [this, obj
#ifdef VFS_DEBUG
            , &propEdges, &changedEdges
#endif
        ](Version srcV, Version dstV) -> bool
        {
#ifdef VFS_DEBUG
            ++propEdges;
#endif
            const VersionedVar srcVar = atKey(obj, srcV);
            const VersionedVar dstVar = atKey(obj, dstV);
            bool changed = vPtD->unionPts(dstVar, srcVar);
#ifdef VFS_DEBUG
            if (changed) ++changedEdges;
#endif
            return changed;
        };
        
        // Define stmt reliance callback: push related stmts to worklist
        // Must handle all sub versions since dynamic merging may occur
        auto stmtRelianceCallback = [this, obj, graph](Version v)
        {
            // v is a rep version, get all its sub versions (including itself)
            const VersionSet& subs = graph->getSubVersions(v);
            for (Version sub : subs)
            {
                for (NodeID s : getStmtReliance(obj, sub))
                {
                    pushIntoWorklist(s);
                }
            }
        };
        
        // Use VDG's propagation API
        graph->propagateInTopoOrder(propagateCallback, stmtRelianceCallback);

#ifdef VFS_DEBUG
        VFS_DEBUG_LOG("    propagated " << propEdges << " edges, " << changedEdges << " changed");
#endif
    }
    
#ifdef VFS_DEBUG
    if (vdgCount > 0)
        VFS_DEBUG_LOG("  propagateAllVersions: processed " << vdgCount << " VDGs");
#endif

    double end = stat->getClk();
    versionPropTime += (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::processNode(NodeID n)
{
    SVFGNode* sn = svfg->getSVFGNode(n);
#ifdef VFS_DEBUG
    const char* nodeType = "Unknown";
    if (SVFUtil::isa<AddrSVFGNode>(sn))         nodeType = "Addr";
    else if (SVFUtil::isa<CopySVFGNode>(sn))    nodeType = "Copy";
    else if (SVFUtil::isa<GepSVFGNode>(sn))     nodeType = "Gep";
    else if (SVFUtil::isa<LoadSVFGNode>(sn))    nodeType = "Load";
    else if (SVFUtil::isa<StoreSVFGNode>(sn))   nodeType = "Store";
    else if (SVFUtil::isa<PHISVFGNode>(sn))     nodeType = "Phi";
    else if (SVFUtil::isa<MSSAPHISVFGNode>(sn)) nodeType = "MSSAPhi";
    else if (SVFUtil::isa<FormalINSVFGNode>(sn))  nodeType = "FormalIn";
    else if (SVFUtil::isa<FormalOUTSVFGNode>(sn)) nodeType = "FormalOut";
    else if (SVFUtil::isa<ActualINSVFGNode>(sn))    nodeType = "ActualIn";
    else if (SVFUtil::isa<ActualOUTSVFGNode>(sn))  nodeType = "ActualOut";
    else if (SVFUtil::isa<FormalParmSVFGNode>(sn))  nodeType = "FormalParam";
    else if (SVFUtil::isa<ActualParmSVFGNode>(sn))  nodeType = "ActualParam";
    else if (SVFUtil::isa<FormalRetSVFGNode>(sn))   nodeType = "FormalRet";
    else if (SVFUtil::isa<ActualRetSVFGNode>(sn))   nodeType = "ActualRet";
    else if (SVFUtil::isa<NullPtrSVFGNode>(sn))     nodeType = "NullPtr";
    VFS_DEBUG_LOG("    processNode id=" << n << " type=" << nodeType);
#endif
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

                // 间接调用触发，加入依赖边
                VDG *graph = vdgManager.getVDG(o);
                if (graph)
                {
                    // Skip if either version was pruned during VDG simplification
                    if (!graph->hasVersion(srcY) || !graph->hasVersion(dstC)) continue;
                    // Use addEdge with version (auto-converts to rep)
                    if(graph->addEdge(srcY, dstC, VDGEdge::IndCallFlow, false)){
                        // Mark source as updated for batch propagation
                        vdgManager.markEdgeAdded(o, srcY);
                    }
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

#ifdef VFS_DEBUG
    const PointsTo& qptDbg = getPts(q);
    VFS_DEBUG_LOG("      Load l=" << l << " p=" << p << " q=" << q
                  << " |pts(q)|=" << qptDbg.count());
#endif

    const PointsTo& qpt = getPts(q);

    // p = *q, the type of p must be a pointer
    if (load->getPAGDstNode()->isPointer())
    {
        for (NodeID o : qpt)
        {
            if (pag->isConstantObj(o)) continue;

            const Version c = getConsume(l, o);
            if (c != invalidVersion){
                VDG* graph = vdgManager.getVDG(o);
                if (graph->hasVersion(c) && vPtD->unionPts(p, vdgManager.atRepKey(o, c)))
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
                    VDG* graph = vdgManager.getVDG(of);
                    if (graph->hasVersion(c) && vPtD->unionPts(p, vdgManager.atRepKey(of, c)))
                    {
                        changed = true;
                    }
                }
            }
        }
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

#ifdef VFS_DEBUG
    VFS_DEBUG_LOG("      Store l=" << l << " p=" << p << " q=" << q
                  << " |pts(p)|=" << ppt.count() << " |pts(q)|=" << qpt.count()
                  << " |consume|=" << consume[l].size());
#endif

    double start = stat->getClk();

    if (!qpt.empty())
    {
        // *p = q, the type of q must be a pointer
        if (store->getPAGSrcNode()->isPointer())
        {
            for (NodeID o : ppt)
            {
                if (pag->isConstantObj(o)) continue;

                const Version y = getYield(l, o);
                if (y == invalidVersion) continue;

                VDG* graph = vdgManager.getVDG(o);
                // Skip if version was pruned during VDG simplification
                if (!graph->hasVersion(y)) continue;

                if (vPtD->unionPts(vdgManager.atRepKey(o, y), q))
                {
                    // Notify statements that rely on this yield version and all its subs
                    const Version repY = graph->getRepVersion(y);
                    const VersionSet& subs = graph->getSubVersions(repY);
                    for (Version sub : subs)
                    {
                        for (NodeID s : getStmtReliance(o, sub))
                        {
                            pushIntoWorklist(s);
                        }
                    }

                    // Mark version as updated for batch propagation through VDG edges
                    vdgManager.markVersionUpdated(o, y);
                }
            }
        }
    }

    double end = stat->getClk();
    storeTime += (end - start) / TIMEINTERVAL;

    double updateStart = stat->getClk();

    NodeID singleton = 0;
    bool isSU = isStrongUpdate(store, singleton);
    if (isSU) svfgHasSU.set(l);
    else svfgHasSU.reset(l);

    // For all objects, perform pts(o:y) = pts(o:y) U pts(o:c) at loc,
    // except when a strong update is taking place.
    for (const ObjToVersionMap::value_type &oc : consume[l])
    {
        const NodeID o = oc.first;
        const Version c = oc.second;

        // Strong-updated; don't propagate.
        if (isSU && o == singleton) continue;

        const Version y = getYield(l, o);
        if (y != invalidVersion)
        {
            VDG *graph = vdgManager.getVDG(o);
            // Skip if either version was pruned during VDG simplification
            if (!graph->hasVersion(c) || !graph->hasVersion(y)) continue;
            // Use addEdge with version (auto-converts to rep)
            if(graph->addEdge(c, y, VDGEdge::StoreFlow, false)){
                // Mark source version as updated for batch propagation
                vdgManager.markEdgeAdded(o, c);
            }
        }
    }

    double updateEnd = stat->getClk();
    updateTime += (updateEnd - updateStart) / TIMEINTERVAL;

    return false;
}

void VersionedFlowSensitive::cluster(void)
{
    std::vector<std::pair<unsigned, unsigned>> keys;
    for (SVFIR::iterator pit = pag->begin(); pit != pag->end(); ++pit)
    {
        unsigned occ = 1;
        //ABTest
        unsigned v = pit->first;
        if (Options::PredictPtOcc() && pag->getBaseObject(v) != nullptr) occ = stmtReliance[v].size() + 1;
        assert(occ != 0);
        keys.push_back(std::make_pair(v, occ));
    }

    PointsTo::MappingPtr nodeMapping =
        std::make_shared<std::vector<NodeID>>(NodeIDAllocator::Clusterer::cluster(ander, keys, candidateMappings, "aux-ander"));
    PointsTo::MappingPtr reverseNodeMapping =
        std::make_shared<std::vector<NodeID>>(NodeIDAllocator::Clusterer::getReverseNodeMapping(*nodeMapping));

    PointsTo::setCurrentBestNodeMapping(nodeMapping, reverseNodeMapping);
}

Version VersionedFlowSensitive::getVersion(const NodeID l, const NodeID o, const LocVersionMap &lvm) const
{
    // const Map<NodeID, NodeID>::const_iterator canonObjectIt = equivalentObject.find(o);
    // const NodeID op = canonObjectIt == equivalentObject.end() ? o : canonObjectIt->second;
    // 经过 expandEquivalentObjectVersions() 扩展后，所有对象都有自己的版本条目无需再通过 equivalentObject 查找规范对象
    const ObjToVersionMap &ovm = lvm[l];
    // const ObjToVersionMap::const_iterator foundVersion = ovm.find(op);
    const ObjToVersionMap::const_iterator foundVersion = ovm.find(o);
    return foundVersion == ovm.end() ? invalidVersion : foundVersion->second;
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

void VersionedFlowSensitive::setVersion(const NodeID l, const NodeID o, const Version v, LocVersionMap &lvm)
{
    ObjToVersionMap &ovm = lvm[l];
    ovm[o] = v;
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
    return stmtReliance[o][v];
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

    auto getGraph = [&](const NodeID o) -> VDG&
    {
        return *vdgManager.getOrCreateVDG(o);
    };

    auto addVirtualIndCallEdge = [&](NodeID srcId, NodeID dstId)
    {
        const SVFGNode *srcNode = svfg->getSVFGNode(srcId);
        const SVFGNode *dstNode = svfg->getSVFGNode(dstId);
        const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
        const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dstNode);
        if (!srcMR || !dstMR) return;

        NodeBS cpts = srcMR->getPointsTo();
        if (!cpts.intersects(dstMR->getPointsTo())) return;
        cpts &= dstMR->getPointsTo();
        
        assert(delta(dstId) && "VFS::updateConnectedNodes: new edges should be to delta nodes!");
        assert(deltaSource(srcId) && "VFS::updateConnectedNodes: new indirect edges should be from delta source nodes!");

        for (const NodeID o : cpts)
        {
            const Version srcY = getYield(srcId, o);
            if (srcY == invalidVersion) continue;
            const Version dstC = getConsume(dstId, o);
            if (dstC == invalidVersion) continue;
            if (srcY == dstC) continue; // same version after meld, no edge needed
            VDG &graph = getGraph(o);
            graph.getOrAddNode(srcY, false, false);
            graph.getOrAddNode(dstC, false, false);
            graph.addEdge(srcY, dstC, VDGEdge::IndCallFlow, true);
        }
    };

    for (NodeID l = 0; l < consume.size(); ++l)
    {
        const ObjToVersionMap &consumeMap = consume[l];
        if (!consumeMap.empty())
        {
            // 对所有consume的version建立节点
            const bool loadConsume = isLoad(l);
            for (const ObjToVersionMap::value_type &ov : consumeMap)
            {
                const Version v = ov.second;
                if (v == invalidVersion) continue;
                VDG &graph = getGraph(ov.first);
                graph.getOrAddNode(v, loadConsume, false);
            }
        }

        const ObjToVersionMap &yieldMap = yield[l];
        if (!yieldMap.empty())
        {
            const bool storeYield = isStore(l);
            // 对所有yield的version建立节点
            for (const ObjToVersionMap::value_type &ov : yieldMap)
            {
                const Version v = ov.second;
                if (v == invalidVersion) continue;
                VDG &graph = getGraph(ov.first);
                graph.getOrAddNode(v, false, storeYield);
            }
        }

        if (isStore(l))
        {
            const StoreSVFGNode *store = SVFUtil::dyn_cast<StoreSVFGNode>(svfg->getSVFGNode(l));
            if (store == nullptr)
                continue;

            const NodeID p = store->getPAGDstNodeID();
            const PointsTo &dstPts = ander->getPts(p);
            if (dstPts.count() == 0)
                continue;

            const ObjToVersionMap &storeConsume = consumeMap;
            const ObjToVersionMap &storeYield = yieldMap;
            if (!storeConsume.empty() && !storeYield.empty())
            {
                for (const ObjToVersionMap::value_type &ov : storeConsume)
                {
                    const NodeID o = ov.first;
                    const bool nonSingletonObj = isNonSingletonObj(o);
                    const Version a = ov.second;
                    if (a == invalidVersion) continue;
                    const ObjToVersionMap::const_iterator yIt = storeYield.find(o);
                    if (yIt == storeYield.end()) continue;
                    const Version b = yIt->second;
                    if (b == invalidVersion) continue;
                    VDG &graph = getGraph(o);
                    // 版本一致无需建边
                    if (a == b)
                        continue;
                    graph.getOrAddNode(a, false, false);
                    const NodeID q = store->getPAGSrcNodeID();
                    const PointsTo &srcPts = ander->getPts(q);
                    if (srcPts.count() == 0)                  
                        graph.getOrAddNode(b, false, false);
                    else
                        graph.getOrAddNode(b, false, true);

                    if (nonSingletonObj)
                        graph.addEdge(a, b, VDGEdge::StoreFlow, false);
                    else
                        graph.addEdge(a, b, VDGEdge::StoreFlow, true);
                }
            }
        }
        // 处理 delta nodes 的 virtual edges
        // case: function entry node (formal-in)
        else if (const FunObjVar *fn = svfg->isFunEntrySVFGNode(svfg->getSVFGNode(l)))
        {
            if (svfg->hasFormalINSVFGNodes(fn))
            {
                const SVFG::FormalINSVFGNodeSet &formalIns = svfg->getFormalINSVFGNodes(fn);
                if (formalIns.test(l))
                {
                    CallGraphEdge::CallInstSet callsites;
                    ander->getCallGraph()->getIndCallSitesInvokingCallee(fn, callsites);
                    for (const CallICFGNode *cs : callsites)
                    {
                        if (!svfg->hasActualINSVFGNodes(cs)) continue;
                        const SVFG::ActualINSVFGNodeSet &actualIns = svfg->getActualINSVFGNodes(cs);
                        for (const NodeID srcId : actualIns)
                        {
                            addVirtualIndCallEdge(srcId, l);
                        }
                    }
                }
            }
        }
        // case: callsite return node (actual-out)
        else if (const CallICFGNode *cs = svfg->isCallSiteRetSVFGNode(svfg->getSVFGNode(l)))
        {
            if (cs->isIndirectCall() && svfg->hasActualOUTSVFGNodes(cs))
            {
                const SVFG::ActualOUTSVFGNodeSet &actualOuts = svfg->getActualOUTSVFGNodes(cs);
                if (actualOuts.test(l))
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
                            {
                                addVirtualIndCallEdge(srcId, l);
                            }
                        }
                    }
                }
            }
        }

    }
    // dumpReliances();

    for (const VersionRelianceMap::value_type &ovrv : versionReliance)
    {
        const NodeID o = ovrv.first;
        for (const Map<Version, std::vector<Version>>::value_type &vrv : ovrv.second)
        {
            const Version v = vrv.first;
            if (v == invalidVersion) continue;
            for (const Version rv : vrv.second)
            {
                if (rv == invalidVersion) continue;
                if (v == rv)
                {
                    continue;
                }
                VDG &graph = getGraph(o);
                graph.getOrAddNode(v, false, false);
                graph.getOrAddNode(rv, false, false);
                graph.addEdge(v, rv, VDGEdge::Depend, false);
            }
        }
    }

    double end = stat->getClk(true);
    vdgBuildTime = (end - start) / TIMEINTERVAL;
}

void VersionedFlowSensitive::simplifyVDGGraphs(void)
{
    double start = stat->getClk(true);
    std::vector<VDGSimplifyPass> passes;
    registerVDGSimplifyPass(passes, vdgSimplifySCCMerge);
    registerVDGSimplifyPass(passes, vdgSimplifyStableReach);
    registerVDGSimplifyPass(passes, vdgSimplifyTransRedundancy);
    registerVDGSimplifyPass(passes, vdgSimplifyChainContraction);

    for (VDGManager::VDGMapTy::value_type &entry : vdgManager.getAllVDGs())
    {
        if (!entry.second)
            continue;
        VDG &graph = *entry.second;
        for (VDGSimplifyPass pass : passes)
            pass(graph);
    }
    double end = stat->getClk(true);
    vdgSimplifyTime = (end - start) / TIMEINTERVAL;
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
    long unsigned int num = 0;
    for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        if(num >= consume.size()) {
            break;
        }
        const NodeID loc = it->first;
        bool locPrinted = false;
        for (const LocVersionMap *lvm :
                {
                    &consume, &yield
                })
        {
            if (lvm->at(loc).empty()) continue;
            if (!locPrinted)
            {
                SVFUtil::outs() << "  " << "SVFG node " << loc << "\n";
                locPrinted = true;
            }

            SVFUtil::outs() << "    " << (lvm == &consume ? "Consume " : "Yield   ") << ": ";

            bool first = true;
            for (const ObjToVersionMap::value_type &ov : lvm->at(loc))
            {
                const NodeID o = ov.first;
                const Version v = ov.second;
                SVFUtil::outs() << (first ? "" : ", ") << "<" << o << ", " << v << ">";
                first = false;
            }

            SVFUtil::outs() << "\n";
        }
        num++;
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

    for (const VersionedFlowSensitive::LocVersionMap *lvm :
            {
                &this->consume, &this->yield
            })
    {
        for (const VersionedFlowSensitive::ObjToVersionMap  &lov : *lvm)
        {
            for (const VersionedFlowSensitive::ObjToVersionMap::value_type &ov : lov)
            {
                const NodeID o = ov.first;
                const Version v = ov.second;
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
