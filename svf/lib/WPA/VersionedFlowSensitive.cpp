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
#include <cctype>
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
    stmtPtsCache.clear();
    stmtPtsCache.resize(svfg->getTotalNodeNum());

    prelabel();
    meldLabel();
    expandEquivalentObjectVersions();
    // Build VDGs in object-major streaming mode and simplify each graph in-place.
    buildVersionDependencyGraphs();
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
                // stmtReliance is load-only (set in meldLabel).
                // Clear the specific object bit so processLoad's delta includes it.
                assert((isLoad(s)) && "VFS::stmtRelianceCallback: unexpected stmt kind");
                assert(s < stmtPtsCache.size() && "stmtPtsCache must be pre-sized to SVFG node count");
                stmtPtsCache[s].reset(obj);
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
