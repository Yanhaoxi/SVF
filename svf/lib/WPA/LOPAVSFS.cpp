//===- LOPAVSFS.cpp -- LOPA frontend + VSFS-style propagation backend ------//
//
// Ablation variant "B". It reuses LOPA's offline compression frontend and
// replaces the solver with the VSFS object-version propagation algorithm.
// The propagation half is a faithful port of VersionedFlowSensitive's solver
// (see code/svf/svf/lib/WPA/VersionedFlowSensitive.cpp).
//
//===----------------------------------------------------------------------===//

#include "WPA/LOPAVSFS.h"
#include "Util/Options.h"

#include <algorithm>

using namespace SVF;
using namespace SVFUtil;

LOPAVSFS *LOPAVSFS::lopavsfs = nullptr;

LOPAVSFS::LOPAVSFS(SVFIR *_pag, PTATY type)
    : LOPA(_pag, type), versionedPTD(nullptr)
{
}

void LOPAVSFS::initialize()
{
    // Run LOPA's frontend exactly as-is: prelabel + buildVDG (construction,
    // offline compression, shrink/publish of consume/yield and stmt reliance),
    // enterSolveAll and removeAllIndirectSVFGEdges.
    LOPA::initialize();

    versionedPTD = getVersionedPTDataTy();

    const double translateStart = stat->getClk(true);
    buildVFSStructures();
    const double translateEnd = stat->getClk(true);

    if (Options::VDGStat())
    {
        size_t reliantNodes = 0, relianceEdges = 0, consumeEntries = 0;
        for (const auto &oc : versionReliance)
            for (const auto &vv : oc.second)
            {
                ++reliantNodes;
                relianceEdges += vv.second.size();
            }
        for (const auto &m : vfsConsume)
            consumeEntries += m.size();
        SVFUtil::outs() << "LOPAVSFS.translate\ttime:" << (translateEnd - translateStart) / TIMEINTERVAL
                        << " objects:" << versionReliance.size()
                        << " reliantNodes:" << reliantNodes
                        << " relianceEdges:" << relianceEdges
                        << " consumeEntries:" << consumeEntries << "\n";
    }
}

void LOPAVSFS::finalize()
{
    LOPA::finalize();
}

/*!
 * Translate the materialized LOPA frontend into VSFS propagation structures.
 *
 *  - versionReliance: LOPA VDG solid edges u->v become reliance u -> v.
 *  - stmtReliance: the per-node load reliance bound in buildVDG.
 *  - vfsConsume/vfsYield: location-major copies of consume/yield (l -> {o -> v}),
 *    used by processLoad/processStore to materialize preservation dynamically.
 */
void LOPAVSFS::buildVFSStructures()
{
    versionReliance.clear();
    versionedVarToPropNode.clear();
    vfsConsume.clear();
    vfsYield.clear();

    for (const NodeID o : prelabeledObjects)
    {
        VDG *g = vdgManager.tryGetVDG(o);
        if (g == nullptr)
            continue;

        g->forEachSuperNode([&](Version v, VDGNode *node)
        {
            const Version rv = g->getRepVersion(v);

            // The published solid adjacency is already deduplicated and holds
            // representative versions, so we can reserve once and copy directly
            // instead of an O(d^2) std::find per inserted edge.
            const VDGNode::AdjSet &solidOut = node->getSolidOut();
            if (!solidOut.empty())
            {
                std::vector<Version> &rel = versionReliance[o][rv];
                rel.reserve(solidOut.size());
                for (const Version d : solidOut)
                {
                    const Version rd = g->getRepVersion(d);
                    if (rd != rv)
                        rel.push_back(rd);
                }
            }

            const NodeBS &stmts = node->getStmtRelianceSet();
            if (!stmts.empty())
                stmtReliance[o][rv] |= stmts;
        });
    }

    // Build location-major consume/yield maps, mirroring VersionedFlowSensitive's
    // LocVersionMap layout so the hot solving path uses a single indexed lookup.
    const NodeID numNodes = svfg->getTotalNodeNum();
    vfsConsume.resize(numNodes);
    vfsYield.resize(numNodes);

    for (const auto &oc : consume)
    {
        const NodeID o = oc.first;
        const LocToVersionMapPtr &lvm = oc.second;
        if (!lvm)
            continue;
        for (const auto &lv : *lvm)
        {
            const NodeID l = lv.first;
            if (l < numNodes)
                vfsConsume[l][o] = lv.second;

            // VSFS notifies both loads and stores when the consumed version of an
            // object grows; LOPA's graph reliance is load-only because its own
            // solver propagates preservation through VDG edges. This backend
            // materializes preservation dynamically in processStore, so a store
            // must be re-run when its consume version changes; register it here.
            if (isStore(l) && lv.second != invalidVersion)
                stmtReliance[o][lv.second].set(l);
        }
    }
    for (const auto &oc : yield)
    {
        const NodeID o = oc.first;
        const LocToVersionMapPtr &lvm = oc.second;
        if (!lvm)
            continue;
        for (const auto &lv : *lvm)
        {
            const NodeID l = lv.first;
            if (l < numNodes)
                vfsYield[l][o] = lv.second;
        }
    }
}

void LOPAVSFS::pushIntoWorklist(NodeID id)
{
    worklist.push(sccRepNode(id));
}

void LOPAVSFS::solveWorklist()
{
    while (!worklist.empty())
    {
        NodeID nodeId = worklist.pop();
        processNode(nodeId);
    }
}

void LOPAVSFS::solveConstraints()
{
    bool limitTimerSet = SVFUtil::startAnalysisLimitTimer(Options::FsTimeLimit());

    double start = stat->getClk(true);
    do
    {
        numOfIteration++;

        if (0 == numOfIteration % OnTheFlyIterBudgetForStat)
            dumpStat();

        callGraphSCC->find();

        // VSFS re-seeds the whole worklist each call-graph round.
        initWorklist();
        solveWorklist();
    }
    while (updateCallGraph(getIndirectCallsites()));

    SVFUtil::stopAnalysisLimitTimer(limitTimerSet);

    double end = stat->getClk(true);
    solveTime += (end - start) / TIMEINTERVAL;
}

void LOPAVSFS::processNode(NodeID n)
{
    SVFGNode *sn = svfg->getSVFGNode(n);
    if (const DummyVersionPropSVFGNode *dvp = SVFUtil::dyn_cast<DummyVersionPropSVFGNode>(sn))
    {
        propagateVersion(dvp->getObject(), dvp->getVersion());
    }
    else if (processSVFGNode(sn))
    {
        propagate(&sn);
    }
}

bool LOPAVSFS::processGep(const GepSVFGNode* edge)
{
    // VSFS uses the base flow-sensitive gep handling; LOPA's delta-cache path
    // is not part of this backend.
    return FlowSensitive::processGep(edge);
}

void LOPAVSFS::propagateVersion(NodeID o, Version v)
{
    double start = stat->getClk();

    const std::vector<Version> &reliantVersions = getReliantVersions(o, v);
    for (Version r : reliantVersions)
        propagateVersion(o, v, r, false);

    double end = stat->getClk();
    versionPropTime += (end - start) / TIMEINTERVAL;
}

void LOPAVSFS::propagateVersion(const NodeID o, const Version v, const Version vp, bool time)
{
    double start = time ? stat->getClk() : 0.0;

    const VersionedVar srcVar = atKey(o, v);
    const VersionedVar dstVar = atKey(o, vp);
    if (versionedPTD->unionPts(dstVar, srcVar))
    {
        const DummyVersionPropSVFGNode *dvp = nullptr;
        VarToPropNodeMap::const_iterator dvpIt = versionedVarToPropNode.find(dstVar);
        if (dvpIt == versionedVarToPropNode.end())
        {
            dvp = svfg->addDummyVersionPropSVFGNode(o, vp);
            versionedVarToPropNode[dstVar] = dvp;
        }
        else
            dvp = dvpIt->second;

        assert(dvp != nullptr && "LOPAVSFS::propagateVersion: propagation dummy node not found?");
        pushIntoWorklist(dvp->getId());

        for (NodeID s : getStmtReliance(o, vp))
            pushIntoWorklist(s);
    }

    double end = time ? stat->getClk() : 0.0;
    if (time) versionPropTime += (end - start) / TIMEINTERVAL;
}

/*!
 * Process load node: p = *q reads each consumed version of the objects q may
 * point to. Faithful port of VersionedFlowSensitive::processLoad.
 */
bool LOPAVSFS::processLoad(const LoadSVFGNode* load)
{
    double start = stat->getClk();
    bool changed = false;

    NodeID l = load->getId();
    NodeID p = load->getPAGDstNodeID();
    NodeID q = load->getPAGSrcNodeID();

    const PointsTo& qpt = getPts(q);
    if (load->getPAGDstNode()->isPointer())
    {
        for (NodeID o : qpt)
        {
            if (pag->isConstantObj(o))
                continue;

            const Version c = getConsumeV(l, o);
            if (c != invalidVersion && versionedPTD->unionPts(p, atKey(o, c)))
                changed = true;

            if (isFieldInsensitive(o))
            {
                const NodeBS& fields = getAllFieldsObjVars(o);
                for (NodeID of : fields)
                {
                    const Version cf = getConsumeV(l, of);
                    if (cf != invalidVersion && versionedPTD->unionPts(p, atKey(of, cf)))
                        changed = true;
                }
            }
        }
    }

    double end = stat->getClk();
    loadTime += (end - start) / TIMEINTERVAL;
    return changed;
}

/*!
 * Process store node: l: *p = q. Writes q into the yielded version of every
 * object p may point to, then materializes consume->yield preservation for all
 * objects with a consume version at l (skipping the strong-update singleton).
 * Faithful port of VersionedFlowSensitive::processStore.
 */
bool LOPAVSFS::processStore(const StoreSVFGNode* store)
{
    NodeID p = store->getPAGDstNodeID();
    const PointsTo &ppt = getPts(p);
    if (ppt.empty())
        return false;

    NodeID q = store->getPAGSrcNodeID();
    const PointsTo &qpt = getPts(q);
    NodeID l = store->getId();

    double start = stat->getClk();
    bool changed = false;
    NodeBS changedObjects;

    if (!qpt.empty())
    {
        if (store->getPAGSrcNode()->isPointer())
        {
            for (NodeID o : ppt)
            {
                if (pag->isConstantObj(o))
                    continue;

                const Version y = getYieldV(l, o);
                if (y != invalidVersion && versionedPTD->unionPts(atKey(o, y), q))
                {
                    changed = true;
                    changedObjects.set(o);
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

    // Preserve incoming contents for every object with a consume version at l,
    // except the strongly updated singleton.
    if (l < vfsConsume.size())
    {
        for (const auto &oc : vfsConsume[l])
        {
            const NodeID o = oc.first;
            if (isSU && o == singleton)
                continue;

            const Version c = oc.second;
            if (c == invalidVersion)
                continue;
            const Version y = getYieldV(l, o);
            if (y != invalidVersion && versionedPTD->unionPts(atKey(o, y), atKey(o, c)))
            {
                changed = true;
                changedObjects.set(o);
            }
        }
    }

    double updateEnd = stat->getClk();
    updateTime += (updateEnd - updateStart) / TIMEINTERVAL;

    if (!changedObjects.empty())
    {
        for (const NodeID o : changedObjects)
        {
            const Version y = getYieldV(l, o);
            if (y == invalidVersion)
                continue;
            propagateVersion(o, y);
            for (NodeID s : getStmtReliance(o, y))
                pushIntoWorklist(s);
        }
    }

    return changed;
}

/*!
 * New indirect edges discovered during on-the-fly call-graph construction.
 * Faithful port of VersionedFlowSensitive::updateConnectedNodes.
 */
void LOPAVSFS::updateConnectedNodes(const SVFGEdgeSetTy& newEdges)
{
    for (const SVFGEdge *e : newEdges)
    {
        SVFGNode *dstNode = e->getDstNode();
        NodeID src = e->getSrcNode()->getId();
        NodeID dst = dstNode->getId();

        if (SVFUtil::isa<PHISVFGNode>(dstNode)
                || SVFUtil::isa<FormalParmSVFGNode>(dstNode)
                || SVFUtil::isa<ActualRetSVFGNode>(dstNode))
        {
            pushIntoWorklist(dst);
        }
        else
        {
            const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(e);
            assert(ie != nullptr && "LOPAVSFS::updateConnectedNodes: given direct edge?");

            assert(delta(dst) && "LOPAVSFS::updateConnectedNodes: new edges should be to delta nodes!");
            assert(deltaSource(src) && "LOPAVSFS::updateConnectedNodes: new indirect edges should be from delta source nodes!");

            const NodeBS &ept = ie->getPointsTo();
            for (const NodeID o : ept)
            {
                Version srcY = getYieldV(src, o);
                if (srcY == invalidVersion)
                    continue;
                Version dstC = getConsumeV(dst, o);
                if (dstC == invalidVersion)
                    continue;

                std::vector<Version> &versionsRelyingOnSrcY = getReliantVersions(o, srcY);
                if (std::find(versionsRelyingOnSrcY.begin(), versionsRelyingOnSrcY.end(), dstC)
                        == versionsRelyingOnSrcY.end())
                {
                    versionsRelyingOnSrcY.push_back(dstC);
                    propagateVersion(o, srcY, dstC);
                }
            }
        }
    }
}
