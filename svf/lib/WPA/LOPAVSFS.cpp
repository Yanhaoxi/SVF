//===- LOPAVSFS.cpp -- LOPA frontend + VSFS-style propagation backend ------//
//
// VSFS object-version propagation over the shared LOPA offline frontend.
//
//===----------------------------------------------------------------------===//

#include "WPA/LOPAVSFS.h"
#include "WPA/WPAStat.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include "MemoryModel/PointsTo.h"

#include <algorithm>
#include <fstream>
#include <sstream>
#include <system_error>

using namespace SVF;
using namespace SVFUtil;

LOPAVSFS *LOPAVSFS::lopavsfs = nullptr;

LOPAVSFS::LOPAVSFS(SVFIR *_pag, PTATY type)
    : LOPAFrontend(_pag, type), versionedPTD(nullptr)
{
}

void LOPAVSFS::initialize()
{
    FlowSensitive::initialize();
    delete stat;
    stat = new LOPAVSFSStat(this);
    versionedPTD = getVersionedPTDataTy();
    initializeVDG();

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
    LOPAFrontend::finalize();
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

            // Stores preserve incoming contents in processStore, so they must
            // run again when their consumed version grows.
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
    // Use SVF's field-sensitive GEP transfer.
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

//===- Versioned result I/O -----------------------------------------------//

void LOPAVSFS::readPtsFromFile(const std::string& filename)
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

void LOPAVSFS::solveAndwritePtsToFile(const std::string& filename)
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

void LOPAVSFS::writeVersionedAnalysisResultToFile(const std::string& filename)
{
    SVFUtil::outs() << "Storing Versioned Analysis Result to '" << filename << "'...";
    std::error_code err;
    std::fstream f(filename.c_str(), std::ios_base::app);
    if (!f.good())
    {
        SVFUtil::outs() << "  error opening file for writing!\n";
        return;
    }

    for (const LOPAVSFS::ObjToLocVersionMap *lvm :
         {
             &this->consume, &this->yield
         })
    {
        for (const LOPAVSFS::ObjToLocVersionMap::value_type &ovm : *lvm)
        {
            const NodeID o = ovm.first;
            if (!ovm.second) continue;
            for (const LOPAVSFS::LocToVersionMap::value_type &lv : *(ovm.second))
            {
                const Version v = lv.second;
                if (versionedPTD->getPts(atKey(o, v)).empty()) continue;

                f <<"[ " <<o <<" " <<v<<" ]"<< " -> { ";
                const PointsTo &ovPts = versionedPTD->getPts(atKey(o, v));
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

void LOPAVSFS::readVersionedAnalysisResultFromFile(std::ifstream& F)
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
        versionedPTD->unionPts(keyPair, dstPts);
    }

}

//===- Statistics (original implementation: mbarbar, 2020) -----------------//

void LOPAVSFSStat::clearStat()
{
    _NumVersions         = 0;
    _MaxVersions         = 0;
    _NumNonEmptyVersions = 0;
    _NumSingleVersion    = 0;
    _NumUsedVersions     = 0;
    _NumEmptyVersions    = 0;
    _MaxPtsSize          = 0;
    _MaxTopLvlPtsSize    = 0;
    _MaxVersionPtsSize   = 0;
    _TotalPtsSize        = 0;
    _AvgPtsSize          = 0.0;
    _AvgTopLvlPtsSize    = 0.0;
    _AvgVersionPtsSize   = 0.0;
    // Equivalent-object statistics
    _NumEquivClasses     = 0;
    _TotalEquivObjs      = 0;
    _NumSingletonClasses = 0;
    _MaxEquivClassSize   = 0;
}

void LOPAVSFSStat::performStat()
{
    // Largely based on that in FlowSensitiveStat. Would be better to split the FSStat version
    // and reuse code rather than copy.
    assert(SVFUtil::isa<LOPAVSFS>(lopa) && "LOPAVSFSStat::performStat: not given LOPA.");
    endClk();

    clearStat();

    SVFIR *pag = lopa->getPAG();

    versionStat();
    ptsSizeStat();
    equivalentObjStat();

    u32_t fiObjNumber = 0;
    u32_t fsObjNumber = 0;
    Set<NodeID> nodeSet;
    for (SVFIR::const_iterator it = pag->begin(); it != pag->end(); ++it)
    {
        NodeID nodeId = it->first;
        PAGNode* pagNode = it->second;
        if (SVFUtil::isa<ObjVar>(pagNode))
        {
            const BaseObjVar* baseObj = pag->getBaseObject(nodeId);
            NodeID baseId = baseObj->getId();
            if (nodeSet.insert(baseId).second)
            {
                if (baseObj->isFieldInsensitive()) fiObjNumber++;
                else fsObjNumber++;
            }
        }
    }

    PTNumStatMap["FIObjNum"] = fiObjNumber;
    PTNumStatMap["FSObjNum"] = fsObjNumber;

    unsigned numOfCopy = 0;
    unsigned numOfStore = 0;
    for (SVFG::iterator it = lopa->svfg->begin(); it != lopa->svfg->end(); ++it)
    {
        SVFGNode* svfgNode = it->second;
        if (SVFUtil::isa<CopySVFGNode>(svfgNode)) numOfCopy++;
        else if (SVFUtil::isa<StoreSVFGNode>(svfgNode)) numOfStore++;
    }

    PTAStat::performStat();

    timeStatMap["TotalTime"]    = (endTime - startTime)/TIMEINTERVAL;
    timeStatMap["SolveTime"]          = lopa->solveTime;
    timeStatMap["SCCTime"]            = lopa->sccTime;
    timeStatMap["ProcessTime"]        = lopa->processTime;
    timeStatMap["PropagationTime"]    = lopa->propagationTime;
    timeStatMap["DirectPropaTime"]    = lopa->directPropaTime;
    timeStatMap["IndirectPropaTime"]  = lopa->indirectPropaTime;
    timeStatMap["Strong/WeakUpdTime"] = lopa->updateTime;
    timeStatMap["AddrTime"]           = lopa->addrTime;
    timeStatMap["CopyTime"]           = lopa->copyTime;
    timeStatMap["GepTime"]            = lopa->gepTime;
    timeStatMap["LoadTime"]           = lopa->loadTime;
    timeStatMap["StoreTime"]          = lopa->storeTime;
    timeStatMap["UpdateCGTime"]       = lopa->updateCallGraphTime;
    timeStatMap["PhiTime"]            = lopa->phiTime;
    timeStatMap["PrelabelingTime"]    = lopa->prelabelingTime;
    timeStatMap["VersionPropTime"]    = lopa->versionPropTime;
    timeStatMap["VDGBuildTime"]       = lopa->vdgBuildTime;

    PTNumStatMap["TotalPointers"]  = pag->getValueNodeNum();
    PTNumStatMap["TotalObjects"]   = pag->getObjectNodeNum();

    PTNumStatMap["Pointers"]         = pag->getValueNodeNum();
    PTNumStatMap["MemObjects"]       = pag->getObjectNodeNum();
    PTNumStatMap["DummyFieldPtrs"] = pag->getFieldValNodeNum();
    PTNumStatMap["FieldObjs"]  = pag->getFieldObjNodeNum();

    PTNumStatMap["TotalVersions"]     = _NumVersions;
    PTNumStatMap["MaxVersionsForObj"] = _MaxVersions;
    PTNumStatMap["TotalNonEmptyVPts"] = _NumNonEmptyVersions;
    PTNumStatMap["TotalEmptyVPts"]    = _NumEmptyVersions;
    PTNumStatMap["TotalExistingVPts"] = _NumUsedVersions;
    PTNumStatMap["TotalSingleVObjs"]  = _NumSingleVersion;

    PTNumStatMap["EquivObjClasses"]    = _NumEquivClasses;
    PTNumStatMap["TotalEquivObjs"]     = _TotalEquivObjs;
    PTNumStatMap["SingletonClasses"]   = _NumSingletonClasses;
    PTNumStatMap["MaxEquivClassSize"]  = _MaxEquivClassSize;

    PTNumStatMap["CopysNum"]  = numOfCopy;
    PTNumStatMap["StoresNum"] = numOfStore;

    PTNumStatMap["SolveIterations"] = lopa->numOfIteration;

    PTNumStatMap["IndEdgeSolved"] = lopa->getNumOfResolvedIndCallEdge();

    PTNumStatMap["StrongUpdates"] = lopa->svfgHasSU.count();
    PTNumStatMap["PrelabelNodes"] = lopa->numPrelabelNodes;
    PTNumStatMap["PrelabelFIObjs"] = lopa->numPrelabelFIObjs;

    PTNumStatMap["MaxPtsSize"]        = _MaxPtsSize;
    PTNumStatMap["MaxTopLvlPtsSize"]  = _MaxTopLvlPtsSize;
    PTNumStatMap["MaxVersionPtsSize"] = _MaxVersionPtsSize;

    timeStatMap["AvgPtsSize"]        = _AvgPtsSize;
    timeStatMap["AvgTopLvlPtsSize"]  = _AvgTopLvlPtsSize;
    timeStatMap["AvgVersionPtsSize"] = _AvgVersionPtsSize;

    PTNumStatMap["ProcessedAddr"]     = lopa->numOfProcessedAddr;
    PTNumStatMap["ProcessedCopy"]     = lopa->numOfProcessedCopy;
    PTNumStatMap["ProcessedGep"]      = lopa->numOfProcessedGep;
    PTNumStatMap["ProcessedLoad"]     = lopa->numOfProcessedLoad;
    PTNumStatMap["ProcessedStore"]    = lopa->numOfProcessedStore;
    PTNumStatMap["ProcessedPhi"]      = lopa->numOfProcessedPhi;
    PTNumStatMap["ProcessedAParam"]   = lopa->numOfProcessedActualParam;
    PTNumStatMap["ProcessedFRet"]     = lopa->numOfProcessedFormalRet;
    PTNumStatMap["ProcessedMSSANode"] = lopa->numOfProcessedMSSANode;

    PTNumStatMap["NumOfNodesInSCC"] = lopa->numOfNodesInSCC;
    PTNumStatMap["MaxSCCSize"]      = lopa->maxSCCSize;
    PTNumStatMap["NumOfSCC"]        = lopa->numOfSCC;
    timeStatMap["AverageSCCSize"]   = (lopa->numOfSCC == 0) ? 0 :
                                      ((double)lopa->numOfNodesInSCC / lopa->numOfSCC);

    PTAStat::printStat("Versioned Flow-Sensitive Pointer Analysis Statistics");
}

void LOPAVSFSStat::versionStat(void)
{
    // TODO! Need to merge yield/consume.
    _NumSingleVersion = 0;
    _MaxVersions = 0;

    // Build per-object unique-version cardinality across consume/yield maps.
    // This fixes MaxVersionsForObj (and TotalSingleVObjs) being stuck at 0.
    Set<NodeID> objects;
    for (const LOPAFrontend::ObjToLocVersionMap::value_type &ovm : lopa->consume)
        if (ovm.second) objects.insert(ovm.first);
    for (const LOPAFrontend::ObjToLocVersionMap::value_type &ovm : lopa->yield)
        if (ovm.second) objects.insert(ovm.first);

    for (const NodeID o : objects)
    {
        Set<Version> objVersions;

        const LOPAFrontend::ObjToLocVersionMap::const_iterator cIt = lopa->consume.find(o);
        if (cIt != lopa->consume.end() && cIt->second)
        {
            for (const LOPAFrontend::LocToVersionMap::value_type &lv : *(cIt->second))
            {
                if (lv.second != LOPAFrontend::invalidVersion)
                    objVersions.insert(lv.second);
            }
        }

        const LOPAFrontend::ObjToLocVersionMap::const_iterator yIt = lopa->yield.find(o);
        if (yIt != lopa->yield.end() && yIt->second)
        {
            for (const LOPAFrontend::LocToVersionMap::value_type &lv : *(yIt->second))
            {
                if (lv.second != LOPAFrontend::invalidVersion)
                    objVersions.insert(lv.second);
            }
        }

        const u32_t versionNum = static_cast<u32_t>(objVersions.size());
        if (versionNum > _MaxVersions)
            _MaxVersions = versionNum;
        if (versionNum == 1)
            ++_NumSingleVersion;
    }

    u32_t totalVersionPtsSize = 0;
    for (const LOPAFrontend::ObjToLocVersionMap *lvm :
            {
                &lopa->consume, &lopa->yield
            })
    {
        for (const LOPAFrontend::ObjToLocVersionMap::value_type &ovm : *lvm)
        {
            const NodeID o = ovm.first;
            if (!ovm.second) continue;
            for (const LOPAFrontend::LocToVersionMap::value_type &lv : *(ovm.second))
            {
                const Version v = lv.second;

                ++_NumVersions;

                // If the version was just over-approximate and never accessed, ignore.
                // Use a non-inserting query so absent versions do not materialize
                // empty points-to entries in the backing store.
                const PointsTo *ovPtsPtr = lopa->versionedPTD->getPtsIfExists(lopa->atKey(o, v));
                if (ovPtsPtr == nullptr || ovPtsPtr->empty()) continue;

                const PointsTo &ovPts = *ovPtsPtr;
                ++_NumNonEmptyVersions;

                const u32_t ovPtsCount = static_cast<u32_t>(ovPts.count());
                _TotalPtsSize += ovPtsCount;
                totalVersionPtsSize += ovPtsCount;
                if (ovPtsCount > _MaxVersionPtsSize) _MaxVersionPtsSize = ovPtsCount;
            }
        }
    }

    _NumUsedVersions = _NumNonEmptyVersions + _NumEmptyVersions;

    if (_NumNonEmptyVersions != 0) _AvgVersionPtsSize = (double)totalVersionPtsSize / (double)_NumUsedVersions;

    _TotalPtsSize += totalVersionPtsSize;
}

void LOPAVSFSStat::ptsSizeStat()
{
    u32_t totalValidTopLvlPointers = 0;
    u32_t totalTopLvlPtsSize = 0;
    for (SVFIR::iterator it = lopa->getPAG()->begin(); it != lopa->getPAG()->end(); ++it)
    {
        if (!lopa->getPAG()->isValidTopLevelPtr(it->second)) continue;

        NodeID p = it->first;

        totalValidTopLvlPointers++;

        u32_t size = lopa->getPts(p).count();
        totalTopLvlPtsSize += size;
        if (size > _MaxTopLvlPtsSize) _MaxTopLvlPtsSize = size;
    }

    if (totalValidTopLvlPointers != 0) _AvgTopLvlPtsSize = (double)totalTopLvlPtsSize / (double)totalValidTopLvlPointers;

    _TotalPtsSize += totalTopLvlPtsSize;

    if (_NumNonEmptyVersions + totalValidTopLvlPointers != 0)
    {
        _AvgPtsSize = (double)_TotalPtsSize / (double)(_NumNonEmptyVersions + totalValidTopLvlPointers);
    }

    _MaxPtsSize = _MaxVersionPtsSize > _MaxTopLvlPtsSize ? _MaxVersionPtsSize : _MaxTopLvlPtsSize;
}

void LOPAVSFSStat::equivalentObjStat(void)
{
    // Equivalent-object dedup is disabled: each materialized object is its own class.
    Set<NodeID> objects;
    for (const LOPAFrontend::ObjToLocVersionMap::value_type &ov : lopa->consume)
        objects.insert(ov.first);
    for (const LOPAFrontend::ObjToLocVersionMap::value_type &ov : lopa->yield)
        objects.insert(ov.first);

    const u32_t total = static_cast<u32_t>(objects.size());
    _TotalEquivObjs = total;
    _NumEquivClasses = total;
    _NumSingletonClasses = total;
    _MaxEquivClassSize = total == 0 ? 0 : 1;
}
