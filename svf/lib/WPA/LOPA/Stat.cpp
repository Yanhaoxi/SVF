//===- Stat.cpp -- Statistics for LOPA -//

/*
 * Stat.cpp
 *
 *  Created on: 25/07/2020
 *      Author: mbarbar
 */

#include "Util/SVFUtil.h"
#include "WPA/WPAStat.h"
#include "WPA/LOPA.h"
#include "MemoryModel/PointsTo.h"

using namespace SVF;
using namespace SVFUtil;

void LOPAStat::clearStat()
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

void LOPAStat::performStat()
{
    // Largely based on that in FlowSensitiveStat. Would be better to split the FSStat version
    // and reuse code rather than copy.
    assert(SVFUtil::isa<LOPA>(lopa) && "LOPAStat::performStat: not given LOPA.");
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

void LOPAStat::versionStat(void)
{
    // TODO! Need to merge yield/consume.
    _NumSingleVersion = 0;
    _MaxVersions = 0;

    // Build per-object unique-version cardinality across consume/yield maps.
    // This fixes MaxVersionsForObj (and TotalSingleVObjs) being stuck at 0.
    Set<NodeID> objects;
    for (const LOPA::ObjToLocVersionMap::value_type &ovm : lopa->consume)
        if (ovm.second) objects.insert(ovm.first);
    for (const LOPA::ObjToLocVersionMap::value_type &ovm : lopa->yield)
        if (ovm.second) objects.insert(ovm.first);

    for (const NodeID o : objects)
    {
        Set<Version> objVersions;

        const LOPA::ObjToLocVersionMap::const_iterator cIt = lopa->consume.find(o);
        if (cIt != lopa->consume.end() && cIt->second)
        {
            for (const LOPA::LocToVersionMap::value_type &lv : *(cIt->second))
            {
                if (lv.second != LOPA::invalidVersion)
                    objVersions.insert(lv.second);
            }
        }

        const LOPA::ObjToLocVersionMap::const_iterator yIt = lopa->yield.find(o);
        if (yIt != lopa->yield.end() && yIt->second)
        {
            for (const LOPA::LocToVersionMap::value_type &lv : *(yIt->second))
            {
                if (lv.second != LOPA::invalidVersion)
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
    for (const LOPA::ObjToLocVersionMap *lvm :
            {
                &lopa->consume, &lopa->yield
            })
    {
        for (const LOPA::ObjToLocVersionMap::value_type &ovm : *lvm)
        {
            const NodeID o = ovm.first;
            if (!ovm.second) continue;
            for (const LOPA::LocToVersionMap::value_type &lv : *(ovm.second))
            {
                const Version v = lv.second;

                ++_NumVersions;

                // If the version was just over-approximate and never accessed, ignore.
                // Use a non-inserting query so absent versions do not materialize
                // empty points-to entries in the backing store.
                const PointsTo *ovPtsPtr = lopa->vPtD->getPtsIfExists(lopa->atKey(o, v));
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

void LOPAStat::ptsSizeStat()
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

void LOPAStat::equivalentObjStat(void)
{
    // Equivalent-object dedup is disabled: each materialized object is its own class.
    Set<NodeID> objects;
    for (const LOPA::ObjToLocVersionMap::value_type &ov : lopa->consume)
        objects.insert(ov.first);
    for (const LOPA::ObjToLocVersionMap::value_type &ov : lopa->yield)
        objects.insert(ov.first);

    const u32_t total = static_cast<u32_t>(objects.size());
    _TotalEquivObjs = total;
    _NumEquivClasses = total;
    _NumSingletonClasses = total;
    _MaxEquivClassSize = total == 0 ? 0 : 1;
}
