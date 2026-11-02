//===- Frontend.cpp -- load-observable versioned flow-sensitive pointer analysis --//

/*
 * LOPAFrontend.cpp
 *
 *  Created on: Jun 26, 2020
 *      Author: Mohamad Barbar
 */

#include "Util/GeneralType.h"
#include "WPA/Andersen.h"
#include "WPA/LOPAFrontend.h"
#include "Util/Options.h"
#include <algorithm>
#include <cassert>

using namespace SVF;

const Version LOPAFrontend::invalidVersion = 0;

VersionedVar LOPAFrontend::atKey(NodeID var, Version version)
{
    assert(version != invalidVersion && "LOPAFrontend::atKey: trying to use an invalid version!");
    return std::make_pair(var, version);
}

LOPAFrontend::LOPAFrontend(SVFIR *_pag, PTATY type)
    : FlowSensitive(_pag, type)
{
    assert(!Options::OPTSVFG() && "LOPAFrontend: -opt-svfg not currently supported with LOPAFrontend.");
}

void LOPAFrontend::initializeVDG()
{
    VDG::setSolvePhaseStarted(false);
    buildIsStoreLoadMaps();
    buildDeltaMaps();
    prelabel();
    // Build VDGs in object-major streaming mode (includes simplify + stmt-reliance bind).
    buildVDG();

    if (Options::DumpVDG())
    {
        std::string outName = Options::VDGOutput();
        outName += "_simplified";
        vdgManager.writeToFile(outName);
    }
    if (Options::VDGStat()){
        vdgManager.dumpStats();
    }

    // Switch all VDGs to solve stage once build/simplify/materialization is done.
    vdgManager.enterSolveAll();

    removeAllIndirectSVFGEdges();
}

void LOPAFrontend::exportOffline(SVFIR* pag, SVFG* graph, AndersenWaveDiff* preanalysis,
                         const PointerAnalysis& analysis, const OfflineConsumer& consumeObject)
{
    LOPAFrontend frontend(pag);
    frontend.buildOffline(graph, preanalysis, analysis, consumeObject);
}

void LOPAFrontend::buildOffline(SVFG* graph, AndersenWaveDiff* preanalysis,
                         const PointerAnalysis& analysis, const OfflineConsumer& consumeObject)
{
    assert(stat == nullptr && callgraph == nullptr && callGraphSCC == nullptr);
    svfg = graph;
    ander = preanalysis;
    callgraph = analysis.getCallGraph();
    callGraphSCC = analysis.getCallGraphSCC();
    offlineConsumer = &consumeObject;
    // The graphs and consumer belong to the caller, including on an exceptional exit.
    struct BorrowedGraphs {
        CallGraph*& graph;
        CallGraphSCC*& scc;
        const OfflineConsumer*& consumer;
        ~BorrowedGraphs() { graph = nullptr; scc = nullptr; consumer = nullptr; }
    } borrowed{callgraph, callGraphSCC, offlineConsumer};
    stat = new PTAStat(this);
    stat->startClk();
    VDG::setSolvePhaseStarted(false);
    buildIsStoreLoadMaps();
    buildDeltaMaps();
    prelabel();
    buildVDG();
    assert(vdgManager.getAllVDGs().empty() && consume.empty() && yield.empty()
           && "Offline graphs must be consumed during construction");
}

void LOPAFrontend::finalize()
{
    FlowSensitive::finalize();
    if (Options::DumpVDG())
    {
        std::string outName = Options::VDGOutput();
        outName += "_final";
        vdgManager.writeToFile(outName);
    }
    if (Options::VDGStat())
        vdgManager.dumpStats();
}

bool LOPAFrontend::delta(const NodeID l) const
{
    assert(l < deltaMap.size() && "LOPAFrontend::delta: deltaMap is missing SVFG nodes!");
    return deltaMap[l];
}

bool LOPAFrontend::deltaSource(const NodeID l) const
{
    assert(l < deltaSourceMap.size() && "LOPAFrontend::delta: deltaSourceMap is missing SVFG nodes!");
    return deltaSourceMap[l];
}

bool LOPAFrontend::isStore(const NodeID l) const
{
    assert(l < isStoreMap.size() && "LOPAFrontend::isStore: isStoreMap is missing SVFG nodes!");
    return isStoreMap[l];
}

bool LOPAFrontend::isLoad(const NodeID l) const
{
    assert(l < isLoadMap.size() && "LOPAFrontend::isLoad: isLoadMap is missing SVFG nodes!");
    return isLoadMap[l];
}

void LOPAFrontend::buildIsStoreLoadMaps(void)
{
    isStoreMap.resize(svfg->getTotalNodeNum(), false);
    isLoadMap.resize(svfg->getTotalNodeNum(), false);
    for (SVFG::const_iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        if (SVFUtil::isa<StoreSVFGNode>(it->second)) isStoreMap[it->first] = true;
        else if (SVFUtil::isa<LoadSVFGNode>(it->second)) isLoadMap[it->first] = true;
    }
}

void LOPAFrontend::buildDeltaMaps(void)
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

void LOPAFrontend::removeAllIndirectSVFGEdges(void)
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

void LOPAFrontend::cluster(void)
{
    std::vector<std::pair<unsigned, unsigned>> keys;
    for (SVFIR::iterator pit = pag->begin(); pit != pag->end(); ++pit)
    {
        unsigned occ = 1;
        //ABTest
        unsigned v = pit->first;
        if (Options::PredictPtOcc() && pag->getBaseObject(v) != nullptr)
        {
            const auto relIt = stmtReliance.find(v);
            occ = (relIt == stmtReliance.end() ? 0 : relIt->second.size()) + 1;
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

void LOPAFrontend::setVersion(const NodeID l, const NodeID o, const Version v, ObjToLocVersionMap &lvm)
{
    LocToVersionMapPtr &objMapPtr = lvm[o];
    if (!objMapPtr)
        objMapPtr = std::make_shared<LocToVersionMap>();

    (*objMapPtr)[l] = v;
}

void LOPAFrontend::setConsume(const NodeID l, const NodeID o, const Version v)
{
    setVersion(l, o, v, consume);
}

void LOPAFrontend::setYield(const NodeID l, const NodeID o, const Version v)
{
    // Non-store: consume == yield.
    if (isStore(l)) setVersion(l, o, v, yield);
    else setVersion(l, o, v, consume);
}

NodeBS &LOPAFrontend::getStmtReliance(const NodeID o, const Version v)
{
    return stmtReliance[o][v];
}
