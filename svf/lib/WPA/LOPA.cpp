#include "WPA/LOPA.h"
#include "Util/PTAStat.h"
#include "Util/Options.h"
#include <algorithm>
#include <cstdlib>

using namespace SVF;


NodeID LOPA::newNode() {
    assert(parent.size() < invalidNode);
    const NodeID id = parent.size();
    parent.push_back(id);
    copyDirty.push_back(false);
    groupHead.push_back(invalidNode);
    groupTail.push_back(invalidNode);
    [[maybe_unused]] const NodeID graphID = constraints->newNode();
    assert(graphID == id);
    return id;
}

NodeID LOPA::representative(NodeID id) {
    NodeID root = id;
    while (parent[root] != root) root = parent[root];
    while (parent[id] != id) {
        const NodeID next = parent[id];
        parent[id] = root;
        id = next;
    }
    return root;
}

NodeID LOPA::valueNode(NodeID value) {
    auto it = values.find(value);
    if (it != values.end()) return it->second;
    const NodeID id = newNode();
    values.emplace(value, id);
    return id;
}

NodeID LOPA::memoryNode(NodeID loc, NodeID object, bool output) const {
    // Pruned states have no observable consequence and must not be recreated.
    return memory.lookup(memoryKey(loc, object, output));
}

const PointsTo& LOPA::getPts(NodeID value) {
    if (exported) return BVDataPTAImpl::getPts(value);
    return points->getPts(representative(valueNode(value)));
}
bool LOPA::unionPts(NodeID value, const PointsTo& pts) {
    if (exported) return BVDataPTAImpl::unionPts(value, pts);
    return join(valueNode(value), pts);
}
bool LOPA::unionPts(NodeID value, NodeID source) {
    if (exported) return BVDataPTAImpl::unionPts(value, source);
    return join(valueNode(value), valueNode(source));
}
bool LOPA::addPts(NodeID value, NodeID object) {
    if (exported) return BVDataPTAImpl::addPts(value, object);
    const NodeID id = representative(valueNode(value));
    if (!points->addPts(id, object)) return false;
    changed(id);
    return true;
}

void LOPA::changed(NodeID id) {
    copyDirty[id] = true;
    if (groupHead[id] != invalidNode) constraintWork.set(id);
    // All Copy successors are already in this round's reachable subgraph.
    if (!copySolver.isPropagating()) roots.set(id);
}
bool LOPA::join(NodeID dst, NodeID src) {
    return joinRepresentatives(representative(dst), representative(src));
}
bool LOPA::joinRepresentatives(NodeID dst, NodeID src) {
    assert(parent[dst] == dst && parent[src] == src);
    ++copyUnions;
    if (!points->unionPts(dst, src)) return false;
    changed(dst);
    return true;
}
bool LOPA::join(NodeID dst, const PointsTo& pts) {
    dst = representative(dst);
    if (!points->unionPts(dst, pts)) return false;
    changed(dst);
    return true;
}
void LOPA::addCopy(NodeID src, NodeID dst) {
    ++copyAttempts;
    if (src == invalidNode || dst == invalidNode) { ++copyInvalid; return; }
    src = representative(src); dst = representative(dst);
    if (src == dst) { ++copySelf; return; }
    if (!constraints->addCopy(src, dst)) { ++copyDuplicates; return; }
    ++copyEdges;
    // New edges need old facts too. Propagate all outgoing edges together in
    // the next Copy round, even if only the graph structure has changed.
    copyDirty[src] = true;
    roots.set(src);
}

void LOPA::initialize() {
    if (!Options::UsePreCompFieldSensitive() || Options::OPTSVFG()) {
        SVFUtil::errs() << "LOPA requires the original field-sensitive SVFG.\n";
        std::exit(1);
    }
    FlowSensitive::initialize();
    delete stat;
    stat = createStat();
    // Same scope as LOPA+CG: construction through export/normalization, excluding
    // shared Andersen/MSSA/SVFG preparation and final statistics enumeration.
    stat->startClk();
    const double start = stat->getClk(true);
    constraints = std::make_unique<PUSConstraintGraph>();
    if (Options::ptDataBacking() == PTBackingType::Persistent)
        points = std::make_unique<PersDiffPTDataTy>(getPtCache(), false);
    else points = std::make_unique<MutDiffPTDataTy>(false);
    compileMemory();
    const double valuesStart = stat->getClk(true);
    compileValues();
    const double constructionEnd = stat->getClk(true);
    valueBuildTime = (constructionEnd - valuesStart) / TIMEINTERVAL;
    constructionTime = (constructionEnd - start) / TIMEINTERVAL;
    initialNodes = parent.size();
    initialCopies = constraints->copyCount();
}

void LOPA::transferGep(const GepSVFGNode* gep, const PointsTo& source) {
    const auto* statement = SVFUtil::cast<GepStmt>(gep->getPAGEdge());
    PointsTo targets;
    for (NodeID object : source) {
        if (isBlkObjOrConstantObj(object)) targets.set(object);
        else if (statement->isVariantFieldGep()) {
            // Andersen should already have marked this object FI. Record any
            // additional conversion without replaying all field constraints.
            if (!isFieldInsensitive(object)) {
                setObjFieldInsensitive(object);
                ++newFIObjects;
            }
            targets.set(getFIObjVar(object));
        } else if (isFieldInsensitive(object)) targets.set(object);
        else targets.set(getGepObjVar(object, statement->getAccessPath().getConstantStructFldIdx()));
    }
    unionPts(gep->getPAGDstNodeID(), targets);
}

void LOPA::processLoadTargets(const LoadSVFGNode* load, const PointsTo& newTargets) {
    if (!load->getPAGDstNode()->isPointer()) return;
    const NodeID dst = valueNode(load->getPAGDstNodeID());
    for (NodeID object : newTargets) {
        if (pag->isConstantObj(object)) continue;
        addCopy(memoryNode(load->getId(), object), dst);
        if (isFieldInsensitive(object))
            for (NodeID field : getAllFieldsObjVars(object))
                addCopy(memoryNode(load->getId(), field), dst);
    }
    ++numOfProcessedLoad;
}

void LOPA::addStoreWrites(const StoreSVFGNode* store, const PointsTo& newTargets) {
    if (!store->getPAGSrcNode()->isPointer()) return;
    for (NodeID object : newTargets)
        if (!pag->isConstantObj(object))
            addCopy(valueNode(store->getPAGSrcNodeID()), memoryNode(store->getId(), object, true));
}

void LOPA::addStoreBypasses(const StoreState& state) {
    for (const MemoryPair& pair : state.memory)
        if (!state.strong || pair.object != state.singleton) addCopy(pair.in, pair.out);
}

void LOPA::processStoreTargets(const StoreSVFGNode* store, const PointsTo& newTargets) {
    if (getPts(store->getPAGDstNodeID()).empty()) return;
    StoreState& state = stores.at(store->getId());
    const bool firstActivation = !state.active;
    const bool wasStrong = state.active && state.strong;
    state.active = true;
    state.strong = isStrongUpdate(store, state.singleton);
    if (wasStrong && !state.strong) ++strongToWeak;
    if (state.strong) svfgHasSU.set(store->getId());
    else svfgHasSU.reset(store->getId());
    addStoreWrites(store, newTargets);
    // Once weak, the bypasses remain valid as the target set grows.
    if (firstActivation || (wasStrong && !state.strong)) addStoreBypasses(state);
    ++numOfProcessedStore;
}

void LOPA::processIndirect(const SVFGNode* node, const PointsTo& newTargets) {
    if (const auto* load = SVFUtil::dyn_cast<LoadSVFGNode>(node))
        processLoadTargets(load, newTargets);
    else
        processStoreTargets(SVFUtil::cast<StoreSVFGNode>(node), newTargets);
}

void LOPA::processConstraintGroup(NodeID group, NodeID source) {
    if (!points->computeDiffPts(group, points->getPts(source))) return;
    const PointsTo& delta = points->getDiffPts(group);
    for (const auto* gep : constraintGroups[group].geps) transferGep(gep, delta);
    for (const auto* node : constraintGroups[group].indirect) processIndirect(node, delta);
}

void LOPA::mergeConstraintGroups(NodeID root, NodeID member) {
    const NodeID first = groupHead[member];
    if (first == invalidNode) return;
    if (groupHead[root] == invalidNode) groupHead[root] = first;
    else constraintGroups[groupTail[root]].nextGroup = first;
    groupTail[root] = groupTail[member];
    groupHead[member] = groupTail[member] = invalidNode;
}

void LOPA::coalesceConstraintGroups(NodeID source) {
    NodeID survivor = groupHead[source];
    if (survivor == invalidNode || groupTail[source] == survivor) return;
    auto& target = constraintGroups[survivor];
    const PointsTo empty;
    NodeID member = target.nextGroup;
    while (member != invalidNode) {
        // Callbacks may grow this source while groups are processed. Keep only
        // facts already processed by every constraint being combined.
        points->updatePropaPtsMap(member, survivor);
        auto& retired = constraintGroups[member];
        const NodeID next = retired.nextGroup;
        target.geps.insert(target.geps.end(), retired.geps.begin(), retired.geps.end());
        target.indirect.insert(target.indirect.end(), retired.indirect.begin(), retired.indirect.end());
        retired = ConstraintGroup{};
        // Group IDs and full-set node IDs belong to independent maps.
        points->computeDiffPts(member, empty);
        ++coalescedGroups;
        member = next;
    }
    target.nextGroup = invalidNode;
    groupTail[source] = survivor;
}

void LOPA::solveIndirect() {
    NodeBS work;
    std::swap(work, constraintWork);
    NodeBS canonical;
    for (NodeID id : work) canonical.set(representative(id));
    for (NodeID id : canonical) {
        for (NodeID group = groupHead[id]; group != invalidNode;
             group = constraintGroups[group].nextGroup)
            processConstraintGroup(group, id);
        coalesceConstraintGroups(id);
    }
    NodeBS reconsider;
    std::swap(reconsider, forcedStores);
    const PointsTo empty;
    for (NodeID id : reconsider) processIndirect(stores.at(id).node, empty);
}

void LOPA::updateConnectedNodes(const SVFGEdgeSetTy& edges) {
    for (const SVFGEdge* edge : edges) {
        addSVFGEdge(edge);
        if (const auto* phi = SVFUtil::dyn_cast<PHISVFGNode>(edge->getDstNode())) addPhi(phi);
    }
}

void LOPA::reconsiderStrongStores() {
    // A newly discovered recursive call can invalidate a stack strong update.
    for (const auto& store : stores)
        if (store.second.active && store.second.strong) forcedStores.set(store.first);
}

void LOPA::solveDataflow() {
    while (!roots.empty() || !constraintWork.empty() || !forcedStores.empty()) {
        ++rounds;
        if (!roots.empty()) copySolver.solve(*this);
        const double indirectStart = Options::LOPAProfile() ? stat->getClk(true) : 0;
        solveIndirect();
        if (Options::LOPAProfile()) indirectTime += (stat->getClk(true) - indirectStart) / TIMEINTERVAL;
    }
}

void LOPA::solveConstraints() {
    const bool timer = SVFUtil::startAnalysisLimitTimer(Options::FsTimeLimit());
    const double start = stat->getClk(true);
    bool callsChanged;
    do {
        ++numOfIteration;
        callGraphSCC->find();
        reconsiderStrongStores();
        solveDataflow();
        callsChanged = updateCallGraph(getIndirectCallsites());
    } while (callsChanged || !roots.empty() || !constraintWork.empty());
    solveTime = (stat->getClk(true) - start) / TIMEINTERVAL;
    SVFUtil::stopAnalysisLimitTimer(timer);
}

void LOPA::finalize() {
    for (const auto& value : values)
        getPTDataTy()->unionPts(value.first, points->getPts(representative(value.second)));
    exported = true;
    if (Options::DumpVFG()) svfg->dump("lopa_source_svfg", true);
    BVDataPTAImpl::finalize();
}
