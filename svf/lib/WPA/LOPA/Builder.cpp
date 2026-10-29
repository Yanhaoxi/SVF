#include "WPA/LOPA.h"
#include "WPA/LOPAFrontend.h"
#include "Util/Options.h"

using namespace SVF;

LOPA::VersionNodes LOPA::createMemoryNodes(const VDG& graph) {
    VersionNodes versions(graph.capacity(), invalidNode);
    graph.forEachSuperNode([&](Version version, const VDGNode*) {
        versions[version] = newNode();
    });
    return versions;
}

NodeID LOPA::memoryVersionNode(const VDG& graph, const VersionNodes& versions, Version version) {
    return versions.at(graph.getRepVersion(version));
}

void LOPA::addMemoryCopies(const VDG& graph, const VersionNodes& versions) {
    graph.forEachSuperNode([&](Version source, const VDGNode* state) {
        for (Version target : state->getSolidOut())
            addCopy(memoryVersionNode(graph, versions, source), memoryVersionNode(graph, versions, target));
    });
}

void LOPA::bindMemoryStates(NodeID object, const VDG& graph, const VersionNodes& versions,
                           const Map<NodeID, Version>& consumes, const Map<NodeID, Version>& yields) {
    auto node = [&](Version version) { return memoryVersionNode(graph, versions, version); };
    auto publish = [&](NodeID location, NodeID id, bool output) {
        assert(id != invalidNode && "Only live memory versions are exported");
        memory.insert(memoryKey(location, object, output), id);
    };
    for (const auto& entry : consumes) {
        const NodeID in = node(entry.second);
        publish(entry.first, in, false);
        auto store = stores.find(entry.first);
        if (store != stores.end()) {
            const auto out = yields.find(entry.first);
            store->second.memory.push_back({object, in, out == yields.end() ? invalidNode : node(out->second)});
        }
    }
    for (const auto& entry : yields) {
        const NodeID out = node(entry.second);
        publish(entry.first, out, true);
        if (consumes.find(entry.first) == consumes.end())
            stores.at(entry.first).memory.push_back({object, invalidNode, out});
    }
}

void LOPA::importMemoryObject(NodeID object, const VDG& graph,
                              const Map<NodeID, Version>& consumes, const Map<NodeID, Version>& yields) {
    const bool profile = Options::LOPAProfile();
    const double start = stat->getClk(true);
    const auto versions = createMemoryNodes(graph);
    const double nodesReady = profile ? stat->getClk(true) : 0;
    addMemoryCopies(graph, versions);
    const double copiesReady = profile ? stat->getClk(true) : 0;
    bindMemoryStates(object, graph, versions, consumes, yields);
    const double end = stat->getClk(true);
    exportTime += (end - start) / TIMEINTERVAL;
    if (profile) {
        exportNodeTime += (nodesReady - start) / TIMEINTERVAL;
        exportCopyTime += (copiesReady - nodesReady) / TIMEINTERVAL;
        exportMapTime += (end - copiesReady) / TIMEINTERVAL;
    }
}

void LOPA::compileMemory() {
    for (const auto& entry : *svfg)
        if (const auto* store = SVFUtil::dyn_cast<StoreSVFGNode>(entry.second))
            stores[store->getId()].node = store;
    const double start = stat->getClk(true);
    LOPAFrontend::exportOffline(pag, svfg, ander, *this,
        [&](NodeID object, const VDG& graph, const LOPAFrontend::LocToVersionMap& consumes,
            const LOPAFrontend::LocToVersionMap& yields) {
            importMemoryObject(object, graph, consumes, yields);
        });
    offlineTime = (stat->getClk(true) - start) / TIMEINTERVAL - exportTime;
}

void LOPA::addPhi(const PHISVFGNode* phi) {
    const NodeID dst = valueNode(phi->getRes()->getId());
    for (auto it = phi->opVerBegin(); it != phi->opVerEnd(); ++it)
        addCopy(valueNode(it->second->getId()), dst);
}
void LOPA::addSVFGEdge(const SVFGEdge* edge) {
    const SVFGNode* src = edge->getSrcNode();
    const SVFGNode* dst = edge->getDstNode();
    if (const auto* indirect = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge)) {
        NodeBS objects = indirect->getPointsTo();
        for (NodeID object : indirect->getPointsTo())
            if (isFieldInsensitive(object)) objects |= getAllFieldsObjVars(object);
        for (NodeID object : objects)
            addCopy(memoryNode(src->getId(), object, SVFUtil::isa<StoreSVFGNode>(src)),
                    memoryNode(dst->getId(), object));
    } else if (const auto* actual = SVFUtil::dyn_cast<ActualParmSVFGNode>(src)) {
        const auto* formal = SVFUtil::cast<FormalParmSVFGNode>(dst);
        addCopy(valueNode(actual->getParam()->getId()), valueNode(formal->getParam()->getId()));
    } else if (const auto* formal = SVFUtil::dyn_cast<FormalRetSVFGNode>(src)) {
        const auto* actual = SVFUtil::cast<ActualRetSVFGNode>(dst);
        addCopy(valueNode(formal->getRet()->getId()), valueNode(actual->getRev()->getId()));
    }
}
LOPA::ConstraintGroup& LOPA::constraintsFor(NodeID source) {
    assert(parent[source] == source && groupHead[source] == groupTail[source]);
    if (groupHead[source] == invalidNode) {
        assert(constraintGroups.size() < invalidNode);
        groupHead[source] = groupTail[source] = constraintGroups.size();
        constraintGroups.emplace_back();
    }
    return constraintGroups[groupHead[source]];
}

void LOPA::registerValueConstraints(const SVFGNode* node) {
    if (const auto* addr = SVFUtil::dyn_cast<AddrSVFGNode>(node)) processAddr(addr);
    else if (const auto* copy = SVFUtil::dyn_cast<CopySVFGNode>(node))
        addCopy(valueNode(copy->getPAGSrcNodeID()), valueNode(copy->getPAGDstNodeID()));
    else if (const auto* phi = SVFUtil::dyn_cast<PHISVFGNode>(node)) addPhi(phi);
    else if (const auto* gep = SVFUtil::dyn_cast<GepSVFGNode>(node)) {
        const NodeID src = valueNode(gep->getPAGSrcNodeID());
        valueNode(gep->getPAGDstNodeID());
        constraintsFor(src).geps.push_back(gep);
    } else if (const auto* load = SVFUtil::dyn_cast<LoadSVFGNode>(node)) {
        const NodeID src = valueNode(load->getPAGSrcNodeID());
        valueNode(load->getPAGDstNodeID());
        constraintsFor(src).indirect.push_back(load);
    } else if (const auto* store = SVFUtil::dyn_cast<StoreSVFGNode>(node)) {
        const NodeID dst = valueNode(store->getPAGDstNodeID());
        valueNode(store->getPAGSrcNodeID());
        constraintsFor(dst).indirect.push_back(store);
    }
    for (const SVFGEdge* edge : node->getOutEdges())
        if (!SVFUtil::isa<IndirectSVFGEdge>(edge)) addSVFGEdge(edge);
}

void LOPA::compileValues() {
    for (const auto& entry : *svfg) registerValueConstraints(entry.second);
    // Addr seeds may precede registration of their GEP/Load/Store constraints.
    for (NodeID id : roots)
        if (groupHead[id] != invalidNode) constraintWork.set(id);
}
