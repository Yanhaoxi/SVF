#include "WPA/FlowSensitiveCG.h"
#include "WPA/Andersen.h"
#include "WPA/WPAStat.h"
#include "WPA/LOPA.h"
#include <algorithm>
#include <cstdlib>
#include <limits>
using namespace SVF;

namespace SVF {
/// Report the constraint graph directly; SFS's DF-IN/OUT maps are not used.
class FlowSensitiveCGStat : public PTAStat {
public:
    explicit FlowSensitiveCGStat(FlowSensitiveCG* analysis) : PTAStat(analysis), cg(analysis) {}
    void performStat() override {
        endClk();
        PTAStat::performStat();
        uint64_t pointers = 0, pairs = 0, nonempty = 0;
        u32_t maximum = 0;
        for (const auto& entry : *cg->getPAG()) {
            if (!cg->getPAG()->isValidTopLevelPtr(entry.second)) continue;
            const u32_t size = cg->getPts(entry.first).count();
            ++pointers;
            pairs += size;
            nonempty += size != 0;
            maximum = std::max(maximum, size);
        }
        timeStatMap["TotalTime"] = (endTime - startTime) / TIMEINTERVAL;
        timeStatMap["SolveTime"] = cg->solveTime;
        timeStatMap["CGConstructionTime"] = cg->constructionTime;
        timeStatMap["LOPAOfflineTime"] = cg->offlineTime;
        timeStatMap["LOPAExportTime"] = cg->exportTime;
        timeStatMap["CGSolveTime"] = cg->solveTime;
        timeStatMap["AvgTopLvlPtsSize"] = pointers ? double(pairs) / pointers : 0;
        PTNumStatMap["MaxTopLvlPtsSize"] = maximum;
        timeStatMap["TopLevelPointers"] = pointers;
        timeStatMap["TopLevelNonempty"] = nonempty;
        timeStatMap["TopLevelPtsPairs"] = pairs;
        timeStatMap["CGCells"] = cg->cells.size();
        timeStatMap["CGMemoryCells"] = cg->memory.size();
        timeStatMap["CGCopyEdgesInserted"] = cg->copyCount;
        timeStatMap["CGOnlineMergedCells"] = cg->mergedCount;
        timeStatMap["CGLiveCells"] = cg->cells.size() - cg->mergedCount;
        uint64_t liveEdges = 0;
        for (size_t id = 0; id < cg->cells.size(); ++id)
            if (cg->cells[id].rep == id) liveEdges += cg->cells[id].copies.count();
        timeStatMap["CGLiveCopyEdges"] = liveEdges;
        timeStatMap["CGPropagationRounds"] = cg->rounds;
        if (cg->useSFR) {
            timeStatMap["CGSFRPositiveCycles"] = cg->positiveCycles;
            timeStatMap["CGSFRStrides"] = cg->strideCount;
            timeStatMap["CGSFRStrideCells"] = cg->strides.size();
            timeStatMap["CGSFRExpansionCalls"] = cg->expansionCalls;
            timeStatMap["CGSFRStrideFacts"] = cg->strideFacts;
            timeStatMap["CGSFRStrideVisits"] = cg->strideVisited;
            const auto& schedule = cg->sfrSchedule.counters;
            timeStatMap["CGSFRCopyGepVisits"] = schedule.visits;
            timeStatMap["CGSFRCopyGepSCCs"] = schedule.components;
            timeStatMap["CGSFRCyclicSCCs"] = schedule.cyclicComponents;
            timeStatMap["CGSFRLocalPops"] = schedule.localPops;
            timeStatMap["CGSFRCyclicPops"] = schedule.cyclicPops;
            timeStatMap["CGSFRFallbackPops"] = schedule.fallbackPops;
        }
        if (Options::CGProfile()) {
            timeStatMap["CGProfileSCCVisits"] = cg->sccVisited;
            timeStatMap["CGProfileSCC"] = cg->profileSCCTime;
            timeStatMap["CGProfileCopyGep"] = cg->profileCopyGepTime;
            timeStatMap["CGProfileLoadStore"] = cg->profileIndirectTime;
            timeStatMap["CGProfileCallGraph"] = cg->profileCallGraphTime;
        }
        printStat(cg->lopaFrontend ? "LOPA+CG-FSPTA Pointer Analysis Stat"
                                  : "CG-FSPTA Pointer Analysis Stat");
    }
private:
    FlowSensitiveCG* cg;
};
}

FlowSensitiveCG::CellID FlowSensitiveCG::newCell() {
    assert(cells.size() < std::numeric_limits<CellID>::max());
    const CellID id = cells.size();
    cells.emplace_back(id);
    return id;
}
FlowSensitiveCG::CellID FlowSensitiveCG::representative(CellID id) {
    CellID root = id;
    while (cells[root].rep != root) root = cells[root].rep;
    while (cells[id].rep != id) {
        const CellID next = cells[id].rep;
        cells[id].rep = root;
        id = next;
    }
    return root;
}
FlowSensitiveCG::CellID FlowSensitiveCG::valueCell(NodeID value) {
    const auto found = values.find(value);
    if (found != values.end()) return found->second;
    const CellID id = newCell();
    values.emplace(value, id);
    return id;
}
FlowSensitiveCG::CellID FlowSensitiveCG::memoryCell(NodeID location, NodeID object, bool output) {
    // SVFG locations are dense low IDs; object IDs retain all 32 bits.
    assert(location < (uint64_t(1) << 31));
    const uint64_t key = (uint64_t(location) << 33) | (uint64_t(object) << 1);
    const auto found = memory.find(key | output);
    if (found != memory.end()) return found->second;
    if (lopaFrontend) return invalidCell;
    const CellID in = newCell();
    memory.emplace(key, in);
    auto store = stores.find(location);
    if (store == stores.end()) {
        assert(!output && "Only stores define an OUT state");
        return in;
    }
    const CellID out = newCell();
    memory.emplace(key | 1, out);
    StoreState& state = store->second;
    state.memory.push_back({object, in, out});
    if (state.active && (!state.strong || state.singleton != object)) addCopy(in, out);
    return output ? out : in;
}
const PointsTo& FlowSensitiveCG::getPts(NodeID id) {
    if (resultExported) return BVDataPTAImpl::getPts(id);
    return cells[representative(valueCell(id))].pts;
}
bool FlowSensitiveCG::unionPts(NodeID id, const PointsTo& pts) {
    if (resultExported) return BVDataPTAImpl::unionPts(id, pts);
    return join(valueCell(id), pts);
}
bool FlowSensitiveCG::unionPts(NodeID id, NodeID source) { return unionPts(id, getPts(source)); }
bool FlowSensitiveCG::addPts(NodeID id, NodeID object) {
    PointsTo singleton;
    singleton.set(object);
    return unionPts(id, singleton);
}
void FlowSensitiveCG::enqueue(CellID id) {
    id = representative(id);
    if (!cells[id].queued) {
        cells[id].queued = true;
        if (!useSFR || !sfrSchedule.route(id)) pending.push_back(id);
    }
}
bool FlowSensitiveCG::join(CellID id, const PointsTo& pts) {
    id = representative(id);
    if (!(cells[id].pts |= pts)) return false;
    enqueue(id);
    return true;
}
void FlowSensitiveCG::addCopy(CellID src, CellID dst) {
    if (src == invalidCell || dst == invalidCell) return;
    src = representative(src);
    dst = representative(dst);
    if (src == dst || !cells[src].copies.test_and_set(dst)) return;
    ++copyCount;
    graphChanged = true;
    if (useSFR) sccCandidates.set(src);
    // New edges need the full source set, including previously propagated facts.
    join(dst, cells[src].pts);
}
void FlowSensitiveCG::addPhi(const PHISVFGNode* phi) {
    const CellID dst = valueCell(phi->getRes()->getId());
    for (auto it = phi->opVerBegin(); it != phi->opVerEnd(); ++it)
        addCopy(valueCell(it->second->getId()), dst);
}
void FlowSensitiveCG::addSVFGEdge(const SVFGEdge* edge) {
    const SVFGNode* src = edge->getSrcNode();
    const SVFGNode* dst = edge->getDstNode();
    if (const auto* indirect = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge)) {
        NodeBS objects = indirect->getPointsTo();
        for (NodeID object : indirect->getPointsTo())
            if (isFieldInsensitive(object)) objects |= getAllFieldsObjVars(object);
        for (NodeID object : objects)
            addCopy(memoryCell(src->getId(), object, SVFUtil::isa<StoreSVFGNode>(src)),
                    memoryCell(dst->getId(), object));
    } else if (const auto* actual = SVFUtil::dyn_cast<ActualParmSVFGNode>(src)) {
        const auto* formal = SVFUtil::cast<FormalParmSVFGNode>(dst);
        addCopy(valueCell(actual->getParam()->getId()), valueCell(formal->getParam()->getId()));
    } else if (const auto* formal = SVFUtil::dyn_cast<FormalRetSVFGNode>(src)) {
        const auto* actual = SVFUtil::cast<ActualRetSVFGNode>(dst);
        addCopy(valueCell(formal->getRet()->getId()), valueCell(actual->getRev()->getId()));
    }
}
void FlowSensitiveCG::compileGraph() {
    // Register stores before constructing memory cells, preserving IN/OUT identity.
    for (const auto& entry : *svfg)
        if (const auto* store = SVFUtil::dyn_cast<StoreSVFGNode>(entry.second))
            stores[store->getId()].node = store;
    for (const auto& entry : *svfg) {
        const SVFGNode* node = entry.second;
        if (const auto* addr = SVFUtil::dyn_cast<AddrSVFGNode>(node)) processAddr(addr);
        else if (const auto* copy = SVFUtil::dyn_cast<CopySVFGNode>(node))
            addCopy(valueCell(copy->getPAGSrcNodeID()), valueCell(copy->getPAGDstNodeID()));
        else if (const auto* phi = SVFUtil::dyn_cast<PHISVFGNode>(node)) addPhi(phi);
        else if (const auto* gep = SVFUtil::dyn_cast<GepSVFGNode>(node)) {
            cells[valueCell(gep->getPAGSrcNodeID())].geps.push_back(gep);
            if (useSFR) {
                // Even a GEP self-cycle may have no incident Copy edge.
                sccCandidates.set(valueCell(gep->getPAGSrcNodeID()));
                valueCell(gep->getPAGDstNodeID());
                graphChanged = true;
            }
        }
        else if (const auto* load = SVFUtil::dyn_cast<LoadSVFGNode>(node))
            cells[valueCell(load->getPAGSrcNodeID())].indirect.push_back(load);
        else if (const auto* store = SVFUtil::dyn_cast<StoreSVFGNode>(node))
            cells[valueCell(store->getPAGDstNodeID())].indirect.push_back(store);
        for (const SVFGEdge* edge : node->getOutEdges())
            if (!lopaFrontend || !SVFUtil::isa<IndirectSVFGEdge>(edge)) addSVFGEdge(edge);
    }
}
void FlowSensitiveCG::compileLOPAMemory() {
    for (const auto& entry : *svfg)
        if (const auto* store = SVFUtil::dyn_cast<StoreSVFGNode>(entry.second))
            stores[store->getId()].node = store;
    const double start = stat->getClk(true);
    LOPA frontend(pag);
    frontend.exportOffline(svfg, ander, *this,
        [&](NodeID object, const VDG& graph, const LOPA::LocToVersionMap& consumes,
            const LOPA::LocToVersionMap& yields) {
            const double exportStart = stat->getClk(true);
            std::vector<CellID> versions(graph.capacity(), invalidCell);
            graph.forEachSuperNode([&](Version version, const VDGNode*) {
                versions[version] = newCell();
            });
            auto cell = [&](Version version) {
                return versions.at(graph.getRepVersion(version));
            };
            auto publish = [&](NodeID location, CellID id, bool output) {
                assert(location < (uint64_t(1) << 31));
                const uint64_t key = (uint64_t(location) << 33) | (uint64_t(object) << 1) | output;
                memory.emplace(key, id);
            };
            graph.forEachSuperNode([&](Version source, const VDGNode* node) {
                for (Version target : node->getSolidOut()) addCopy(cell(source), cell(target));
            });
            for (const auto& entry : consumes) {
                const CellID in = cell(entry.second);
                publish(entry.first, in, false);
                auto store = stores.find(entry.first);
                if (store != stores.end()) {
                    const auto output = yields.find(entry.first);
                    const CellID out = output == yields.end() ? invalidCell : cell(output->second);
                    store->second.memory.push_back({object, in, out});
                }
            }
            for (const auto& entry : yields) {
                const CellID out = cell(entry.second);
                publish(entry.first, out, true);
                if (consumes.find(entry.first) == consumes.end())
                    stores.at(entry.first).memory.push_back({object, invalidCell, out});
            }
            exportTime += (stat->getClk(true) - exportStart) / TIMEINTERVAL;
        });
    offlineTime = (stat->getClk(true) - start) / TIMEINTERVAL - exportTime;
}
void FlowSensitiveCG::initialize() {
    if (!Options::UsePreCompFieldSensitive()) {
        SVFUtil::errs() << "CG-FSPTA requires -pre-field-sensitive=true: "
                       << "memory constraints use the preanalysis field model.\n";
        std::exit(1);
    }
    if (lopaFrontend && (Options::OPTSVFG() || !Options::VDGPassProfile().empty())) {
        SVFUtil::errs() << "LOPA+CG requires the original SVFG and disabled VDG pass profiling.\n";
        std::exit(1);
    }
    FlowSensitive::initialize();
    delete stat;
    stat = new FlowSensitiveCGStat(this);
    // Match VSFS: TotalTime starts after shared Andersen/MSSA/SVFG work and
    // includes graph construction, solving, export and normalization.
    stat->startClk();
    const double start = stat->getClk(true);
    if (lopaFrontend) compileLOPAMemory();
    compileGraph();
    constructionTime = (stat->getClk(true) - start) / TIMEINTERVAL;
}
void FlowSensitiveCG::queueIndirect(const SVFGNode* node) {
    if (indirectQueued.test_and_set(node->getId())) indirectWork.push_back(node);
}
void FlowSensitiveCG::solveCopies() {
    auto process = [&](CellID raw) {
        const CellID id = representative(raw);
        if (raw != id || !cells[id].queued) return;
        Cell& cell = cells[id];
        cell.queued = false;
        PointsTo delta = cell.pts - cell.sent;
        if (delta.empty()) return;
        cell.sent |= delta;
        for (CellID dst : cell.copies) join(dst, delta);
        for (const GepSVFGNode* gep : cell.geps) propagateGep(gep, delta);
        for (const SVFGNode* node : cell.indirect) queueIndirect(node);
    };
    if (useSFR) {
        sfrSchedule.solve(pending, [&](CellID id) { return cells[id].queued; }, process);
    } else {
        while (!pending.empty()) {
            const CellID raw = pending.front();
            pending.pop_front();
            process(raw);
        }
    }
}
void FlowSensitiveCG::propagateGep(const GepSVFGNode* gep, const PointsTo& delta) {
    const GepStmt* statement = SVFUtil::cast<GepStmt>(gep->getPAGEdge());
    PointsTo targets;
    for (NodeID object : delta) {
        if (isBlkObjOrConstantObj(object)) targets.set(object);
        else if (statement->isVariantFieldGep()) {
            setObjFieldInsensitive(object);
            targets.set(getFIObjVar(object));
        } else if (isFieldInsensitive(object)) targets.set(object);
        else targets.set(getGepObjVar(object, statement->getAccessPath().getConstantStructFldIdx()));
    }
    if (useSFR && !statement->isVariantFieldGep() &&
        statement->getAccessPath().getConstantStructFldIdx() >= 0)
        expandGepStrides(representative(valueCell(gep->getPAGDstNodeID())), targets);
    unionPts(gep->getPAGDstNodeID(), targets);
}
void FlowSensitiveCG::solveIndirect(const SVFGNode* node) {
    if (const auto* load = SVFUtil::dyn_cast<LoadSVFGNode>(node)) {
        if (!load->getPAGDstNode()->isPointer()) return;
        const PointsTo targets = getPts(load->getPAGSrcNodeID());
        const CellID dst = valueCell(load->getPAGDstNodeID());
        for (NodeID object : targets) {
            if (pag->isConstantObj(object)) continue;
            addCopy(memoryCell(load->getId(), object), dst);
            if (isFieldInsensitive(object))
                for (NodeID field : getAllFieldsObjVars(object))
                    addCopy(memoryCell(load->getId(), field), dst);
        }
        ++numOfProcessedLoad;
        return;
    }
    const auto* store = SVFUtil::cast<StoreSVFGNode>(node);
    const PointsTo targets = getPts(store->getPAGDstNodeID());
    // Delay bypass until the destination is resolved: a future singleton may kill IN.
    if (targets.empty()) return;
    StoreState& state = stores.at(store->getId());
    state.active = true;
    state.strong = isStrongUpdate(store, state.singleton);
    if (state.strong) svfgHasSU.set(store->getId());
    else svfgHasSU.reset(store->getId());
    if (store->getPAGSrcNode()->isPointer())
        for (NodeID object : targets)
            if (!pag->isConstantObj(object))
                addCopy(valueCell(store->getPAGSrcNodeID()), memoryCell(store->getId(), object, true));
    for (const MemoryPair& pair : state.memory)
        if (!state.strong || pair.object != state.singleton) addCopy(pair.in, pair.out);
    ++numOfProcessedStore;
}
void FlowSensitiveCG::collapseCopyCycles() {
    // Iterative Tarjan; only Copy cycles imply equal sets. No offline folding.
    const size_t count = cells.size();
    std::vector<unsigned> waveIndex, waveLow;
    std::vector<bool> waveActive;
    auto& index = useSFR ? sfrIndex : waveIndex;
    auto& low = useSFR ? sfrLow : waveLow;
    auto& active = useSFR ? sfrActive : waveActive;
    index.resize(count, 0); low.resize(count, 0); active.resize(count, false);
    std::vector<CellID> stack;
    struct Frame { CellID id; NodeBS::iterator it, end; };
    std::vector<Frame> dfs;
    std::vector<std::vector<CellID>> components;
    std::vector<CellID> reverseTopological;
    std::vector<CellID> visited;
    uint64_t roundVisited = 0;
    unsigned clock = 0;
    auto enter = [&](CellID id) {
        ++roundVisited;
        if (useSFR) visited.push_back(id);
        index[id] = low[id] = ++clock;
        active[id] = true;
        stack.push_back(id);
        dfs.push_back({id, cells[id].copies.begin(), cells[id].copies.end()});
    };
    // Every new cycle contains a new edge. Starting at its source and following
    // Copy edges therefore visits the complete affected Copy SCC.
    NodeBS roots;
    std::vector<CellID> selectedRoots;
    if (useSFR) {
        for (CellID root : sccCandidates) roots.set(representative(root));
        for (CellID root : roots) selectedRoots.push_back(root);
    }
    for (size_t nextRoot = 0; nextRoot < (useSFR ? selectedRoots.size() : count); ++nextRoot) {
        const CellID root = useSFR ? selectedRoots[nextRoot] : nextRoot;
        if (representative(root) != root || index[root]) continue;
        enter(root);
        while (!dfs.empty()) {
            Frame& frame = dfs.back();
            const CellID id = frame.id;
            if (frame.it != frame.end) {
                const CellID dst = representative(*frame.it);
                ++frame.it;
                if (!index[dst]) { enter(dst); continue; }
                if (active[dst]) low[id] = std::min(low[id], index[dst]);
                continue;
            }
            dfs.pop_back();
            if (!dfs.empty()) low[dfs.back().id] = std::min(low[dfs.back().id], low[id]);
            if (low[id] != index[id]) continue;
            std::vector<CellID> component;
            CellID member;
            do {
                member = stack.back(); stack.pop_back();
                active[member] = false;
                component.push_back(member);
            } while (member != id);
            reverseTopological.push_back(component.front());
            if (component.size() > 1) components.push_back(std::move(component));
        }
    }
    // Install all representatives before collecting outgoing edges, so internal
    // edges never accumulate in a temporary SCC adjacency set.
    for (const auto& component : components)
        for (size_t i = 1; i < component.size(); ++i)
            cells[component[i]].rep = component.front();
    auto collectCopies = [&](CellID source, CellID root, std::vector<CellID>& edges) {
        for (CellID dst : cells[source].copies) {
            const CellID target = representative(dst);
            if (target != root) edges.push_back(target);
        }
    };
    auto replaceCopies = [&](CellID id, std::vector<CellID>& edges) {
        std::sort(edges.begin(), edges.end());
        edges.erase(std::unique(edges.begin(), edges.end()), edges.end());
        cells[id].copies.clear();
        // SparseBitVector insertion is linear when destinations are sorted.
        for (CellID dst : edges) cells[id].copies.set(dst);
    };
    std::vector<CellID> edges;
    for (const auto& component : components) {
        const CellID root = component.front();
        Cell& target = cells[root];
        edges.clear();
        collectCopies(root, root, edges);
        for (size_t i = 1; i < component.size(); ++i) {
            Cell& source = cells[component[i]];
            target.pts |= source.pts;
            collectCopies(component[i], root, edges);
            target.geps.insert(target.geps.end(), source.geps.begin(), source.geps.end());
            target.indirect.insert(target.indirect.end(), source.indirect.begin(), source.indirect.end());
            if (useSFR) {
                const auto found = strides.find(component[i]);
                if (found != strides.end()) {
                    const auto sourceStrides = std::move(found->second);
                    strides.erase(found);
                    auto& targetStrides = strides[root];
                    for (CGSFR::Weight stride : sourceStrides)
                        if (std::find(targetStrides.begin(), targetStrides.end(), stride) == targetStrides.end())
                            targetStrides.push_back(stride);
                }
            }
            source.pts.clear(); source.sent.clear(); source.copies.clear();
            source.geps.clear(); source.indirect.clear(); source.queued = false;
            ++mergedCount;
        }
        replaceCopies(root, edges);
        target.sent.clear();
        enqueue(root);
    }
    if (!components.empty()) {
        // Contract edge endpoints as well as nodes. Otherwise several retired
        // destinations keep representing the same Copy edge in later waves.
        for (size_t next = 0; next < (useSFR ? visited.size() : count); ++next) {
            const CellID id = useSFR ? visited[next] : next;
            if (cells[id].rep != id) continue;
            edges.clear();
            collectCopies(id, id, edges);
            replaceCopies(id, edges);
        }
    }
    // SCCs finish sink first. Seed the propagation wave in source-first order;
    // GEP consequences discovered during the wave can append further work.
    std::deque<CellID> remaining;
    if (useSFR) remaining.swap(pending);
    else pending.clear();
    NodeBS scheduled;
    for (auto it = reverseTopological.rbegin(); it != reverseTopological.rend(); ++it)
        if (cells[*it].queued) {
            pending.push_back(*it);
            if (useSFR) scheduled.set(*it);
        }
    // A selective scan need not visit every cell whose points-to set changed.
    // Keep these pending facts, including representatives created by merging.
    for (CellID raw : remaining) {
        const CellID id = representative(raw);
        if (cells[id].queued && scheduled.test_and_set(id)) pending.push_back(id);
    }
    sccVisited += roundVisited;
    if (useSFR) {
        for (CellID id : visited) index[id] = 0;
        scheduleCopyGep(roots);
        detectStrides();
        sccCandidates.clear();
    }
    graphChanged = false;
}

void FlowSensitiveCG::scheduleCopyGep(const NodeBS& candidates) {
    NodeBS roots;
    for (CellID id : candidates) roots.set(representative(id));
    struct Cursor {
        CellID source;
        NodeBS::iterator copy, end;
        size_t gep = 0;
    };
    sfrSchedule.build(roots, cells.size(),
        [&](CellID id) {
            return Cursor{id, cells[id].copies.begin(), cells[id].copies.end(), 0};
        },
        [&](Cursor& cursor) -> CellID {
            if (cursor.copy != cursor.end) return representative(*cursor.copy++);
            const auto& geps = cells[cursor.source].geps;
            if (cursor.gep == geps.size()) return CGSFR::Schedule::invalid;
            return representative(valueCell(geps[cursor.gep++]->getPAGDstNodeID()));
        }, sfrIndex, sfrLow, sfrActive);
}

void FlowSensitiveCG::detectStrides() {
    std::vector<CellID> roots;
    sfrSchedule.forEachMultiNodeComponent([&](auto begin, auto end) {
        roots.insert(roots.end(), begin, end);
    });
    const auto result = CGSFR::findStrides(roots,
        [&](CellID id) {
            std::vector<CGSFR::Edge> edges;
            edges.reserve(cells[id].copies.count() + cells[id].geps.size());
            const CellID component = sfrSchedule.component(id);
            for (CellID target : cells[id].copies) {
                target = representative(target);
                if (sfrSchedule.component(target) == component) edges.push_back({target, 0});
            }
            for (const GepSVFGNode* gep : cells[id].geps) {
                const GepStmt* statement = SVFUtil::cast<GepStmt>(gep->getPAGEdge());
                if (statement->isVariantFieldGep()) continue;
                const APOffset offset = statement->getAccessPath().getConstantStructFldIdx();
                if (offset < 0) continue;
                const CellID target = representative(valueCell(gep->getPAGDstNodeID()));
                if (sfrSchedule.component(target) == component)
                    edges.push_back({target, static_cast<CGSFR::Weight>(offset)});
            }
            return edges;
        },
        [&](CellID id, CGSFR::Weight stride) {
            // SVF's bounded-offset check casts offsets to u32_t. Do not use
            // an arithmetic shortcut outside that transfer function's range.
            if (stride > std::numeric_limits<u32_t>::max()) return;
            auto& current = strides[id];
            if (std::find(current.begin(), current.end(), stride) != current.end()) return;
            current.push_back(stride);
            ++strideCount;
        });
    strideVisited += result.visited;
    positiveCycles += result.positiveCycles;
}

void FlowSensitiveCG::expandGepStrides(CellID dst, PointsTo& targets) {
    const auto found = strides.find(dst);
    if (found == strides.end() || targets.empty()) return;
    PointsTo expanded;
    const auto initials = CGSFR::expandGep(targets, found->second,
        [&](NodeID object) { return cells[dst].pts.test(object); },
        [&](NodeID object) { return !isBlkObjOrConstantObj(object) && !isFieldInsensitive(object); },
        [&](NodeID object, CGSFR::Weight stride) {
            // All witnessed edges are nonnegative. Repeating the whole cycle
            // has exactly this shift under SVF's existing bounded field model.
            const auto* field = SVFUtil::dyn_cast<GepObjVar>(pag->getGNode(object));
            const APOffset offset = field ? field->getConstantFieldIdx() : 0;
            if (stride > std::numeric_limits<u32_t>::max() - static_cast<CGSFR::Weight>(offset))
                return object;
            return getGepObjVar(object, static_cast<APOffset>(stride));
        },
        [&](NodeID object) { expanded.set(object); });
    if (!initials) return;
    ++expansionCalls;
    expanded -= cells[dst].pts;
    expanded -= targets;
    strideFacts += expanded.count();
    targets |= expanded;
}
void FlowSensitiveCG::updateConnectedNodes(const SVFGEdgeSetTy& edges) {
    for (const SVFGEdge* edge : edges) {
        addSVFGEdge(edge);
        if (const auto* phi = SVFUtil::dyn_cast<PHISVFGNode>(edge->getDstNode())) addPhi(phi);
    }
}
void FlowSensitiveCG::solveConstraints() {
    const bool timer = SVFUtil::startAnalysisLimitTimer(Options::FsTimeLimit());
    const double start = stat->getClk(true);
    const bool profile = Options::CGProfile();
    bool callsChanged;
    do {
        ++numOfIteration;
        const double callSCCStart = profile ? stat->getClk(true) : 0;
        callGraphSCC->find();
        if (profile) profileCallGraphTime += (stat->getClk(true) - callSCCStart) / TIMEINTERVAL;
        // New recursion can invalidate a formerly strong store.
        for (const auto& entry : stores)
            if (entry.second.active) queueIndirect(entry.second.node);
        do {
            ++rounds;
            const size_t pendingBefore = pending.size();
            double phaseStart = profile ? stat->getClk(true) : 0;
            if (graphChanged) collapseCopyCycles();
            const double sccTime = profile ? (stat->getClk(true) - phaseStart) / TIMEINTERVAL : 0;
            phaseStart = profile ? stat->getClk(true) : 0;
            solveCopies();
            const double copyGepTime = profile ? (stat->getClk(true) - phaseStart) / TIMEINTERVAL : 0;
            const size_t indirectBefore = indirectWork.size();
            phaseStart = profile ? stat->getClk(true) : 0;
            while (!indirectWork.empty()) {
                const SVFGNode* node = indirectWork.front(); indirectWork.pop_front();
                indirectQueued.reset(node->getId());
                solveIndirect(node);
            }
            if (profile) {
                const double indirectTime = (stat->getClk(true) - phaseStart) / TIMEINTERVAL;
                profileSCCTime += sccTime;
                profileCopyGepTime += copyGepTime;
                profileIndirectTime += indirectTime;
                SVFUtil::outs() << "CGProfile round=" << rounds
                    << " call_iteration=" << numOfIteration
                    << " scc_cpu=" << sccTime << " copy_gep_cpu=" << copyGepTime
                    << " load_store_cpu=" << indirectTime
                    << " pending_before=" << pendingBefore << " indirect_before=" << indirectBefore
                    << " cells=" << cells.size() << " live_cells=" << cells.size() - mergedCount
                    << " copy_edges_inserted=" << copyCount << "\n";
            }
        } while (!pending.empty());
        const double callStart = profile ? stat->getClk(true) : 0;
        callsChanged = updateCallGraph(getIndirectCallsites());
        if (profile) {
            const double callTime = (stat->getClk(true) - callStart) / TIMEINTERVAL;
            profileCallGraphTime += callTime;
            SVFUtil::outs() << "CGProfile call_iteration=" << numOfIteration
                << " call_update_cpu=" << callTime << " changed=" << callsChanged << "\n";
        }
    } while (callsChanged || !pending.empty());
    solveTime = (stat->getClk(true) - start) / TIMEINTERVAL;
    SVFUtil::stopAnalysisLimitTimer(timer);
}
void FlowSensitiveCG::finalize() {
    for (const auto& entry : values)
        getPTDataTy()->unionPts(entry.first, cells[representative(entry.second)].pts);
    // SVF normalizes field objects through getPts/clearPts/addPts at finalize.
    // Use one storage backend for all three operations from this point onward.
    resultExported = true;
    if (Options::DumpVFG()) svfg->dump("cg_source_svfg", true);
    BVDataPTAImpl::finalize();
}
