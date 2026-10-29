#include "WPA/LOPA.h"
#include "Util/PTAStat.h"
#include "Util/Options.h"
#include <algorithm>

using namespace SVF;

const LOPACopySolver::Components& LOPACopySolver::findComponents(const PUSConstraintGraph& graph, const NodeBS& selected) {
    Components& result = components;
    result.visited.clear();
    result.members.clear();
    result.ranges.clear();
    stack.clear();
    dfs.clear();
    auto& visited = result.visited;
    auto& members = result.members;
    auto& components = result.ranges;
    // Most components are singletons. Store all members contiguously instead
    // of allocating a separate vector for every visited node in every round.
    unsigned clock = 0;
    auto enter = [&](NodeID id) {
        index[id] = low[id] = ++clock;
        active[id] = true; stack.push_back(id); visited.push_back(id);
        const auto& edges = graph.getNode(id)->outgoing;
        dfs.push_back({id, edges.begin(), edges.end()});
    };
    for (NodeID root : selected) {
        if (index[root]) continue;
        enter(root);
        while (!dfs.empty()) {
            Frame& frame = dfs.back();
            const NodeID id = frame.id;
            if (frame.it != frame.end) {
                const NodeID dst = *frame.it++;
                if (!index[dst]) { enter(dst); continue; }
                if (active[dst]) low[id] = std::min(low[id], index[dst]);
                continue;
            }
            dfs.pop_back();
            if (!dfs.empty()) low[dfs.back().id] = std::min(low[dfs.back().id], low[id]);
            if (low[id] != index[id]) continue;
            const size_t begin = members.size();
            NodeID member;
            do {
                member = stack.back(); stack.pop_back(); active[member] = false;
                members.push_back(member);
            } while (member != id);
            components.emplace_back(begin, members.size());
        }
    }
    return result;
}

uint64_t LOPACopySolver::detachEdges(LOPA& p, NodeID id, EdgeList& replacements) {
    return p.constraints->detachNode(id, [&](NodeID src, NodeID dst) {
        const NodeID from = p.representative(src), to = p.representative(dst);
        if (from != to) replacements.emplace_back(from, to);
    });
}

void LOPACopySolver::mergeFacts(LOPA& p, NodeID root, NodeID member) {
    p.points->unionPts(root, member);
    p.points->clearFullPts(member);
    p.mergeConstraintGroups(root, member);
    p.copyDirty[member] = false;
    ++stats.merged;
}

uint64_t LOPACopySolver::rebuildEdges(LOPA& p, EdgeList& edges) {
    std::sort(edges.begin(), edges.end());
    edges.erase(std::unique(edges.begin(), edges.end()), edges.end());
    uint64_t rebuilt = 0;
    for (const auto& edge : edges) rebuilt += p.constraints->addCopy(edge.first, edge.second);
    return rebuilt;
}

void LOPACopySolver::mergeComponent(LOPA& p, const NodeID* begin, const NodeID* end) {
    ++stats.sccMerges;
    stats.maxSCCMembers = std::max(stats.maxSCCMembers, uint64_t(end - begin));
    NodeID root = *begin;
    // Canonicalize endpoints before collecting replacement edges.
    for (auto it = begin; it != end; ++it) p.parent[*it] = root;
    replacements.clear();
    uint64_t removed = 0;
    for (auto it = begin; it != end; ++it) {
        removed += detachEdges(p, *it, replacements);
        if (*it != root) mergeFacts(p, root, *it);
    }
    for (auto it = begin; it != end; ++it)
        if (*it != root) p.constraints->removeNode(*it);
    const uint64_t rebuilt = rebuildEdges(p, replacements);
    stats.sccEdgesTouched += removed;
    stats.sccEdgesRebuilt += rebuilt;
    stats.sccEdgesRemoved += removed - rebuilt;
    // Each inherited group retains its own history and consumes any facts it
    // has not yet seen from the merged set, including the root's old facts.
    p.changed(root);
}

void LOPACopySolver::mergeCycles(LOPA& p, const Components& components) {
    for (const auto& range : components.ranges)
        if (range.second - range.first > 1)
            mergeComponent(p, components.members.data() + range.first,
                           components.members.data() + range.second);
}

void LOPACopySolver::propagateCopies(LOPA& p, const Components& components) {
    // Tarjan emits sinks first; visit changed predecessors before successors.
    for (auto it = components.ranges.rbegin(); it != components.ranges.rend(); ++it) {
        const NodeID id = components.members[it->first];
        if (p.copyDirty[id]) {
            for (NodeID dst : p.constraints->getNode(id)->outgoing) p.joinRepresentatives(dst, id);
        }
        p.copyDirty[id] = false;
    }
}

void LOPACopySolver::solve(LOPA& p) {
    const bool profile = Options::LOPAProfile();
    const double start = profile ? p.stat->getClk(true) : 0;
    NodeBS selected;
    for (NodeID id : p.roots) selected.set(p.representative(id));
    p.roots.clear();
    index.resize(p.parent.size(), 0); low.resize(p.parent.size()); active.resize(p.parent.size(), false);
    const Components& components = findComponents(*p.constraints, selected);
    propagating = true;
    const double mergeStart = profile ? p.stat->getClk(true) : 0;
    mergeCycles(p, components);
    if (profile) stats.mergeTime += (p.stat->getClk(true) - mergeStart) / TIMEINTERVAL;
    stats.visits += components.visited.size();
    for (NodeID id : components.visited) index[id] = 0;
    const double propagated = profile ? p.stat->getClk(true) : 0;
    if (profile) stats.sccTime += (propagated - start) / TIMEINTERVAL;
    propagateCopies(p, components);
    propagating = false;
    if (profile) stats.copyTime += (p.stat->getClk(true) - propagated) / TIMEINTERVAL;
}
