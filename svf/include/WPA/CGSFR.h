#ifndef SVF_CG_SFR_H
#define SVF_CG_SFR_H

#include <cstdint>
#include <limits>
#include <unordered_map>
#include <unordered_set>
#include <vector>

namespace SVF {
/// Online helpers for the explicit-field SFR implementation in AndersenSFR/CSC.
/// A recorded stride always has a witnessed directed cycle. Unrecorded cycles
/// are still resolved by ordinary Copy/GEP propagation in the caller.
namespace CGSFR {
using Node = uint32_t;
using Weight = uint64_t;
struct Edge { Node target; Weight weight; };
struct CycleStats { uint64_t visited = 0, positiveCycles = 0; };

/// Successors must contain only Copy and nonnegative constant GEP edges.
/// Path distance belongs to the current DFS branch, and visitation is fresh
/// for each call, including calls following a dynamically inserted edge.
template<class Roots, class Successors, class Record>
CycleStats findStrides(const Roots& roots, Successors successors, Record record) {
    struct State { size_t depth; bool active; };
    struct Frame { Node node; Weight distance; std::vector<Edge> edges; size_t next; };
    std::unordered_map<Node, State> visited;
    std::vector<Frame> path;
    CycleStats stats;
    auto enter = [&](Node node, Weight distance) {
        visited.emplace(node, State{path.size(), true});
        path.push_back({node, distance, successors(node), 0});
        ++stats.visited;
    };
    for (Node root : roots) {
        if (visited.count(root)) continue;
        enter(root, 0);
        while (!path.empty()) {
            Frame& frame = path.back();
            if (frame.next == frame.edges.size()) {
                visited.at(frame.node).active = false;
                path.pop_back();
                continue;
            }
            const Edge edge = frame.edges[frame.next++];
            // Ignoring an unrepresentable shortcut cannot lose ordinary facts.
            if (edge.weight > std::numeric_limits<Weight>::max() - frame.distance) continue;
            const Weight distance = frame.distance + edge.weight;
            auto found = visited.find(edge.target);
            if (found == visited.end()) {
                enter(edge.target, distance);
                continue;
            }
            if (!found->second.active) continue;
            const size_t first = found->second.depth;
            const Weight stride = distance - path[first].distance;
            if (!stride) continue;
            ++stats.positiveCycles;
            for (size_t i = first; i < path.size(); ++i) record(path[i].node, stride);
        }
    }
    return stats;
}

/// Expand a finite explicit field domain using its existing shift operation.
/// The callback retains the caller's modulus/saturation and object identity.
template<class Initials, class Strides, class Shift, class Emit>
uint64_t expand(const Initials& initials, const Strides& strides, Shift shift, Emit emit) {
    std::unordered_set<Node> seen;
    std::vector<Node> pending;
    for (Node initial : initials)
        if (seen.insert(initial).second) pending.push_back(initial);
    uint64_t added = 0;
    for (size_t next = 0; next < pending.size(); ++next) {
        const Node source = pending[next];
        for (Weight stride : strides) {
            const Node target = shift(source, stride);
            if (seen.insert(target).second) {
                pending.push_back(target);
                emit(target);
                ++added;
            }
        }
    }
    return added;
}

/// The ordinary GEP offset has already been applied to targets. Keep every
/// ordinary result, then close eligible new destination facts under its strides.
/// Testing unshifted source facts against the destination could lose GEP facts.
template<class Targets, class Strides, class Known, class Eligible, class Shift, class Emit>
uint64_t expandGep(const Targets& targets, const Strides& strides,
                   Known known, Eligible eligible, Shift shift, Emit emit) {
    std::vector<Node> initials;
    for (Node target : targets) {
        emit(target);
        if (!known(target) && eligible(target)) initials.push_back(target);
    }
    if (!initials.empty()) expand(initials, strides, shift, emit);
    return initials.size();
}
} // namespace CGSFR
} // namespace SVF
#endif
