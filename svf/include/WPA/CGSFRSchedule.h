#ifndef SVF_CG_SFR_SCHEDULE_H
#define SVF_CG_SFR_SCHEDULE_H

#include "WPA/CGSFR.h"
#include <algorithm>
#include <cassert>
#include <deque>

namespace SVF {
namespace CGSFR {

/// Copy+GEP SCCs control propagation order, without identifying their nodes.
/// Build only between propagation phases, when the direct graph is fixed.
class Schedule {
public:
    static constexpr Node invalid = std::numeric_limits<Node>::max();
    struct Counters {
        uint64_t visits = 0, components = 0, cyclicComponents = 0;
        uint64_t localPops = 0, cyclicPops = 0, fallbackPops = 0;
    } counters;

    /// Reuse the caller's Tarjan workspace. start(node) creates an edge cursor;
    /// next(cursor) returns its next canonical target, or invalid at the end.
    template<class Roots, class Start, class Next>
    void build(const Roots& roots, size_t count, Start start, Next next,
               std::vector<unsigned>& index, std::vector<unsigned>& low,
               std::vector<bool>& active) {
        assert(current == invalid && local.empty());
        componentOf.resize(count, invalid);
        for (Node node : members) componentOf[node] = invalid;
        members.clear(); ends.clear(); cyclic.clear();
        index.resize(count, 0); low.resize(count, 0); active.resize(count, false);
        using Cursor = decltype(start(Node{}));
        struct Frame { Node node; Cursor edges; bool selfEdge = false; };
        std::vector<Frame> dfs;
        std::vector<Node> stack;
        unsigned clock = 0;
        auto enter = [&](Node node) {
            assert(node < count && !index[node]);
            index[node] = low[node] = ++clock;
            active[node] = true;
            stack.push_back(node);
            dfs.push_back({node, start(node), false});
        };
        for (Node root : roots) {
            assert(root < count);
            if (index[root]) continue;
            enter(root);
            while (!dfs.empty()) {
                Frame& frame = dfs.back();
                const Node node = frame.node;
                const Node target = next(frame.edges);
                if (target != invalid) {
                    assert(target < count);
                    frame.selfEdge |= target == node;
                    if (!index[target]) { enter(target); continue; }
                    if (active[target]) low[node] = std::min(low[node], index[target]);
                    continue;
                }
                const bool selfEdge = frame.selfEdge;
                dfs.pop_back();
                if (!dfs.empty())
                    low[dfs.back().node] = std::min(low[dfs.back().node], low[node]);
                if (low[node] != index[node]) continue;
                const size_t begin = members.size();
                const Node component = ends.size();
                Node member;
                do {
                    member = stack.back(); stack.pop_back();
                    active[member] = false;
                    componentOf[member] = component;
                    members.push_back(member);
                } while (member != node);
                ends.push_back(members.size());
                cyclic.push_back(selfEdge || members.size() - begin > 1);
            }
        }
        for (Node node : members) index[node] = 0;
        counters.visits += members.size();
        counters.components += ends.size();
        counters.cyclicComponents += std::count(cyclic.begin(), cyclic.end(), true);
    }

    Node component(Node node) const {
        return node < componentOf.size() ? componentOf[node] : invalid;
    }

    template<class Visit>
    void forEachMultiNodeComponent(Visit visit) const {
        size_t begin = 0;
        for (size_t end : ends) {
            if (end - begin > 1) visit(members.begin() + begin, members.begin() + end);
            begin = end;
        }
    }

    /// The caller marks a node queued before routing it. Future components
    /// inspect that mark when reached; the current component needs a local push.
    bool route(Node node) {
        if (current == invalid) return false;
        const Node target = component(node);
        if (target == invalid || target > current) return false;
        if (target == current) local.push_back(node);
        return true;
    }

    template<class Queued, class Process>
    void solve(std::deque<Node>& pending, Queued queued, Process process) {
        // Tarjan finishes sinks first, so reverse the component order.
        for (size_t next = ends.size(); next > 0; --next) {
            current = next - 1;
            const size_t begin = current ? ends[current - 1] : 0;
            for (size_t i = begin; i < ends[current]; ++i)
                if (queued(members[i])) local.push_back(members[i]);
            while (!local.empty()) {
                const Node node = local.front(); local.pop_front();
                ++counters.localPops;
                counters.cyclicPops += cyclic[current];
                process(node);
            }
        }
        current = invalid;
        // A selective graph scan may omit nodes with pending facts. Keep their
        // work, including facts they send into already processed components.
        while (!pending.empty()) {
            const Node node = pending.front(); pending.pop_front();
            ++counters.fallbackPops;
            process(node);
        }
    }

private:
    std::vector<Node> componentOf, members;
    std::vector<size_t> ends;
    std::vector<bool> cyclic;
    std::deque<Node> local;
    Node current = invalid;
};
} // namespace CGSFR
} // namespace SVF
#endif
