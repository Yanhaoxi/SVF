#include "Graphs/PUSGraph.h"
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <random>
#include <set>
#include <unordered_set>
#include <vector>

using namespace SVF;
using Key = uint64_t;

#define CHECK(condition) do { \
    if (!(condition)) { \
        std::cerr << "Check failed at line " << __LINE__ << ": " << #condition << '\n'; \
        std::abort(); \
    } \
} while (false)

static Key key(NodeID src, NodeID dst) {
    return (Key(src) << 32) | dst;
}

static void verify(const PUSConstraintGraph& graph,
                   const std::unordered_set<Key>& expected,
                   const std::vector<bool>& live) {
    CHECK(graph.copyCount() == expected.size());
    size_t outgoing = 0, incoming = 0;
    for (NodeID id = 0; id < live.size(); ++id) {
        CHECK(graph.hasNode(id) == live[id]);
        if (!live[id]) continue;
        const auto* node = graph.getNode(id);
        for (NodeID dst : node->outgoing) {
            CHECK(id != dst && graph.hasNode(dst));
            CHECK(expected.count(key(id, dst)));
            CHECK(graph.getNode(dst)->incoming.count(id));
            ++outgoing;
        }
        for (NodeID src : node->incoming) {
            CHECK(id != src && graph.hasNode(src));
            CHECK(expected.count(key(src, id)));
            CHECK(graph.getNode(src)->outgoing.count(id));
            ++incoming;
        }
    }
    CHECK(outgoing == expected.size() && incoming == expected.size());
}

static void adjacent_components() {
    PUSConstraintGraph graph;
    for (NodeID id = 0; id < 8; ++id) CHECK(graph.newNode() == id);
    // Two adjacent cyclic components, with duplicate edges after contraction.
    const std::vector<std::pair<NodeID, NodeID>> edges = {
        {0,1}, {1,0}, {0,2}, {1,2}, {1,3}, {2,3}, {3,2},
        {3,4}, {2,4}, {5,0}, {5,1}, {4,6}
    };
    for (const auto& e : edges) CHECK(graph.addCopy(e.first, e.second));
    for (const auto& e : std::vector<std::pair<NodeID, NodeID>>{
            {0,2}, {1,2}, {1,3}, {2,3}, {3,2}, {3,4}, {2,4}})
        CHECK(graph.removeCopy(e.first, e.second));
    graph.removeNode(2);
    CHECK(graph.addCopy(0,3));
    CHECK(graph.addCopy(1,3));
    CHECK(graph.addCopy(3,4));
    CHECK(!graph.addCopy(1,3));
    for (const auto& e : std::vector<std::pair<NodeID, NodeID>>{
            {0,1}, {1,0}, {0,3}, {1,3}, {5,0}, {5,1}})
        CHECK(graph.removeCopy(e.first, e.second));
    graph.removeNode(0);
    CHECK(graph.addCopy(1,3));
    CHECK(graph.addCopy(5,1));
    std::vector<bool> live(8, true);
    live[0] = live[2] = false;
    std::unordered_set<Key> expected = {key(1,3), key(3,4), key(4,6), key(5,1)};
    verify(graph, expected, live);
    // A later edge can form a new cycle among the surviving representatives.
    CHECK(graph.addCopy(4,1));
    expected.insert(key(4,1));
    verify(graph, expected, live);
    CHECK(graph.newNode() == 8); // Retired IDs must never be reused.
}

static void high_degree_and_growth() {
    PUSConstraintGraph graph;
    constexpr NodeID count = 20000;
    for (NodeID id = 0; id < count; ++id) CHECK(graph.newNode() == id);
    std::unordered_set<Key> expected;
    // Reverse insertions exercise ordered iteration and high-degree fallback.
    for (NodeID id = count - 1; id > 0; --id) {
        CHECK(graph.addCopy(0, id));
        CHECK(graph.addCopy(id, 0));
        expected.insert(key(0, id));
        expected.insert(key(id, 0));
    }
    for (NodeID id = count; id < count * 2; ++id) CHECK(graph.newNode() == id);
    NodeID previous = 0;
    for (NodeID dst : graph.getNode(0)->outgoing) {
        CHECK(dst > previous);
        previous = dst;
    }
    CHECK(previous == count - 1);
    std::vector<bool> live(count * 2, true);
    verify(graph, expected, live);
    const size_t before = expected.size();
    CHECK(graph.detachNode(0, [&](NodeID src, NodeID dst) {
        CHECK(expected.erase(key(src, dst)) == 1);
    }) == before);
    graph.removeNode(0); live[0] = false;
    verify(graph, expected, live);
    // Repeated promotion, shrinkage and clear exercise both representations.
    for (unsigned cycle = 0; cycle < 1000; ++cycle) {
        for (NodeID dst = 9; dst > 1; --dst) CHECK(graph.addCopy(1, dst));
        for (NodeID dst = 2; dst < 9; ++dst) CHECK(graph.removeCopy(1, dst));
        CHECK(graph.getNode(1)->outgoing.count(9));
        CHECK(graph.detachNode(1, [](NodeID src, NodeID dst) {
            CHECK(src == 1 && dst == 9);
        }) == 1);
    }
    verify(graph, expected, live);
}

int main() {
    adjacent_components();
    high_degree_and_growth();
    constexpr NodeID count = 2048;
    constexpr unsigned campaigns = 4, operations = 40000;
    std::mt19937 rng(20261029);
    uint64_t inserted = 0, removed = 0, duplicateChecks = 0, selfChecks = 0;
    for (unsigned campaign = 0; campaign < campaigns; ++campaign) {
        PUSConstraintGraph graph;
        CHECK(graph.newNode() == 0);
        for (NodeID id = 1; id < count; ++id) CHECK(graph.newNode() == id);
        CHECK(graph.hasNode(0) && graph.getNode(0)->outgoing.empty());
        std::vector<bool> live(count, true);
        std::unordered_set<Key> expected;
        std::vector<Key> history;
        for (unsigned op = 0; op < operations; ++op) {
            NodeID src = rng() % count, dst = rng() % count;
            if (op % 5 == 0 && !history.empty()) {
                const Key chosen = history[rng() % history.size()];
                src = chosen >> 32; dst = chosen & 0xffffffffu;
                const bool erased = expected.erase(chosen) != 0;
                CHECK(graph.removeCopy(src, dst) == erased);
                removed += erased;
            } else {
                const bool added = src != dst && expected.insert(key(src, dst)).second;
                CHECK(graph.addCopy(src, dst) == added);
                if (added) { ++inserted; history.push_back(key(src, dst)); }
                CHECK(!graph.addCopy(src, dst));
                ++duplicateChecks;
            }
            CHECK(!graph.addCopy(src, src));
            ++selfChecks;
            if (op % 2000 == 0) verify(graph, expected, live);
        }
        verify(graph, expected, live);
        for (NodeID id = 0; id < count; id += 11) {
            const size_t before = expected.size();
            const size_t detached = graph.detachNode(id, [&](NodeID src, NodeID dst) {
                CHECK(src == id || dst == id);
                CHECK(expected.erase(key(src, dst)) == 1);
                ++removed;
            });
            CHECK(detached == before - expected.size());
            graph.removeNode(id); live[id] = false;
        }
        verify(graph, expected, live);
        for (NodeID id = count; id < count + 1024; ++id) {
            CHECK(graph.newNode() == id); live.push_back(true);
        }
        verify(graph, expected, live);
        if (campaign % 2 == 0) {
            for (Key e : expected) {
                CHECK(graph.removeCopy(e >> 32, e & 0xffffffffu));
                ++removed;
            }
            expected.clear();
            for (NodeID id = 0; id < live.size(); ++id)
                if (live[id]) { graph.removeNode(id); live[id] = false; }
            verify(graph, expected, live);
        }
        // Other campaigns leave edges and nodes to the graph destructor.
    }
    std::cout << "{\"campaigns\":" << campaigns
              << ",\"random_operations\":" << campaigns * operations
              << ",\"insertions\":" << inserted << ",\"deletions\":" << removed
              << ",\"duplicate_checks\":" << duplicateChecks
              << ",\"self_checks\":" << selfChecks
              << ",\"node_bytes\":" << sizeof(PUSConstraintGraph::Node)
              << ",\"adjacency_bytes\":" << sizeof(PUSConstraintGraph::Adjacency)
              << ",\"iterator_bytes\":" << sizeof(PUSConstraintGraph::Adjacency::const_iterator)
              << ",\"result\":\"pass\"}\n";
}
