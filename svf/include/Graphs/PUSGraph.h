#ifndef SVF_PUS_GRAPH_H
#define SVF_PUS_GRAPH_H

#include "Util/GeneralType.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <iterator>
#include <limits>
#include <variant>

namespace SVF {

/// Copy-only graph. Dense IDs index nodes; adjacency stores IDs directly.
/// SCC representatives and GEP/Load/Store constraints belong to the solver.
class PUSConstraintGraph {
public:
    /// Keep small neighborhoods inline without making high-degree insertion linear.
    /// Both representations iterate in ID order, preserving the solver's traversal.
    class Adjacency {
        static constexpr size_t inlineCapacity = 4;
        using Small = std::array<NodeID, inlineCapacity>;
        using Tree = std::set<NodeID>;
        std::variant<Small, std::unique_ptr<Tree>> storage;
        unsigned smallSize = 0;

        const Tree* tree() const {
            const auto* expanded = std::get_if<std::unique_ptr<Tree>>(&storage);
            return expanded ? expanded->get() : nullptr;
        }

    public:
        class const_iterator {
            std::variant<const NodeID*, Tree::const_iterator> position;
        public:
            using iterator_category = std::forward_iterator_tag;
            using value_type = NodeID;
            using difference_type = std::ptrdiff_t;
            using pointer = const NodeID*;
            using reference = const NodeID&;

            const_iterator() = default;
            explicit const_iterator(const NodeID* value) : position(value) {}
            explicit const_iterator(Tree::const_iterator value) : position(value) {}
            reference operator*() const {
                return std::visit([](const auto& it) -> reference { return *it; }, position);
            }
            pointer operator->() const { return &**this; }
            const_iterator& operator++() {
                std::visit([](auto& it) { ++it; }, position);
                return *this;
            }
            const_iterator operator++(int) {
                auto old = *this;
                ++*this;
                return old;
            }
            bool operator==(const const_iterator& other) const { return position == other.position; }
            bool operator!=(const const_iterator& other) const { return !(*this == other); }
        };

        bool empty() const { return size() == 0; }
        size_t size() const {
            const auto* expanded = tree();
            return expanded ? expanded->size() : smallSize;
        }
        size_t count(NodeID id) const {
            if (const auto* expanded = tree()) return expanded->count(id);
            const auto& small = std::get<Small>(storage);
            return std::binary_search(small.begin(), small.begin() + smallSize, id);
        }
        const_iterator begin() const {
            if (const auto* expanded = tree()) return const_iterator(expanded->begin());
            return const_iterator(std::get<Small>(storage).data());
        }
        const_iterator end() const {
            if (const auto* expanded = tree()) return const_iterator(expanded->end());
            return const_iterator(std::get<Small>(storage).data() + smallSize);
        }
        bool insert(NodeID id) {
            if (auto* expanded = std::get_if<std::unique_ptr<Tree>>(&storage))
                return (*expanded)->insert(id).second;
            auto& small = std::get<Small>(storage);
            auto end = small.begin() + smallSize;
            auto position = std::lower_bound(small.begin(), end, id);
            if (position != end && *position == id) return false;
            if (smallSize < inlineCapacity) {
                std::move_backward(position, end, end + 1);
                *position = id;
                ++smallSize;
            } else {
                auto expanded = std::make_unique<Tree>(small.begin(), end);
                expanded->insert(id);
                storage = std::move(expanded);
                smallSize = 0;
            }
            return true;
        }
        bool erase(NodeID id) {
            if (auto* expanded = std::get_if<std::unique_ptr<Tree>>(&storage))
                return (*expanded)->erase(id) != 0;
            auto& small = std::get<Small>(storage);
            auto end = small.begin() + smallSize;
            auto position = std::lower_bound(small.begin(), end, id);
            if (position == end || *position != id) return false;
            std::move(position + 1, end, position);
            --smallSize;
            return true;
        }
        void clear() {
            storage.emplace<Small>();
            smallSize = 0;
        }
    };
    struct Node {
        Adjacency incoming, outgoing;
    };

    NodeID newNode() {
        assert(nodes.size() < std::numeric_limits<NodeID>::max());
        const NodeID id = nodes.size();
        nodes.emplace_back();
        live.push_back(true);
        return id;
    }
    bool hasNode(NodeID id) const { return id < nodes.size() && live[id]; }
    /// newNode() may invalidate node pointers; adjacency mutations invalidate iterators.
    const Node* getNode(NodeID id) const {
        assert(hasNode(id));
        return &nodes[id];
    }
    bool addCopy(NodeID src, NodeID dst) {
        assert(hasNode(src) && hasNode(dst));
        if (src == dst || !nodes[src].outgoing.insert(dst)) return false;
        nodes[dst].incoming.insert(src);
        ++copies;
        return true;
    }
    bool removeCopy(NodeID src, NodeID dst) {
        assert(hasNode(src) && hasNode(dst));
        if (!nodes[src].outgoing.erase(dst)) return false;
        [[maybe_unused]] const bool removed = nodes[dst].incoming.erase(src);
        assert(removed);
        --copies;
        return true;
    }
    /// Report and remove all incident edges. The callback must not mutate this graph.
    template<class Emit>
    size_t detachNode(NodeID id, Emit&& emit) {
        assert(hasNode(id));
        auto& node = nodes[id];
        const size_t removed = node.outgoing.size() + node.incoming.size();
        for (NodeID dst : node.outgoing) {
            [[maybe_unused]] const bool erased = nodes[dst].incoming.erase(id);
            assert(erased);
            emit(id, dst);
        }
        for (NodeID src : node.incoming) {
            [[maybe_unused]] const bool erased = nodes[src].outgoing.erase(id);
            assert(erased);
            emit(src, id);
        }
        node.outgoing.clear();
        node.incoming.clear();
        copies -= removed;
        return removed;
    }
    void removeNode(NodeID id) {
        assert(hasNode(id));
        assert(nodes[id].incoming.empty() && nodes[id].outgoing.empty());
        nodes[id].incoming.clear();
        nodes[id].outgoing.clear();
        live[id] = false;
    }
    size_t copyCount() const { return copies; }

private:
    // Retired IDs are not reused. Their adjacency allocations are released.
    std::vector<Node> nodes;
    std::vector<bool> live;
    size_t copies = 0;
};
}
#endif
