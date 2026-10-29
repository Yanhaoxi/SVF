#ifndef SVF_LOPA_COPY_SOLVER_H
#define SVF_LOPA_COPY_SOLVER_H

#include "Graphs/PUSGraph.h"

namespace SVF {
class LOPA;

/// A PUS Copy round: find reachable SCCs, merge cycles, propagate in DAG order.
/// Graph traversal is independent of SVF statements. The backend owns facts,
/// representatives and watchers, which mergeComponent updates together.
class LOPACopySolver {
public:
    struct Statistics {
        uint64_t visits = 0, merged = 0, sccMerges = 0, maxSCCMembers = 0;
        uint64_t sccEdgesTouched = 0, sccEdgesRebuilt = 0, sccEdgesRemoved = 0;
        double sccTime = 0, mergeTime = 0, copyTime = 0;
    };
    void solve(LOPA& backend);
    const Statistics& statistics() const { return stats; }
    bool isPropagating() const { return propagating; }
private:
    struct Components {
        std::vector<NodeID> members, visited;
        std::vector<std::pair<size_t, size_t>> ranges;
    };
    using EdgeList = std::vector<std::pair<NodeID, NodeID>>;
    using Iterator = PUSConstraintGraph::Adjacency::const_iterator;
    struct Frame { NodeID id; Iterator it, end; };
    const Components& findComponents(const PUSConstraintGraph& graph, const NodeBS& roots);
    uint64_t detachEdges(LOPA& backend, NodeID node, EdgeList& replacements);
    void mergeFacts(LOPA& backend, NodeID root, NodeID member);
    uint64_t rebuildEdges(LOPA& backend, EdgeList& edges);
    void mergeComponent(LOPA& backend, const NodeID* begin, const NodeID* end);
    void mergeCycles(LOPA& backend, const Components& components);
    void propagateCopies(LOPA& backend, const Components& components);
    std::vector<unsigned> index, low;
    std::vector<bool> active;
    Components components;
    std::vector<NodeID> stack;
    std::vector<Frame> dfs;
    EdgeList replacements;
    bool propagating = false;
    Statistics stats;
};
} // namespace SVF
#endif
