#include "Graphs/VDG.h"
#include <iostream>
#include <map>
#include <set>

using namespace SVF;

namespace
{
void buildGraph(VDG& graph)
{
    VDG::setSolvePhaseStarted(false);
    for (Version v = 1; v <= 4; ++v)
        graph.getOrAddNode(v, v == 4, v == 1);

    // Tarjan starts at 1, but {2,3} must survive the union-by-size merge.
    graph.mergeVersionsIntoRep(NodeVector{3}, 2);
    graph.addSolidEdge(1, 2);
    graph.addSolidEdge(2, 1);
    graph.addSolidEdge(2, 4);
}

bool checkPropagation(bool factsAtSurvivor)
{
    VDG graph(7);
    buildGraph(graph);
    graph.enterSolve();

    std::map<Version, std::set<unsigned>> pointsTo;
    pointsTo[factsAtSurvivor ? 2 : 1].insert(42);
    graph.markVersionUpdated(1);
    bool loadNotified = false;
    graph.propagateInTopoOrder(
        [&](Version src, Version dst)
        {
            const auto previousSize = pointsTo[dst].size();
            pointsTo[dst].insert(pointsTo[src].begin(), pointsTo[src].end());
            if (!graph.isSuperVersion(src))
                pointsTo[src].clear();
            return pointsTo[dst].size() != previousSize;
        },
        [&](Version v)
        {
            if (v == 4)
                loadNotified = true;
        });

    return graph.getRepVersion(1) == 2
        && pointsTo[4] == std::set<unsigned>{42}
        && pointsTo[1].empty()
        && loadNotified
        && !graph.hasPendingUpdates();
}
}

int main()
{
    VDG graph(7);
    buildGraph(graph);
    if (graph.sccMergeSolidEdges(NodeVector{1}) != NodeVector{2, 4})
    {
        std::cerr << "SCC topological order must contain the surviving representative\n";
        return 1;
    }
    if (!checkPropagation(false) || !checkPropagation(true))
    {
        std::cerr << "SCC facts must reach and notify the downstream load\n";
        return 1;
    }
    return 0;
}
