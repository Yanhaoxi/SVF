// Profiling's graph helpers are private to this translation unit. Include the
// implementation so this regression exercises the same insertion and rewrites
// as -vdg-pass-profile, without constructing a whole SVFG.
#include "../../svf/lib/WPA/LOPA/Profiling.cpp"
#include <iostream>

using namespace SVF;

namespace
{
bool checkSelfLoop(bool virtualLoop)
{
    ProfileGraph profile;
    profile.nodes[1].storeYield = true;
    profile.nodes[2];
    profile.nodes[3].loadConsume = true;
    profile.nodes[4]; // An isolated raw endpoint must still count as a node.

    VDG::setSolvePhaseStarted(false);
    VDG real(7);
    for (Version v = 1; v <= 4; ++v)
        real.getOrAddNode(v, v == 3, v == 1);

    // A store-to-load diamond with a self-loop on the relay. If the loop is
    // retained, every node in the diamond has two incident edges on the side
    // needed for contraction, and the profiling graph incorrectly stays at 3.
    for (const auto &e : std::vector<std::pair<Version, Version>>{{1, 2}, {2, 3}, {1, 3}})
    {
        insertProfileEdge(profile, e.first, e.second, false);
        real.addEdge(e.first, e.second, false);
    }
    const bool acceptedRelay = insertProfileEdge(profile, 2, 2, virtualLoop);
    const bool acceptedIsolated = insertProfileEdge(profile, 4, 4, virtualLoop);
    real.addEdge(2, 2, virtualLoop);
    real.addEdge(4, 4, virtualLoop);
    if (acceptedRelay || acceptedIsolated || profile.nodes.size() != 4)
        return false;

    for (char pass : std::string("SPC"))
        applyProfilePass(profile, pass);
    real.sccMergeSolidEdges();
    real.pruneUnreachableToLoadConsume();
    real.pruneUnreachableFromStoreYield();
    real.chainContraction();

    size_t realEdges = 0;
    bool realFlags = false;
    real.forEachSuperNode([&](Version, VDGNode *node)
    {
        realEdges += node->getSolidOut().size() + node->getVirtualOut().size();
        realFlags = node->isStoreYield() && node->isLoadConsume();
    });
    return profile.nodes.size() == 1 && real.getTotalNodeNum() == 1
        && countSolidEdges(profile) == 0 && countVirtualEdges(profile) == 0
        && profile.nodes.begin()->second.storeYield
        && profile.nodes.begin()->second.loadConsume
        && realEdges == 0 && realFlags;
}
}

int main()
{
    if (!checkSelfLoop(false) || !checkSelfLoop(true))
    {
        std::cerr << "Profiling self-loops block contraction or change the raw node population\n";
        return 1;
    }
    return 0;
}
