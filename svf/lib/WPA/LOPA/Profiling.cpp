//===- Profiling.cpp -- VDG pass-pattern profiling for LOPA ---------------//

#include "Util/GeneralType.h"
#include "WPA/Andersen.h"
#include "WPA/LOPA.h"
#include "Util/Options.h"
#include "MemoryModel/PointsTo.h"
#include <algorithm>
#include <array>
#include <cassert>
#include <cctype>
#include <chrono>
#include <cstddef>
#include <cstdlib>
#include <functional>
#include <limits>
#include <memory>
#include <queue>
#include <random>
#include <string>
#include <utility>
#include <vector>

using namespace SVF;

namespace SVF
{
namespace
{
    enum class VDGProfileSVFGTy : u8_t
    {
        Addr = 0,
        Copy = 1,
        Gep = 2,
        Load = 3,
        Store = 4,
        Phi = 5,
        ActualParm = 6,
        FormalParm = 7,
        ActualRet = 8,
        FormalRet = 9,
        ActualIn = 10,
        ActualOut = 11,
        FormalIn = 12,
        FormalOut = 13,
        MSSAPhi = 14,
        DummyVersionProp = 15,
        Other = 16,
        Count = 17
    };

    static constexpr size_t kVDGProfileSVFGTyCount = static_cast<size_t>(VDGProfileSVFGTy::Count);
    using VDGTypeCountArray = std::array<u64_t, kVDGProfileSVFGTyCount>;

    enum class ProfileNodeRole : u8_t
    {
        Normal = 0,
        StoreConsume = 1,
        StoreYield = 2
    };

    using ProfileKey = u64_t;

    struct ProfileNode
    {
        VDGProfileSVFGTy svfgTy = VDGProfileSVFGTy::Other;
        bool loadConsume = false;
        bool storeYield = false;
        u32_t classSize = 1;   // number of original N0 nodes merged into this rep
        Set<ProfileKey> solidOut;
        Set<ProfileKey> solidIn;
        Set<ProfileKey> virtualOut;
        Set<ProfileKey> virtualIn;
    };

    struct ProfileGraph
    {
        Map<ProfileKey, ProfileNode> nodes;
    };

    inline ProfileKey makeProfileKey(const NodeID stmtId, const ProfileNodeRole role)
    {
        return (static_cast<ProfileKey>(stmtId) << 2) | static_cast<ProfileKey>(role);
    }

    inline NodeID getStmtIdFromProfileKey(const ProfileKey key)
    {
        return static_cast<NodeID>(key >> 2);
    }

    inline ProfileNodeRole getRoleFromProfileKey(const ProfileKey key)
    {
        return static_cast<ProfileNodeRole>(key & static_cast<ProfileKey>(0x3));
    }

    inline size_t svfgTyIndex(const VDGProfileSVFGTy ty)
    {
        return static_cast<size_t>(ty);
    }

    inline const char* svfgTyName(const VDGProfileSVFGTy ty)
    {
        switch (ty)
        {
        case VDGProfileSVFGTy::Addr:
            return "Addr";
        case VDGProfileSVFGTy::Copy:
            return "Copy";
        case VDGProfileSVFGTy::Gep:
            return "Gep";
        case VDGProfileSVFGTy::Load:
            return "Load";
        case VDGProfileSVFGTy::Store:
            return "Store";
        case VDGProfileSVFGTy::Phi:
            return "Phi";
        case VDGProfileSVFGTy::ActualParm:
            return "ActualParm";
        case VDGProfileSVFGTy::FormalParm:
            return "FormalParm";
        case VDGProfileSVFGTy::ActualRet:
            return "ActualRet";
        case VDGProfileSVFGTy::FormalRet:
            return "FormalRet";
        case VDGProfileSVFGTy::ActualIn:
            return "ActualIn";
        case VDGProfileSVFGTy::ActualOut:
            return "ActualOut";
        case VDGProfileSVFGTy::FormalIn:
            return "FormalIn";
        case VDGProfileSVFGTy::FormalOut:
            return "FormalOut";
        case VDGProfileSVFGTy::MSSAPhi:
            return "MSSAPhi";
        case VDGProfileSVFGTy::DummyVersionProp:
            return "DummyVersionProp";
        case VDGProfileSVFGTy::Other:
            return "Other";
        default:
            return "Unknown";
        }
    }

    inline VDGProfileSVFGTy classifySVFGNodeType(const SVFGNode *node)
    {
        if (node == nullptr) return VDGProfileSVFGTy::Other;
        if (SVFUtil::isa<AddrSVFGNode>(node)) return VDGProfileSVFGTy::Addr;
        if (SVFUtil::isa<LoadSVFGNode>(node)) return VDGProfileSVFGTy::Load;
        if (SVFUtil::isa<StoreSVFGNode>(node)) return VDGProfileSVFGTy::Store;
        if (SVFUtil::isa<GepSVFGNode>(node)) return VDGProfileSVFGTy::Gep;
        if (SVFUtil::isa<PHISVFGNode>(node)) return VDGProfileSVFGTy::Phi;
        if (SVFUtil::isa<ActualParmSVFGNode>(node)) return VDGProfileSVFGTy::ActualParm;
        if (SVFUtil::isa<FormalParmSVFGNode>(node)) return VDGProfileSVFGTy::FormalParm;
        if (SVFUtil::isa<ActualRetSVFGNode>(node)) return VDGProfileSVFGTy::ActualRet;
        if (SVFUtil::isa<FormalRetSVFGNode>(node)) return VDGProfileSVFGTy::FormalRet;
        if (SVFUtil::isa<ActualINSVFGNode>(node)) return VDGProfileSVFGTy::ActualIn;
        if (SVFUtil::isa<ActualOUTSVFGNode>(node)) return VDGProfileSVFGTy::ActualOut;
        if (SVFUtil::isa<FormalINSVFGNode>(node)) return VDGProfileSVFGTy::FormalIn;
        if (SVFUtil::isa<FormalOUTSVFGNode>(node)) return VDGProfileSVFGTy::FormalOut;
        if (SVFUtil::isa<MSSAPHISVFGNode>(node)) return VDGProfileSVFGTy::MSSAPhi;
        if (SVFUtil::isa<DummyVersionPropSVFGNode>(node)) return VDGProfileSVFGTy::DummyVersionProp;
        if (SVFUtil::isa<CopySVFGNode>(node)) return VDGProfileSVFGTy::Copy;
        return VDGProfileSVFGTy::Other;
    }

    inline bool isLoadConsumeRole(const SVFGNode *stmtNode, const ProfileNodeRole role)
    {
        return role == ProfileNodeRole::Normal && SVFUtil::isa<LoadSVFGNode>(stmtNode);
    }

    inline bool isStoreYieldRole(const ProfileNodeRole role)
    {
        return role == ProfileNodeRole::StoreYield;
    }

    std::string buildSVFGTypePatternKey(const VDGTypeCountArray &typeCounts)
    {
        std::string key;
        for (size_t i = 0; i < kVDGProfileSVFGTyCount; ++i)
        {
            const u64_t cnt = typeCounts[i];
            if (cnt == 0)
                continue;
            if (!key.empty())
                key += "|";
            key += svfgTyName(static_cast<VDGProfileSVFGTy>(i));
            key += ":";
            key += std::to_string(cnt);
        }
        if (key.empty())
            return "None";
        return key;
    }

    inline ProfileNode &getOrCreateProfileNode(ProfileGraph &graph, const ProfileKey key, const SVFG *svfg)
    {
        ProfileNode &node = graph.nodes[key];
        const NodeID stmtId = getStmtIdFromProfileKey(key);
        const ProfileNodeRole role = getRoleFromProfileKey(key);
        const SVFGNode *stmtNode = svfg->getSVFGNode(stmtId);
        node.svfgTy = classifySVFGNodeType(stmtNode);
        node.loadConsume = node.loadConsume || isLoadConsumeRole(stmtNode, role);
        node.storeYield = node.storeYield || isStoreYieldRole(role);
        return node;
    }

    inline bool insertProfileEdge(ProfileGraph &graph,
                                  const ProfileKey src,
                                  const ProfileKey dst,
                                  const bool isVirtual)
    {
        // Match VDG::addEdge: self-loops do not represent a dependence between
        // distinct states. Counting them in the degrees can block ChainFwd/Bwd.
        if (src == dst)
            return false;
        ProfileNode &srcNode = graph.nodes.at(src);
        ProfileNode &dstNode = graph.nodes.at(dst);
        bool inserted = false;
        if (isVirtual)
        {
            // must \sqcup may = must: a may edge never coexists with a must edge
            // between the same endpoints.
            if (srcNode.solidOut.find(dst) != srcNode.solidOut.end())
                return false;
            inserted = srcNode.virtualOut.insert(dst).second;
            dstNode.virtualIn.insert(src);
        }
        else
        {
            // A must edge subsumes an existing may edge between the same endpoints.
            srcNode.virtualOut.erase(dst);
            dstNode.virtualIn.erase(src);
            inserted = srcNode.solidOut.insert(dst).second;
            dstNode.solidIn.insert(src);
        }
        return inserted;
    }

    inline bool addProfileEdge(ProfileGraph &graph,
                               const ProfileKey src,
                               const ProfileKey dst,
                               const bool isVirtual,
                               const SVFG *svfg)
    {
        // Preserve the raw node population, including isolated endpoints.
        getOrCreateProfileNode(graph, src, svfg);
        getOrCreateProfileNode(graph, dst, svfg);
        return insertProfileEdge(graph, src, dst, isVirtual);
    }

    void printSortedPatternCounts(const std::string &prefix,
                                  const Map<std::string, u64_t> &counts,
                                  const size_t limit = 0,
                                  const std::string &tag = "")
    {
        std::vector<std::pair<std::string, u64_t>> ordered(counts.begin(), counts.end());
        std::sort(ordered.begin(), ordered.end(),
                  [](const std::pair<std::string, u64_t> &lhs, const std::pair<std::string, u64_t> &rhs)
        {
            if (lhs.second != rhs.second)
                return lhs.second > rhs.second;
            return lhs.first < rhs.first;
        });

        const size_t maxPrint = (limit == 0) ? ordered.size() : std::min(limit, ordered.size());
        for (size_t i = 0; i < maxPrint; ++i)
        {
            SVFUtil::outs()
                << prefix
                << tag
                << "\tidx:" << i
                << " pattern:" << ordered[i].first
                << " count:" << ordered[i].second
                << "\n";
        }
        if (maxPrint < ordered.size())
        {
            SVFUtil::outs()
                << prefix
                << tag
                << "\ttruncated:" << (ordered.size() - maxPrint)
                << "\n";
        }
    }

    struct VDGPassProfileAggregate
    {
        u64_t graphs = 0;
        u64_t nodeMapObjects = 0;
        u64_t nodeMapEntries = 0;
        u64_t solidEdges = 0;
        u64_t virtualEdges = 0;

        u64_t forwardPairs = 0;
        u64_t backwardPairs = 0;
        u64_t bothForwardBackwardPairs = 0;
        Map<std::string, u64_t> forwardPatterns;
        Map<std::string, u64_t> backwardPatterns;

        // Node-type composition (relay vs protected endpoints).
        VDGTypeCountArray typeCounts{};
        VDGTypeCountArray typeCountsNormal{};
        VDGTypeCountArray typeCountsConsume{};
        VDGTypeCountArray typeCountsYield{};
        VDGTypeCountArray chainFwdTypeCounts{};
        VDGTypeCountArray chainBwdTypeCounts{};
        VDGTypeCountArray chainBwdConsumeTypeCounts{};
        u64_t storeYieldNodes = 0;
        u64_t loadConsumeNodes = 0;
        u64_t relayNodes = 0;

        u64_t sccCount = 0;
        u64_t sccTotalNodes = 0;
        u64_t sccNonTrivialCount = 0;
        u64_t sccNonTrivialNodes = 0;
        u64_t sccMaxSize = 0;
        Map<std::string, u64_t> sccPatternCounts;

        u64_t storeReachableNodes = 0;
        u64_t loadReverseReachableNodes = 0;
        u64_t bothReachableNodes = 0;
    };

    void profileVDGObjectForPassPatterns(const ProfileGraph &graph, VDGPassProfileAggregate &agg)
    {
        if (graph.nodes.empty())
            return;

        ++agg.graphs;
        ++agg.nodeMapObjects;
        agg.nodeMapEntries += static_cast<u64_t>(graph.nodes.size());

        for (const auto &kn : graph.nodes)
        {
            const ProfileNode &node = kn.second;
            agg.solidEdges += static_cast<u64_t>(node.solidOut.size());
            agg.virtualEdges += static_cast<u64_t>(node.virtualOut.size());

            const size_t tyIdx = svfgTyIndex(node.svfgTy);
            ++agg.typeCounts[tyIdx];
            const ProfileNodeRole nodeRole = getRoleFromProfileKey(kn.first);
            if (nodeRole == ProfileNodeRole::StoreConsume)
                ++agg.typeCountsConsume[tyIdx];
            else if (nodeRole == ProfileNodeRole::StoreYield)
                ++agg.typeCountsYield[tyIdx];
            else
                ++agg.typeCountsNormal[tyIdx];
            if (node.storeYield)
                ++agg.storeYieldNodes;
            else if (node.loadConsume)
                ++agg.loadConsumeNodes;
            else
                ++agg.relayNodes;

            bool forwardMatched = false;
            if (node.solidOut.size() == 1 && node.virtualOut.empty() && !node.loadConsume)
            {
                const ProfileKey dst = *node.solidOut.begin();
                const auto dstIt = graph.nodes.find(dst);
                if (dstIt != graph.nodes.end())
                {
                    const std::string key = std::string(svfgTyName(node.svfgTy))
                                          + "->" + svfgTyName(dstIt->second.svfgTy);
                    ++agg.forwardPatterns[key];
                    ++agg.forwardPairs;
                    ++agg.chainFwdTypeCounts[tyIdx];
                    forwardMatched = true;
                }
            }

            bool backwardMatched = false;
            if (node.solidIn.size() == 1 && node.virtualIn.empty() && !node.storeYield)
            {
                const ProfileKey src = *node.solidIn.begin();
                const auto srcIt = graph.nodes.find(src);
                if (srcIt != graph.nodes.end())
                {
                    const std::string key = std::string(svfgTyName(srcIt->second.svfgTy))
                                          + "->" + svfgTyName(node.svfgTy);
                    ++agg.backwardPatterns[key];
                    ++agg.backwardPairs;
                    ++agg.chainBwdTypeCounts[tyIdx];
                    if (nodeRole == ProfileNodeRole::StoreConsume)
                        ++agg.chainBwdConsumeTypeCounts[tyIdx];
                    backwardMatched = true;
                }
            }

            if (forwardMatched && backwardMatched)
                ++agg.bothForwardBackwardPairs;
        }

        // Tarjan SCC on solid edges.
        Map<ProfileKey, u64_t> index;
        Map<ProfileKey, u64_t> lowlink;
        Set<ProfileKey> onStack;
        std::vector<ProfileKey> stack;
        u64_t nextIndex = 1;

        std::function<void(ProfileKey)> strongConnect = [&](ProfileKey v)
        {
            index[v] = nextIndex;
            lowlink[v] = nextIndex;
            ++nextIndex;
            stack.push_back(v);
            onStack.insert(v);

            const auto vIt = graph.nodes.find(v);
            if (vIt != graph.nodes.end())
            {
                for (const ProfileKey w : vIt->second.solidOut)
                {
                    if (graph.nodes.find(w) == graph.nodes.end())
                        continue;

                    if (index.find(w) == index.end())
                    {
                        strongConnect(w);
                        lowlink[v] = std::min(lowlink[v], lowlink[w]);
                    }
                    else if (onStack.find(w) != onStack.end())
                    {
                        lowlink[v] = std::min(lowlink[v], index[w]);
                    }
                }
            }

            if (lowlink[v] == index[v])
            {
                VDGTypeCountArray kindCnt{};
                u64_t sccSize = 0;
                while (!stack.empty())
                {
                    const ProfileKey w = stack.back();
                    stack.pop_back();
                    onStack.erase(w);
                    ++sccSize;
                    const auto wIt = graph.nodes.find(w);
                    if (wIt != graph.nodes.end())
                        ++kindCnt[svfgTyIndex(wIt->second.svfgTy)];
                    if (w == v)
                        break;
                }

                ++agg.sccCount;
                agg.sccTotalNodes += sccSize;
                if (sccSize > 1)
                {
                    ++agg.sccNonTrivialCount;
                    agg.sccNonTrivialNodes += sccSize;
                }
                if (sccSize > agg.sccMaxSize)
                    agg.sccMaxSize = sccSize;
                ++agg.sccPatternCounts[buildSVFGTypePatternKey(kindCnt)];
            }
        };

        for (const auto &kn : graph.nodes)
        {
            const ProfileKey v = kn.first;
            if (index.find(v) == index.end())
                strongConnect(v);
        }

        // Step5: reachability ratios over both solid and virtual edges.
        Set<ProfileKey> storeSeen;
        std::queue<ProfileKey> storeQ;
        for (const auto &kn : graph.nodes)
        {
            if (!kn.second.storeYield)
                continue;
            if (storeSeen.insert(kn.first).second)
                storeQ.push(kn.first);
        }
        while (!storeQ.empty())
        {
            const ProfileKey cur = storeQ.front();
            storeQ.pop();
            const auto curIt = graph.nodes.find(cur);
            if (curIt == graph.nodes.end())
                continue;
            for (const ProfileKey dst : curIt->second.solidOut)
            {
                if (graph.nodes.find(dst) == graph.nodes.end())
                    continue;
                if (storeSeen.insert(dst).second)
                    storeQ.push(dst);
            }
            for (const ProfileKey dst : curIt->second.virtualOut)
            {
                if (graph.nodes.find(dst) == graph.nodes.end())
                    continue;
                if (storeSeen.insert(dst).second)
                    storeQ.push(dst);
            }
        }
        agg.storeReachableNodes += static_cast<u64_t>(storeSeen.size());

        Set<ProfileKey> loadRevSeen;
        std::queue<ProfileKey> loadRevQ;
        for (const auto &kn : graph.nodes)
        {
            if (!kn.second.loadConsume)
                continue;
            if (loadRevSeen.insert(kn.first).second)
                loadRevQ.push(kn.first);
        }
        while (!loadRevQ.empty())
        {
            const ProfileKey cur = loadRevQ.front();
            loadRevQ.pop();
            const auto curIt = graph.nodes.find(cur);
            if (curIt == graph.nodes.end())
                continue;
            for (const ProfileKey src : curIt->second.solidIn)
            {
                if (graph.nodes.find(src) == graph.nodes.end())
                    continue;
                if (loadRevSeen.insert(src).second)
                    loadRevQ.push(src);
            }
            for (const ProfileKey src : curIt->second.virtualIn)
            {
                if (graph.nodes.find(src) == graph.nodes.end())
                    continue;
                if (loadRevSeen.insert(src).second)
                    loadRevQ.push(src);
            }
        }
        agg.loadReverseReachableNodes += static_cast<u64_t>(loadRevSeen.size());

        u64_t bothReachable = 0;
        if (storeSeen.size() <= loadRevSeen.size())
        {
            for (const ProfileKey key : storeSeen)
            {
                if (loadRevSeen.find(key) != loadRevSeen.end())
                    ++bothReachable;
            }
        }
        else
        {
            for (const ProfileKey key : loadRevSeen)
            {
                if (storeSeen.find(key) != storeSeen.end())
                    ++bothReachable;
            }
        }
        agg.bothReachableNodes += bothReachable;
    }

    void dumpVDGPassProfile(const VDGPassProfileAggregate &agg, const std::string &tag = "")
    {
        const u64_t solidSolidVirtualDen = agg.solidEdges + agg.virtualEdges;
        const double step2Ratio = solidSolidVirtualDen == 0
                                ? 0.0
                                : static_cast<double>(agg.forwardPairs)
                                / static_cast<double>(solidSolidVirtualDen);
        const double step3Ratio = solidSolidVirtualDen == 0
                                ? 0.0
                                : static_cast<double>(agg.backwardPairs)
                                / static_cast<double>(solidSolidVirtualDen);
        const double bothForwardBackwardRatio = solidSolidVirtualDen == 0
                                              ? 0.0
                                              : static_cast<double>(agg.bothForwardBackwardPairs)
                                              / static_cast<double>(solidSolidVirtualDen);

        SVFUtil::outs()
            << "vdg.passprofile.step1.summary" << tag << "\tgraphs:" << agg.graphs
            << " nodeMapObjects:" << agg.nodeMapObjects
            << " nodeMapEntries:" << agg.nodeMapEntries
            << " solidEdges:" << agg.solidEdges
            << " virtualEdges:" << agg.virtualEdges
            << "\n";

        SVFUtil::outs()
            << "vdg.passprofile.type.summary" << tag
            << "\tnodes:" << agg.nodeMapEntries
            << " storeYield:" << agg.storeYieldNodes
            << " loadConsume:" << agg.loadConsumeNodes
            << " relay:" << agg.relayNodes
            << "\n";
        for (size_t i = 0; i < kVDGProfileSVFGTyCount; ++i)
        {
            if (agg.typeCounts[i] == 0)
                continue;
            SVFUtil::outs()
                << "vdg.passprofile.type.node" << tag
                << "\ttype:" << svfgTyName(static_cast<VDGProfileSVFGTy>(i))
                << " nodes:" << agg.typeCounts[i]
                << " normal:" << agg.typeCountsNormal[i]
                << " consume:" << agg.typeCountsConsume[i]
                << " yield:" << agg.typeCountsYield[i]
                << " chainFwd:" << agg.chainFwdTypeCounts[i]
                << " chainBwd:" << agg.chainBwdTypeCounts[i]
                << " chainBwdConsume:" << agg.chainBwdConsumeTypeCounts[i]
                << "\n";
        }

        SVFUtil::outs()
            << "vdg.passprofile.step2.summary" << tag << "\tpairs:" << agg.forwardPairs
            << " ratio:" << step2Ratio
            << " patternKinds:" << agg.forwardPatterns.size()
            << "\n";
        printSortedPatternCounts("vdg.passprofile.step2.pattern", agg.forwardPatterns, 0, tag);

        SVFUtil::outs()
            << "vdg.passprofile.step3.summary" << tag << "\tpairs:" << agg.backwardPairs
            << " ratio:" << step3Ratio
            << " patternKinds:" << agg.backwardPatterns.size()
            << "\n";
        printSortedPatternCounts("vdg.passprofile.step3.pattern", agg.backwardPatterns, 0, tag);

        SVFUtil::outs()
            << "vdg.passprofile.step23.summary" << tag << "\tbothPairs:" << agg.bothForwardBackwardPairs
            << " solidSolidVirtual:" << solidSolidVirtualDen
            << " ratio:" << bothForwardBackwardRatio
            << "\n";

        SVFUtil::outs()
            << "vdg.passprofile.step4.summary" << tag << "\tsccCount:" << agg.sccCount
            << " sccTotalNodes:" << agg.sccTotalNodes
            << " nonTrivialSccCount:" << agg.sccNonTrivialCount
            << " nonTrivialSccNodes:" << agg.sccNonTrivialNodes
            << " sccMaxSize:" << agg.sccMaxSize
            << " patternKinds:" << agg.sccPatternCounts.size()
            << "\n";
        printSortedPatternCounts("vdg.passprofile.step4.pattern", agg.sccPatternCounts, 20, tag);

        const double storeReachRatio = agg.nodeMapEntries == 0
                                     ? 0.0
                                     : static_cast<double>(agg.storeReachableNodes) / static_cast<double>(agg.nodeMapEntries);
        const double loadRevReachRatio = agg.nodeMapEntries == 0
                                       ? 0.0
                                       : static_cast<double>(agg.loadReverseReachableNodes) / static_cast<double>(agg.nodeMapEntries);
        const double bothReachRatio = agg.nodeMapEntries == 0
                                    ? 0.0
                                    : static_cast<double>(agg.bothReachableNodes) / static_cast<double>(agg.nodeMapEntries);
        SVFUtil::outs()
            << "vdg.passprofile.step5.summary" << tag << "\tstoreReachable:" << agg.storeReachableNodes
            << "/" << agg.nodeMapEntries
            << " ratio:" << storeReachRatio
            << " loadReverseReachable:" << agg.loadReverseReachableNodes
            << "/" << agg.nodeMapEntries
            << " ratio:" << loadRevReachRatio
            << " bothReachable:" << agg.bothReachableNodes
            << "/" << agg.nodeMapEntries
            << " ratio:" << bothReachRatio
            << "\n";
    }

    //===--------------------------------------------------------------------===//
    // Estimation-graph simplification.
    //
    // The profiling graph is a non-materialized estimate of the VDG. The helpers
    // below apply the same simplification predicates as the real VDG passes so
    // that -vdg-pass-profile can report the *applied* effect of a strategy on the
    // estimate (N0 -> N1) alongside opportunity coverage.
    //===--------------------------------------------------------------------===//

    inline u64_t countSolidEdges(const ProfileGraph &g)
    {
        u64_t n = 0;
        for (const auto &kn : g.nodes)
            n += static_cast<u64_t>(kn.second.solidOut.size());
        return n;
    }

    inline u64_t countVirtualEdges(const ProfileGraph &g)
    {
        u64_t n = 0;
        for (const auto &kn : g.nodes)
            n += static_cast<u64_t>(kn.second.virtualOut.size());
        return n;
    }

    // Nodes that are neither a load-consume nor a store-yield endpoint, i.e. the
    // relay/internal states that compression aims to quotient away.
    inline u64_t countPlainNodes(const ProfileGraph &g)
    {
        u64_t n = 0;
        for (const auto &kn : g.nodes)
        {
            if (!kn.second.loadConsume && !kn.second.storeYield)
                ++n;
        }
        return n;
    }

    void removeProfileNode(ProfileGraph &g, const ProfileKey key)
    {
        const auto it = g.nodes.find(key);
        if (it == g.nodes.end())
            return;
        const ProfileNode node = it->second;
        for (const ProfileKey dst : node.solidOut)
        {
            const auto d = g.nodes.find(dst);
            if (d != g.nodes.end())
                d->second.solidIn.erase(key);
        }
        for (const ProfileKey dst : node.virtualOut)
        {
            const auto d = g.nodes.find(dst);
            if (d != g.nodes.end())
                d->second.virtualIn.erase(key);
        }
        for (const ProfileKey src : node.solidIn)
        {
            const auto s = g.nodes.find(src);
            if (s != g.nodes.end())
                s->second.solidOut.erase(key);
        }
        for (const ProfileKey src : node.virtualIn)
        {
            const auto s = g.nodes.find(src);
            if (s != g.nodes.end())
                s->second.virtualOut.erase(key);
        }
        g.nodes.erase(it);
    }

    void mergeProfileNodesIntoRep(ProfileGraph &g, const std::vector<ProfileKey> &members, const ProfileKey rep)
    {
        auto repIt = g.nodes.find(rep);
        if (repIt == g.nodes.end())
            return;
        ProfileNode &repNode = repIt->second;
        for (const ProfileKey m : members)
        {
            if (m == rep)
                continue;
            const auto it = g.nodes.find(m);
            if (it == g.nodes.end())
                continue;
            const ProfileNode mn = it->second;
            repNode.loadConsume = repNode.loadConsume || mn.loadConsume;
            repNode.storeYield = repNode.storeYield || mn.storeYield;
            repNode.classSize += mn.classSize;

            for (const ProfileKey dst : mn.solidOut)
            {
                const ProfileKey nd = (dst == m) ? rep : dst;
                if (nd == rep)
                    continue;
                repNode.solidOut.insert(nd);
                repNode.virtualOut.erase(nd);
                const auto d = g.nodes.find(nd);
                if (d != g.nodes.end())
                {
                    d->second.solidIn.insert(rep);
                    d->second.virtualIn.erase(rep);
                }
            }
            for (const ProfileKey dst : mn.virtualOut)
            {
                const ProfileKey nd = (dst == m) ? rep : dst;
                if (nd == rep)
                    continue;
                // must \sqcup may = must: a must edge subsumes a may edge.
                if (repNode.solidOut.find(nd) != repNode.solidOut.end())
                    continue;
                repNode.virtualOut.insert(nd);
                const auto d = g.nodes.find(nd);
                if (d != g.nodes.end())
                    d->second.virtualIn.insert(rep);
            }
            for (const ProfileKey src : mn.solidIn)
            {
                const ProfileKey ns = (src == m) ? rep : src;
                if (ns == rep)
                    continue;
                const auto s = g.nodes.find(ns);
                if (s != g.nodes.end())
                {
                    s->second.solidOut.insert(rep);
                    s->second.virtualOut.erase(rep);
                }
                repNode.solidIn.insert(ns);
                repNode.virtualIn.erase(ns);
            }
            for (const ProfileKey src : mn.virtualIn)
            {
                const ProfileKey ns = (src == m) ? rep : src;
                if (ns == rep)
                    continue;
                // must \sqcup may = must: a must edge subsumes a may edge.
                if (repNode.solidIn.find(ns) != repNode.solidIn.end())
                    continue;
                const auto s = g.nodes.find(ns);
                if (s != g.nodes.end())
                    s->second.virtualOut.insert(rep);
                repNode.virtualIn.insert(ns);
            }
            for (const ProfileKey dst : mn.solidOut)
            {
                const auto d = g.nodes.find(dst);
                if (d != g.nodes.end())
                    d->second.solidIn.erase(m);
            }
            for (const ProfileKey dst : mn.virtualOut)
            {
                const auto d = g.nodes.find(dst);
                if (d != g.nodes.end())
                    d->second.virtualIn.erase(m);
            }
            for (const ProfileKey src : mn.solidIn)
            {
                const auto s = g.nodes.find(src);
                if (s != g.nodes.end())
                    s->second.solidOut.erase(m);
            }
            for (const ProfileKey src : mn.virtualIn)
            {
                const auto s = g.nodes.find(src);
                if (s != g.nodes.end())
                    s->second.virtualOut.erase(m);
            }
            g.nodes.erase(it);
        }
        repNode.solidOut.erase(rep);
        repNode.solidIn.erase(rep);
        repNode.virtualOut.erase(rep);
        repNode.virtualIn.erase(rep);
    }

    /// Mirrors VDG::sccMergeSolidEdges: merge every non-trivial solid SCC.
    void sccMergeProfileGraph(ProfileGraph &g)
    {
        Map<ProfileKey, u64_t> index;
        Map<ProfileKey, u64_t> lowlink;
        Set<ProfileKey> onStack;
        std::vector<ProfileKey> stack;
        std::vector<std::vector<ProfileKey>> sccs;
        u64_t nextIndex = 1;

        std::function<void(ProfileKey)> strongConnect = [&](const ProfileKey v)
        {
            index[v] = nextIndex;
            lowlink[v] = nextIndex;
            ++nextIndex;
            stack.push_back(v);
            onStack.insert(v);

            const auto vIt = g.nodes.find(v);
            if (vIt != g.nodes.end())
            {
                for (const ProfileKey w : vIt->second.solidOut)
                {
                    if (g.nodes.find(w) == g.nodes.end())
                        continue;
                    if (index.find(w) == index.end())
                    {
                        strongConnect(w);
                        lowlink[v] = std::min(lowlink[v], lowlink[w]);
                    }
                    else if (onStack.find(w) != onStack.end())
                    {
                        lowlink[v] = std::min(lowlink[v], index[w]);
                    }
                }
            }

            if (lowlink[v] == index[v])
            {
                std::vector<ProfileKey> scc;
                while (!stack.empty())
                {
                    const ProfileKey w = stack.back();
                    stack.pop_back();
                    onStack.erase(w);
                    scc.push_back(w);
                    if (w == v)
                        break;
                }
                if (scc.size() > 1)
                    sccs.push_back(std::move(scc));
            }
        };

        for (const auto &kn : g.nodes)
        {
            const ProfileKey v = kn.first;
            if (index.find(v) == index.end())
                strongConnect(v);
        }

        for (const std::vector<ProfileKey> &scc : sccs)
        {
            ProfileKey rep = scc.front();
            for (const ProfileKey v : scc)
                rep = std::min(rep, v);
            mergeProfileNodesIntoRep(g, scc, rep);
        }
    }

    /// Mirrors VDG::pruneUnreachableToLoadConsume + pruneUnreachableFromStoreYield.
    void pruneProfileGraph(ProfileGraph &g)
    {
        Set<ProfileKey> fromStore;
        std::queue<ProfileKey> storeQ;
        for (const auto &kn : g.nodes)
        {
            if (kn.second.storeYield && fromStore.insert(kn.first).second)
                storeQ.push(kn.first);
        }
        while (!storeQ.empty())
        {
            const ProfileKey v = storeQ.front();
            storeQ.pop();
            const auto it = g.nodes.find(v);
            if (it == g.nodes.end())
                continue;
            for (const ProfileKey dst : it->second.solidOut)
            {
                if (g.nodes.find(dst) != g.nodes.end() && fromStore.insert(dst).second)
                    storeQ.push(dst);
            }
            for (const ProfileKey dst : it->second.virtualOut)
            {
                if (g.nodes.find(dst) != g.nodes.end() && fromStore.insert(dst).second)
                    storeQ.push(dst);
            }
        }

        Set<ProfileKey> toLoad;
        std::queue<ProfileKey> loadQ;
        for (const auto &kn : g.nodes)
        {
            if (kn.second.loadConsume && toLoad.insert(kn.first).second)
                loadQ.push(kn.first);
        }
        while (!loadQ.empty())
        {
            const ProfileKey v = loadQ.front();
            loadQ.pop();
            const auto it = g.nodes.find(v);
            if (it == g.nodes.end())
                continue;
            for (const ProfileKey src : it->second.solidIn)
            {
                if (g.nodes.find(src) != g.nodes.end() && toLoad.insert(src).second)
                    loadQ.push(src);
            }
            for (const ProfileKey src : it->second.virtualIn)
            {
                if (g.nodes.find(src) != g.nodes.end() && toLoad.insert(src).second)
                    loadQ.push(src);
            }
        }

        std::vector<ProfileKey> toRemove;
        for (const auto &kn : g.nodes)
        {
            if (fromStore.find(kn.first) == fromStore.end()
                || toLoad.find(kn.first) == toLoad.end())
                toRemove.push_back(kn.first);
        }
        for (const ProfileKey v : toRemove)
            removeProfileNode(g, v);
    }

    /// Mirrors VDG::chainContraction: contract single-solid-edge relay nodes.
    void chainContractProfileGraph(ProfileGraph &g)
    {
        Set<ProfileKey> inWorklist;
        std::vector<ProfileKey> worklist;
        auto enqueue = [&](const ProfileKey v)
        {
            if (g.nodes.find(v) == g.nodes.end())
                return;
            if (inWorklist.insert(v).second)
                worklist.push_back(v);
        };
        auto enqueueNeighbors = [&](const ProfileKey v)
        {
            const auto it = g.nodes.find(v);
            if (it == g.nodes.end())
                return;
            for (const ProfileKey src : it->second.solidIn)
                enqueue(src);
            for (const ProfileKey dst : it->second.solidOut)
                enqueue(dst);
        };

        {
            std::vector<ProfileKey> seedKeys;
            seedKeys.reserve(g.nodes.size());
            for (const auto &kn : g.nodes)
                seedKeys.push_back(kn.first);
            if (const char *shuffleSeed = std::getenv("LOPA_CHAIN_SHUFFLE"))
            {
                std::mt19937 rng(static_cast<std::mt19937::result_type>(
                    std::strtoul(shuffleSeed, nullptr, 10)));
                std::shuffle(seedKeys.begin(), seedKeys.end(), rng);
            }
            for (const ProfileKey key : seedKeys)
                enqueue(key);
        }

        while (!worklist.empty())
        {
            const ProfileKey v = worklist.back();
            worklist.pop_back();
            inWorklist.erase(v);
            if (g.nodes.find(v) == g.nodes.end())
                continue;

            bool merged = false;
            {
                const ProfileNode &vn = g.nodes.find(v)->second;
                if (!vn.loadConsume && vn.solidOut.size() == 1 && vn.virtualOut.empty())
                {
                    const ProfileKey y = *vn.solidOut.begin();
                    if (g.nodes.find(y) != g.nodes.end())
                    {
                        mergeProfileNodesIntoRep(g, std::vector<ProfileKey>{v}, y);
                        enqueueNeighbors(y);
                        enqueue(y);
                        merged = true;
                    }
                }
            }
            if (merged)
                continue;

            const auto mIt = g.nodes.find(v);
            if (mIt == g.nodes.end())
                continue;
            const ProfileNode &mn = mIt->second;
            if (!mn.storeYield && mn.solidIn.size() == 1 && mn.virtualIn.empty())
            {
                const ProfileKey x = *mn.solidIn.begin();
                if (g.nodes.find(x) != g.nodes.end())
                {
                    mergeProfileNodesIntoRep(g, std::vector<ProfileKey>{v}, x);
                    enqueueNeighbors(x);
                    enqueue(x);
                }
            }
        }
    }

    /// Mirrors VDG::bfsMergeByStoreYieldAndVirtualIn (storeSide) and
    /// VDG::bfsMergeByLoadConsumeAndVirtualOut (!storeSide): propagate seed sets
    /// on solid edges, merge nodes with identical signatures, and drop solid
    /// edges made redundant by the propagation.
    void bfsMergeProfileGraph(ProfileGraph &g, const bool storeSide)
    {
        sccMergeProfileGraph(g);
        if (g.nodes.empty())
            return;

        // Dense index over the current keys so seed-set propagation can use
        // sparse bit sets (NodeBS) instead of per-node hash sets (which is
        // O(N^2) on long chains) or dense O(N^2/64) bitmaps.
        std::vector<ProfileKey> keys;
        keys.reserve(g.nodes.size());
        for (const auto &kn : g.nodes)
            keys.push_back(kn.first);
        std::sort(keys.begin(), keys.end());

        Map<ProfileKey, u32_t> idx;
        idx.reserve(keys.size() * 2);
        for (u32_t i = 0; i < static_cast<u32_t>(keys.size()); ++i)
            idx[keys[i]] = i;

        const u32_t n = static_cast<u32_t>(keys.size());

        // Kahn topological order over solid edges (DAG after SCC merge).
        std::vector<u32_t> indeg(n, 0);
        for (u32_t i = 0; i < n; ++i)
        {
            const ProfileNode &node = g.nodes.find(keys[i])->second;
            for (const ProfileKey dst : node.solidOut)
            {
                const auto d = idx.find(dst);
                if (d != idx.end())
                    ++indeg[d->second];
            }
        }
        std::vector<u32_t> ready;
        for (u32_t i = 0; i < n; ++i)
        {
            if (indeg[i] == 0)
                ready.push_back(i);
        }
        std::vector<u32_t> topo;
        topo.reserve(n);
        while (!ready.empty())
        {
            const u32_t v = ready.back();
            ready.pop_back();
            topo.push_back(v);
            const ProfileNode &node = g.nodes.find(keys[v])->second;
            for (const ProfileKey dst : node.solidOut)
            {
                const auto d = idx.find(dst);
                if (d != idx.end() && --indeg[d->second] == 0)
                    ready.push_back(d->second);
            }
        }
        if (topo.size() != n)
        {
            for (u32_t i = 0; i < n; ++i)
            {
                if (indeg[i] > 0)
                    topo.push_back(i);
            }
        }

        std::vector<NodeBS> reach(n);
        auto seedOf = [&](const ProfileNode &node) -> bool
        {
            return storeSide ? (node.storeYield || !node.virtualIn.empty())
                             : (node.loadConsume || !node.virtualOut.empty());
        };

        std::vector<std::pair<u32_t, u32_t>> redundantSolidEdges;
        if (storeSide)
        {
            for (const u32_t v : topo)
            {
                const ProfileNode &node = g.nodes.find(keys[v])->second;
                if (seedOf(node))
                    reach[v].set(v);
                if (reach[v].empty())
                    continue;
                for (const ProfileKey dst : node.solidOut)
                {
                    const auto d = idx.find(dst);
                    if (d == idx.end())
                        continue;
                    const u32_t di = d->second;
                    if (!(reach[di] |= reach[v]))
                        redundantSolidEdges.emplace_back(v, di);
                }
            }
        }
        else
        {
            for (auto it = topo.rbegin(); it != topo.rend(); ++it)
            {
                const u32_t v = *it;
                const ProfileNode &node = g.nodes.find(keys[v])->second;
                if (seedOf(node))
                    reach[v].set(v);
                if (reach[v].empty())
                    continue;
                for (const ProfileKey src : node.solidIn)
                {
                    const auto s = idx.find(src);
                    if (s == idx.end())
                        continue;
                    const u32_t si = s->second;
                    if (!(reach[si] |= reach[v]))
                        redundantSolidEdges.emplace_back(si, v);
                }
            }
        }

        for (const auto &edge : redundantSolidEdges)
        {
            const ProfileKey a = keys[edge.first];
            const ProfileKey b = keys[edge.second];
            const auto s = g.nodes.find(a);
            if (s != g.nodes.end())
                s->second.solidOut.erase(b);
            const auto d = g.nodes.find(b);
            if (d != g.nodes.end())
                d->second.solidIn.erase(a);
        }

        // Merge nodes that share an identical reach label. This mirrors the
        // label -> version collapse in VersionedFlowSensitive::meldLabel
        // (`Map<MeldVersion, Version> mvv`): the label itself is the map key, so
        // equal labels resolve to a single representative. The sparse bit set
        // is used as the label (NodeBS) to keep label storage proportional to
        // the number of set bits rather than O(n/64) per node.
        struct LabelHash
        {
            size_t operator()(const NodeBS &bs) const
            {
                size_t h = 1469598103934665603ull;
                for (const unsigned bit : bs)
                {
                    h ^= static_cast<size_t>(bit) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
                    h *= 1099511628211ull;
                }
                h ^= static_cast<size_t>(bs.count()) + 0x9e3779b97f4a7c15ull + (h << 6) + (h >> 2);
                return h;
            }
        };

        Map<NodeBS, std::vector<ProfileKey>, LabelHash> labelMembers;
        for (u32_t v = 0; v < n; ++v)
        {
            if (reach[v].empty())
                continue;
            labelMembers[reach[v]].push_back(keys[v]);
        }

        for (auto &kv : labelMembers)
        {
            std::vector<ProfileKey> &members = kv.second;
            if (members.size() < 2)
                continue;
            std::sort(members.begin(), members.end());
            mergeProfileNodesIntoRep(g, members, members.front());
        }
    }

    inline void applyProfilePass(ProfileGraph &g, const char pass)
    {
        switch (pass)
        {
        case 'S':
            sccMergeProfileGraph(g);
            break;
        case 'P':
            pruneProfileGraph(g);
            break;
        case 'C':
            chainContractProfileGraph(g);
            break;
        case 'B':
            bfsMergeProfileGraph(g, true);
            break;
        case 'L':
            bfsMergeProfileGraph(g, false);
            break;
        default:
            break;
        }
    }

    struct ProfileSweepConfig
    {
        bool kill;
        std::string order;
    };

    struct ProfileSweepMetrics
    {
        u64_t graphs = 0;
        u64_t n0Nodes = 0, n0Solid = 0, n0Virtual = 0, n0Plain = 0;
        u64_t n1Nodes = 0, n1Solid = 0, n1Virtual = 0, n1Plain = 0;
        std::vector<u64_t> passNodes, passSolid, passVirtual, passPlain;
        std::vector<double> passSeconds;
        // Merge-class size distribution (how many N0 nodes each surviving rep absorbs).
        Map<u64_t, u64_t> classSizeHist;
        u64_t maxClassSize = 0;
    };

    inline std::string trimAscii(const std::string &s)
    {
        size_t b = 0;
        size_t e = s.size();
        while (b < e && std::isspace(static_cast<unsigned char>(s[b])))
            ++b;
        while (e > b && std::isspace(static_cast<unsigned char>(s[e - 1])))
            --e;
        return s.substr(b, e - b);
    }

    inline std::vector<std::string> splitAscii(const std::string &s, const char delim)
    {
        std::vector<std::string> out;
        std::string cur;
        for (const char c : s)
        {
            if (c == delim)
            {
                out.push_back(cur);
                cur.clear();
            }
            else
            {
                cur.push_back(c);
            }
        }
        out.push_back(cur);
        return out;
    }

    inline bool parseProfileBool(const std::string &v)
    {
        const std::string t = trimAscii(v);
        return t == "1" || t == "true" || t == "on" || t == "yes" || t == "y";
    }

    inline bool isCoverageProfileSpec(const std::string &spec)
    {
        const std::string t = trimAscii(spec);
        return t == "on" || t == "1" || t == "true" || t == "coverage" || t == "yes";
    }

    std::vector<ProfileSweepConfig> parseProfileSweepSpec(const std::string &spec,
                                                          const bool defaultKill)
    {
        std::vector<bool> kills;
        std::vector<std::string> orders;
        bool haveKill = false;
        bool haveOrder = false;

        for (const std::string &partRaw : splitAscii(spec, ';'))
        {
            const std::string part = trimAscii(partRaw);
            if (part.empty())
                continue;
            const size_t eq = part.find('=');
            if (eq == std::string::npos)
                continue;
            const std::string key = trimAscii(part.substr(0, eq));
            const std::string vals = part.substr(eq + 1);
            for (const std::string &vRaw : splitAscii(vals, ','))
            {
                const std::string v = trimAscii(vRaw);
                if (key == "kill")
                {
                    kills.push_back(parseProfileBool(v));
                    haveKill = true;
                }
                else if (key == "order")
                {
                    orders.push_back(v);
                    haveOrder = true;
                }
            }
        }

        if (!haveKill)
            kills.push_back(defaultKill);
        if (!haveOrder)
            orders.push_back(std::string());

        std::vector<ProfileSweepConfig> out;
        out.reserve(kills.size() * orders.size());
        for (const bool k : kills)
        {
            for (const std::string &o : orders)
                out.push_back(ProfileSweepConfig{k, o});
        }
        return out;
    }

    void dumpProfileSweepSummary(const ProfileSweepConfig &cfg, const ProfileSweepMetrics &m)
    {
        const std::string orderName = cfg.order.empty() ? std::string("none") : cfg.order;
        double totalTime = 0.0;
        for (const double t : m.passSeconds)
            totalTime += t;

        SVFUtil::outs()
            << "vdg.passprofile.config.summary"
            << " config=kill:" << (cfg.kill ? 1 : 0)
            << ",order:" << orderName
            << " graphs:" << m.graphs
            << " n0_nodes:" << m.n0Nodes
            << " n0_solid:" << m.n0Solid
            << " n0_virtual:" << m.n0Virtual
            << " n0_plain:" << m.n0Plain
            << " n1_nodes:" << m.n1Nodes
            << " n1_solid:" << m.n1Solid
            << " n1_virtual:" << m.n1Virtual
            << " n1_plain:" << m.n1Plain
            << " maxClassSize:" << m.maxClassSize
            << " time:" << totalTime
            << "\n";

        // Also report every proper prefix of the order (e.g. S and SP for SPC),
        // so a single sweep run yields the prefix distribution for free.
        for (size_t i = 0; i + 1 < cfg.order.size(); ++i)
        {
            double cumTime = 0.0;
            for (size_t j = 0; j <= i; ++j)
                cumTime += m.passSeconds[j];

            SVFUtil::outs()
                << "vdg.passprofile.config.summary"
                << " config=kill:" << (cfg.kill ? 1 : 0)
                << ",order:" << cfg.order.substr(0, i + 1)
                << " graphs:" << m.graphs
                << " n0_nodes:" << m.n0Nodes
                << " n0_solid:" << m.n0Solid
                << " n0_virtual:" << m.n0Virtual
                << " n0_plain:" << m.n0Plain
                << " n1_nodes:" << m.passNodes[i]
                << " n1_solid:" << m.passSolid[i]
                << " n1_virtual:" << m.passVirtual[i]
                << " n1_plain:" << m.passPlain[i]
                << " maxClassSize:" << m.maxClassSize
                << " time:" << cumTime
                << "\n";
        }

        {
            u64_t b1 = 0, b2 = 0, b3 = 0, b4 = 0, b5 = 0, b6 = 0, b7 = 0, b8 = 0;
            for (const auto &kv : m.classSizeHist)
            {
                const u64_t s = kv.first;
                const u64_t c = kv.second;
                if (s <= 1) b1 += c;
                else if (s == 2) b2 += c;
                else if (s <= 5) b3 += c;
                else if (s <= 10) b4 += c;
                else if (s <= 50) b5 += c;
                else if (s <= 100) b6 += c;
                else if (s <= 1000) b7 += c;
                else b8 += c;
            }
            SVFUtil::outs()
                << "vdg.passprofile.config.classsize"
                << " config=kill:" << (cfg.kill ? 1 : 0)
                << ",order:" << orderName
                << " size1:" << b1 << " size2:" << b2 << " size3_5:" << b3
                << " size6_10:" << b4 << " size11_50:" << b5
                << " size51_100:" << b6 << " size101_1000:" << b7
                << " size1001p:" << b8 << " maxSize:" << m.maxClassSize
                << "\n";
        }

        for (size_t i = 0; i < cfg.order.size(); ++i)
        {
            SVFUtil::outs()
                << "vdg.passprofile.config.pass"
                << " config=kill:" << (cfg.kill ? 1 : 0)
                << ",order:" << orderName
                << " pass:" << cfg.order[i]
                << " nodes:" << m.passNodes[i]
                << " solid:" << m.passSolid[i]
                << " virtual:" << m.passVirtual[i]
                << " plain:" << m.passPlain[i]
                << " time:" << m.passSeconds[i]
                << "\n";
        }
    }

    } // namespace

void runSVFGPassProfiling(const LOPA &pta, const SVFG *svfg)
    {
        if (svfg == nullptr)
            return;

        Map<NodeID, ProfileGraph> objGraphs;
        Map<NodeID, NodeVector> deltaSrcCacheByDst;
        SVFG *mutableSVFG = const_cast<SVFG *>(svfg);
        CallGraph *cg = svfg->getCallGraph();

        auto nonStrongUpdateObj = [&pta](const NodeID o) -> bool
        {
            const BaseObjVar *base = pta.getPAG()->getBaseObject(o);
            if (base == nullptr)
                return true;
            return pta.isHeapMemObj(o) || pta.isArrayMemObj(o)
                || base->isFieldInsensitive()
                || pta.isLocalVarInRecursiveFun(o);
        };

        // Rebuild delta/delta-source marks locally for profiling (same criteria as buildDeltaMaps).
        std::vector<bool> deltaMap(svfg->getTotalNodeNum(), false);
        std::vector<bool> deltaSourceMap(svfg->getTotalNodeNum(), false);
        Set<const CallICFGNode *> deltaCBNs;
        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const NodeID l = it->first;
            if (l >= deltaMap.size())
                continue;

            const SVFGNode *s = it->second;
            bool isDelta = false;
            if (const FunObjVar *fn = svfg->isFunEntrySVFGNode(s))
            {
                if (cg != nullptr)
                {
                    CallGraphEdge::CallInstSet callsites;
                    cg->getIndCallSitesInvokingCallee(fn, callsites);
                    isDelta = !callsites.empty();
                    if (isDelta)
                    {
                        for (const CallICFGNode *cbn : callsites)
                            deltaCBNs.insert(cbn);
                    }
                }
            }
            else if (const CallICFGNode *cbn = svfg->isCallSiteRetSVFGNode(s))
            {
                isDelta = cbn->isIndirectCall();
                if (isDelta)
                    deltaCBNs.insert(cbn);
            }
            deltaMap[l] = isDelta;
        }
        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const NodeID l = it->first;
            if (l >= deltaSourceMap.size())
                continue;

            const SVFGNode *s = it->second;
            if (const CallICFGNode *cbn = SVFUtil::dyn_cast<CallICFGNode>(s->getICFGNode()))
            {
                if (deltaCBNs.find(cbn) != deltaCBNs.end())
                    deltaSourceMap[l] = true;
            }
            if (SVFUtil::isa<FormalOUTSVFGNode>(s))
                deltaSourceMap[l] = true;
        }

        // Build delta-source -> delta-destination reverse cache (same ind-call resolution logic as buildVDG).
        Map<NodeID, NodeVector> deltaDstCache;
        auto getDeltaDstsForSrc = [&deltaMap, cg, svfg, mutableSVFG, &deltaDstCache](NodeID srcId) -> const NodeVector&
        {
            const auto cached = deltaDstCache.find(srcId);
            if (cached != deltaDstCache.end())
                return cached->second;

            NodeVector dsts;
            const SVFGNode *srcNode = svfg->getSVFGNode(srcId);
            if (srcNode != nullptr)
            {
                if (const ActualINSVFGNode *actualIn = SVFUtil::dyn_cast<ActualINSVFGNode>(srcNode))
                {
                    const CallICFGNode *cs = actualIn->getCallSite();
                    if (cs && cs->isIndirectCall())
                    {
                        if (cg != nullptr && cg->hasCallGraphEdge(cs))
                        {
                            for (CallGraph::CallGraphEdgeSet::const_iterator it = cg->getCallEdgeBegin(cs),
                                 eit = cg->getCallEdgeEnd(cs); it != eit; ++it)
                            {
                                const FunObjVar *callee = (*it)->getDstNode()->getFunction();
                                if (!svfg->hasFormalINSVFGNodes(callee))
                                    continue;
                                const SVFG::FormalINSVFGNodeSet &formalIns
                                    = mutableSVFG->getFormalINSVFGNodes(callee);
                                for (const NodeID dstId : formalIns)
                                {
                                    if (dstId < deltaMap.size() && deltaMap[dstId])
                                        dsts.push_back(dstId);
                                }
                            }
                        }
                    }
                }
                else if (const FormalOUTSVFGNode *formalOut = SVFUtil::dyn_cast<FormalOUTSVFGNode>(srcNode))
                {
                    const FunExitICFGNode *exitNode = formalOut->getFunExitNode();
                    const FunObjVar *fun = exitNode ? exitNode->getFun() : nullptr;
                    if (fun != nullptr && cg != nullptr)
                    {
                        CallGraphEdge::CallInstSet callsites;
                        cg->getIndCallSitesInvokingCallee(fun, callsites);
                        for (const CallICFGNode *cs : callsites)
                        {
                            if (!svfg->hasActualOUTSVFGNodes(cs))
                                continue;
                            const SVFG::ActualOUTSVFGNodeSet &actualOuts
                                = mutableSVFG->getActualOUTSVFGNodes(cs);
                            for (const NodeID dstId : actualOuts)
                            {
                                if (dstId < deltaMap.size() && deltaMap[dstId])
                                    dsts.push_back(dstId);
                            }
                        }
                    }
                }
            }

            if (!dsts.empty())
            {
                std::sort(dsts.begin(), dsts.end());
                dsts.erase(std::unique(dsts.begin(), dsts.end()), dsts.end());
            }

            const auto inserted = deltaDstCache.emplace(srcId, std::move(dsts));
            return inserted.first->second;
        };

        for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
        {
            const NodeID srcId = it->first;
            if (srcId >= deltaSourceMap.size() || !deltaSourceMap[srcId])
                continue;

            const NodeVector &deltaDsts = getDeltaDstsForSrc(srcId);
            for (const NodeID dstId : deltaDsts)
                deltaSrcCacheByDst[dstId].push_back(srcId);
        }
        for (Map<NodeID, NodeVector>::value_type &entry : deltaSrcCacheByDst)
        {
            NodeVector &srcs = entry.second;
            if (srcs.empty())
                continue;
            std::sort(srcs.begin(), srcs.end());
            srcs.erase(std::unique(srcs.begin(), srcs.end()), srcs.end());
        }

        auto buildProfileGraphs = [&](const bool useFSLowerBound) -> Map<NodeID, ProfileGraph>
        {
            Map<NodeID, ProfileGraph> objGraphs;

            // Build profiling graph directly from SVFG indirect edges.
            for (SVFG::const_iterator it = svfg->begin(), eit = svfg->end(); it != eit; ++it)
            {
                const SVFGNode *srcNode = it->second;
                const NodeID srcStmt = srcNode->getId();
                const ProfileNodeRole srcRole = pta.isStore(srcStmt)
                                              ? ProfileNodeRole::StoreYield
                                              : ProfileNodeRole::Normal;
                const ProfileKey srcKey = makeProfileKey(srcStmt, srcRole);

                for (const SVFGEdge *edge : srcNode->getOutEdges())
                {
                    const IndirectSVFGEdge *ie = SVFUtil::dyn_cast<IndirectSVFGEdge>(edge);
                    if (ie == nullptr)
                        continue;

                    const SVFGNode *dstNode = ie->getDstNode();
                    const NodeID dstStmt = dstNode->getId();
                    const ProfileNodeRole dstRole = pta.isStore(dstStmt)
                                                  ? ProfileNodeRole::StoreConsume
                                                  : ProfileNodeRole::Normal;
                    const ProfileKey dstKey = makeProfileKey(dstStmt, dstRole);

                    for (NodeID o : ie->getPointsTo())
                    {
                        ProfileGraph &g = objGraphs[o];
                        (void)addProfileEdge(g, srcKey, dstKey, false, svfg);
                    }
                }
            }

            // Add delta virtual edges expanded through resolved indirect calls.
            for (const Map<NodeID, NodeVector>::value_type &entry : deltaSrcCacheByDst)
            {
                const NodeID dstStmt = entry.first;
                const SVFGNode *dstNode = svfg->getSVFGNode(dstStmt);
                const MRSVFGNode *dstMR = SVFUtil::dyn_cast<MRSVFGNode>(dstNode);
                if (dstMR == nullptr)
                    continue;

                const ProfileNodeRole dstRole = pta.isStore(dstStmt)
                                              ? ProfileNodeRole::StoreConsume
                                              : ProfileNodeRole::Normal;
                const ProfileKey dstKey = makeProfileKey(dstStmt, dstRole);

                for (NodeID o : dstMR->getPointsTo())
                {
                    ProfileGraph &g = objGraphs[o];
                    for (const NodeID srcStmt : entry.second)
                    {
                        const SVFGNode *srcNode = svfg->getSVFGNode(srcStmt);
                        const MRSVFGNode *srcMR = SVFUtil::dyn_cast<MRSVFGNode>(srcNode);
                        if (srcMR == nullptr || !srcMR->getPointsTo().test(o))
                            continue;

                        const ProfileNodeRole srcRole = pta.isStore(srcStmt)
                                                      ? ProfileNodeRole::StoreYield
                                                      : ProfileNodeRole::Normal;
                        const ProfileKey srcKey = makeProfileKey(srcStmt, srcRole);
                        (void)addProfileEdge(g, srcKey, dstKey, true, svfg);
                    }
                }
            }

            // Add store C->Y edges with existing virtual/solid logic.
            // Mirror the real builder: a store yields (and gets a C->Y edge)
            // only when it actually appears as a yield endpoint in this object's
            // footprint (VDG::touchedYieldLocs). Stores that only appear as a
            // StoreConsume endpoint must not gain a synthetic yield node/edge.
            for (Map<NodeID, ProfileGraph>::value_type &entry : objGraphs)
            {
                const NodeID o = entry.first;
                ProfileGraph &g = entry.second;
                Set<NodeID> storeYieldStmtIds;
                for (const auto &kn : g.nodes)
                {
                    if (getRoleFromProfileKey(kn.first) != ProfileNodeRole::StoreYield)
                        continue;
                    const NodeID stmtId = getStmtIdFromProfileKey(kn.first);
                    if (pta.isStore(stmtId))
                        storeYieldStmtIds.insert(stmtId);
                }

                const bool keepVirtualStoreCY = !useFSLowerBound || !nonStrongUpdateObj(o);
                for (const NodeID storeStmt : storeYieldStmtIds)
                {
                    const ProfileKey cKey = makeProfileKey(storeStmt, ProfileNodeRole::StoreConsume);
                    const ProfileKey yKey = makeProfileKey(storeStmt, ProfileNodeRole::StoreYield);
                    (void)addProfileEdge(g, cKey, yKey, keepVirtualStoreCY, svfg);
                }
            }

            return objGraphs;
        };

        const std::string profileSpec = Options::VDGPassProfile();

        // Coverage-only mode: report opportunity coverage of the current kill setting.
        if (isCoverageProfileSpec(profileSpec))
        {
            Map<NodeID, ProfileGraph> objGraphs = buildProfileGraphs(Options::LOPAObjFSLowerBound());
            VDGPassProfileAggregate agg;
            for (const Map<NodeID, ProfileGraph>::value_type &entry : objGraphs)
                profileVDGObjectForPassPatterns(entry.second, agg);
            dumpVDGPassProfile(agg);
            return;
        }

        // Sweep mode: apply each (kill, order) configuration to the estimation
        // graph and report the resulting size and per-pass time.
        const std::vector<ProfileSweepConfig> configs
            = parseProfileSweepSpec(profileSpec, Options::LOPAObjFSLowerBound());

        std::vector<std::pair<bool, std::vector<std::string>>> ordersByKill;
        for (const ProfileSweepConfig &cfg : configs)
        {
            bool found = false;
            for (auto &entry : ordersByKill)
            {
                if (entry.first == cfg.kill)
                {
                    entry.second.push_back(cfg.order);
                    found = true;
                    break;
                }
            }
            if (!found)
                ordersByKill.push_back(std::make_pair(cfg.kill, std::vector<std::string>{cfg.order}));
        }

        for (const auto &killEntry : ordersByKill)
        {
            const bool kill = killEntry.first;
            const Map<NodeID, ProfileGraph> objGraphs = buildProfileGraphs(kill);

            // Also emit edge-pattern coverage for this kill setting, so a single
            // sweep run reports both coverage (step1..step5) and sizes/times.
            {
                VDGPassProfileAggregate covAgg;
                for (const Map<NodeID, ProfileGraph>::value_type &entry : objGraphs)
                    profileVDGObjectForPassPatterns(entry.second, covAgg);
                dumpVDGPassProfile(covAgg,
                                   std::string(" config=kill:") + (kill ? "1" : "0"));
            }

            for (const std::string &order : killEntry.second)
            {
                const ProfileSweepConfig cfg{kill, order};
                ProfileSweepMetrics metrics;
                metrics.passNodes.assign(order.size(), 0);
                metrics.passSolid.assign(order.size(), 0);
                metrics.passVirtual.assign(order.size(), 0);
                metrics.passPlain.assign(order.size(), 0);
                metrics.passSeconds.assign(order.size(), 0.0);

                for (const Map<NodeID, ProfileGraph>::value_type &entry : objGraphs)
                {
                    ProfileGraph work = entry.second;
                    ++metrics.graphs;
                    metrics.n0Nodes += static_cast<u64_t>(work.nodes.size());
                    metrics.n0Solid += countSolidEdges(work);
                    metrics.n0Virtual += countVirtualEdges(work);
                    metrics.n0Plain += countPlainNodes(work);

                    for (size_t i = 0; i < order.size(); ++i)
                    {
                        const auto passStart = std::chrono::steady_clock::now();
                        applyProfilePass(work, order[i]);
                        const auto passEnd = std::chrono::steady_clock::now();
                        metrics.passSeconds[i]
                            += std::chrono::duration<double>(passEnd - passStart).count();
                        metrics.passNodes[i] += static_cast<u64_t>(work.nodes.size());
                        metrics.passSolid[i] += countSolidEdges(work);
                        metrics.passVirtual[i] += countVirtualEdges(work);
                        metrics.passPlain[i] += countPlainNodes(work);
                    }

                    metrics.n1Nodes += static_cast<u64_t>(work.nodes.size());
                    metrics.n1Solid += countSolidEdges(work);
                    metrics.n1Virtual += countVirtualEdges(work);
                    metrics.n1Plain += countPlainNodes(work);

                    for (const auto &kn : work.nodes)
                    {
                        const u64_t cs = static_cast<u64_t>(kn.second.classSize);
                        ++metrics.classSizeHist[cs];
                        if (cs > metrics.maxClassSize)
                            metrics.maxClassSize = cs;
                    }
                }

                dumpProfileSweepSummary(cfg, metrics);
            }
        }
    }
} // namespace SVF
