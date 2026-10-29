#ifndef SVF_LOPA_H
#define SVF_LOPA_H

#include "WPA/FlowSensitive.h"
#include "Graphs/PUSGraph.h"
#include "Graphs/PUSMemoryMap.h"
#include "WPA/LOPACopySolver.h"
#include <memory>
#include <unordered_map>

namespace SVF {
class VDG;

/// LOPA's offline states and SSA values share an inclusion constraint graph.
/// PUS schedules Copy SCCs first, then the affected GEP/Load/Store constraints.
/// GEP constraints retain their original SVF statements, including their offsets.
class LOPA : public FlowSensitive {
    friend class LOPAStat;
    friend class LOPACopySolver;
public:
    explicit LOPA(SVFIR* pag) : FlowSensitive(pag) {}
    void initialize() override;
    void solveConstraints() override;
    void finalize() override;
    const std::string PTAName() const override { return "LOPA"; }
    const PointsTo& getPts(NodeID value) override;
    bool unionPts(NodeID value, const PointsTo& pts) override;
    bool unionPts(NodeID value, NodeID source) override;
    bool addPts(NodeID value, NodeID object) override;

private:
    static constexpr NodeID invalidNode = ~NodeID(0);
    static uint64_t memoryKey(NodeID location, NodeID object, bool output) {
        // Bits 33..63 hold location, 1..32 hold the full object ID, and 0 is OUT.
        assert(location < (uint64_t(1) << 31));
        return (uint64_t(location) << 33) | (uint64_t(object) << 1) | output;
    }
    // Constraints registered on the same source share a processing history.
    // Groups retain separate histories across a Copy merge until processed.
    struct ConstraintGroup {
        std::vector<const GepSVFGNode*> geps;
        std::vector<const SVFGNode*> indirect;
        NodeID nextGroup = invalidNode;
    };
    struct MemoryPair { NodeID object, in, out; };
    struct StoreState {
        const StoreSVFGNode* node = nullptr;
        std::vector<MemoryPair> memory;
        bool active = false, strong = false;
        NodeID singleton = 0;
    };
    std::unique_ptr<PUSConstraintGraph> constraints;
    // Full sets are keyed by Copy representative; diff/propa sets by group ID.
    // DiffPTData stores these in independent maps, also for retired Copy nodes.
    std::unique_ptr<DiffPTDataTy> points;
    // Parent lookup touches only node IDs; links are stored in the group slots.
    std::vector<NodeID> parent;
    std::vector<bool> copyDirty;
    std::vector<NodeID> groupHead, groupTail;
    std::vector<ConstraintGroup> constraintGroups;
    std::unordered_map<NodeID, NodeID> values;
    PUSMemoryMap memory;
    std::unordered_map<NodeID, StoreState> stores;
    NodeBS roots, constraintWork, forcedStores;
    LOPACopySolver copySolver;
    bool exported = false;
    uint64_t rounds = 0, copyEdges = 0;
    uint64_t copyUnions = 0, strongToWeak = 0;
    uint64_t coalescedGroups = 0;
    uint64_t newFIObjects = 0;
    uint64_t initialNodes = 0, initialCopies = 0;
    uint64_t copyAttempts = 0, copyInvalid = 0, copySelf = 0, copyDuplicates = 0;
    double constructionTime = 0, offlineTime = 0, exportTime = 0;
    double valueBuildTime = 0, exportNodeTime = 0, exportCopyTime = 0, exportMapTime = 0;
    double indirectTime = 0;

    NodeID newNode();
    NodeID representative(NodeID id);
    NodeID valueNode(NodeID value);
    NodeID memoryNode(NodeID location, NodeID object, bool output = false) const;
    void changed(NodeID id);
    bool join(NodeID dst, NodeID src);
    bool joinRepresentatives(NodeID dst, NodeID src);
    bool join(NodeID dst, const PointsTo& pts);
    void addCopy(NodeID src, NodeID dst);
    void addPhi(const PHISVFGNode* phi);
    void addSVFGEdge(const SVFGEdge* edge);
    using VersionNodes = std::vector<NodeID>;
    VersionNodes createMemoryNodes(const VDG&);
    static NodeID memoryVersionNode(const VDG&, const VersionNodes&, Version);
    void addMemoryCopies(const VDG&, const VersionNodes&);
    void bindMemoryStates(NodeID, const VDG&, const VersionNodes&,
                          const Map<NodeID, Version>& consumes, const Map<NodeID, Version>& yields);
    void importMemoryObject(NodeID, const VDG&, const Map<NodeID, Version>& consumes,
                            const Map<NodeID, Version>& yields);
    void registerValueConstraints(const SVFGNode*);
    ConstraintGroup& constraintsFor(NodeID source);
    void compileMemory();
    void compileValues();
    PTAStat* createStat();
    void processLoadTargets(const LoadSVFGNode*, const PointsTo&);
    void processStoreTargets(const StoreSVFGNode*, const PointsTo&);
    void addStoreWrites(const StoreSVFGNode*, const PointsTo&);
    void addStoreBypasses(const StoreState&);
    void reconsiderStrongStores();
    void solveDataflow();
    void solveIndirect();
    void processConstraintGroup(NodeID group, NodeID source);
    void mergeConstraintGroups(NodeID root, NodeID member);
    void coalesceConstraintGroups(NodeID source);
    void processIndirect(const SVFGNode* node, const PointsTo& newTargets);
    void transferGep(const GepSVFGNode* gep, const PointsTo& source);
    void updateConnectedNodes(const SVFGEdgeSetTy& edges) override;
};
}
#endif
