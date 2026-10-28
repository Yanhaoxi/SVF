#ifndef FLOWSENSITIVECG_H
#define FLOWSENSITIVECG_H
#include "WPA/FlowSensitive.h"
#include "WPA/CGSFR.h"
#include "WPA/CGSFRSchedule.h"
#include <deque>
#include <unordered_map>
namespace SVF {
/// Explicit FSConsG cells. Only stores have separate IN/OUT states.
/// FlowSensitive supplies preprocessing and object/call semantics, not solving.
class FlowSensitiveCG : public FlowSensitive {
    friend class FlowSensitiveCGStat;
public:
    explicit FlowSensitiveCG(SVFIR* pag, bool compressed = false, bool sfr = false)
        : FlowSensitive(pag), lopaFrontend(compressed), useSFR(sfr) {}
    void initialize() override;
    void solveConstraints() override;
    void finalize() override;
    const std::string PTAName() const override {
        return std::string(lopaFrontend ? "LOPA+CG-FSPTA-" : "CG-FSPTA-")
            + (useSFR ? "SFR-explicit" : "Wave");
    }
    const PointsTo& getPts(NodeID id) override;
    bool unionPts(NodeID id, const PointsTo& pts) override;
    bool unionPts(NodeID id, NodeID source) override;
    bool addPts(NodeID id, NodeID object) override;
private:
    using CellID = u32_t;
    static constexpr CellID invalidCell = ~CellID(0);
    struct Cell {
        CellID rep;
        PointsTo pts, sent;
        NodeBS copies;
        std::vector<const GepSVFGNode*> geps;
        std::vector<const SVFGNode*> indirect;
        bool queued = false;
        explicit Cell(CellID id) : rep(id) {}
    };
    struct MemoryPair { NodeID object; CellID in, out; };
    struct StoreState {
        const StoreSVFGNode* node = nullptr;
        std::vector<MemoryPair> memory;
        bool active = false, strong = false;
        NodeID singleton = 0;
    };
    std::deque<Cell> cells;
    std::unordered_map<NodeID, CellID> values;
    std::unordered_map<uint64_t, CellID> memory;
    std::unordered_map<NodeID, StoreState> stores;
    std::deque<CellID> pending;
    std::deque<const SVFGNode*> indirectWork;
    NodeBS indirectQueued;
    bool graphChanged = false;
    bool resultExported = false;
    bool lopaFrontend;
    bool useSFR = false;
    NodeBS sccCandidates;
    // Sparse stride map keeps ordinary cells unchanged in the Wave backend.
    std::unordered_map<CellID, std::vector<CGSFR::Weight>> strides;
    // Reuse dense Tarjan storage; reset only nodes visited by this wave.
    std::vector<unsigned> sfrIndex, sfrLow;
    std::vector<bool> sfrActive;
    CGSFR::Schedule sfrSchedule;
    uint64_t sccVisited = 0, strideVisited = 0, positiveCycles = 0;
    uint64_t strideCount = 0, expansionCalls = 0, strideFacts = 0;
    size_t copyCount = 0, mergedCount = 0, rounds = 0;
    double constructionTime = 0;
    double offlineTime = 0, exportTime = 0;
    double profileSCCTime = 0, profileCopyGepTime = 0;
    double profileIndirectTime = 0, profileCallGraphTime = 0;
    CellID newCell();
    CellID representative(CellID id);
    CellID valueCell(NodeID value);
    CellID memoryCell(NodeID location, NodeID object, bool output = false);
    void enqueue(CellID id);
    bool join(CellID id, const PointsTo& pts);
    void addCopy(CellID src, CellID dst);
    void addPhi(const PHISVFGNode* phi);
    void addSVFGEdge(const SVFGEdge* edge);
    void compileGraph();
    void compileLOPAMemory();
    void solveCopies();
    void propagateGep(const GepSVFGNode* gep, const PointsTo& delta);
    void queueIndirect(const SVFGNode* node);
    void solveIndirect(const SVFGNode* node);
    void collapseCopyCycles();
    void scheduleCopyGep(const NodeBS& candidates);
    void detectStrides();
    void expandGepStrides(CellID dst, PointsTo& targets);
    void updateConnectedNodes(const SVFGEdgeSetTy& edges) override;
};
}
#endif
