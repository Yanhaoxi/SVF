//===- LOPAFrontend.h -- shared offline compression frontend -----------------------//
#ifndef LOPA_FRONTEND_H_
#define LOPA_FRONTEND_H_

#include "Graphs/VDG.h"
#include "WPA/FlowSensitive.h"
#include <functional>
#include <memory>

namespace SVF {
class AndersenWaveDiff;
class LOPAVSFS;
class LOPAVSFSStat;

/// Shared VDG construction and compression for PUS, CG and VSFS backends.
/// Materialized graphs/maps are used by VSFS; PUS and CG consume each object
/// through exportOffline and release its graph immediately.
class LOPAFrontend : public FlowSensitive {
    friend class LOPAVSFS;
    friend class LOPAVSFSStat;
public:
    using LocToVersionMap = Map<NodeID, Version>;
    using LocToVersionMapPtr = std::shared_ptr<LocToVersionMap>;
    using ObjToLocVersionMap = Map<NodeID, LocToVersionMapPtr>;
    static const Version invalidVersion;
    static VersionedVar atKey(NodeID, Version);

    /// References passed to the consumer are valid only during its invocation.
    using OfflineConsumer = std::function<void(NodeID, const VDG&,
        const LocToVersionMap&, const LocToVersionMap&)>;
    static void exportOffline(SVFIR* pag, SVFG* graph, AndersenWaveDiff* preanalysis,
        const PointerAnalysis& analysis, const OfflineConsumer& consumeObject);

    const std::string PTAName() const override { return "LOPA frontend"; }
    bool isStore(NodeID location) const;
    bool isLoad(NodeID location) const;
    NodeBS& getStmtReliance(NodeID object, Version version);

protected:
    explicit LOPAFrontend(SVFIR* pag, PTATY type = LOPA_WPA);
    /// Build the materialized frontend after the backend initializes SVF/stat.
    void initializeVDG();
    void finalize() override;
    void cluster() override;
    bool propAlongIndirectEdge(const IndirectSVFGEdge*) override { return false; }

private:
    const OfflineConsumer* offlineConsumer = nullptr;
    void buildOffline(SVFG*, AndersenWaveDiff*, const PointerAnalysis&, const OfflineConsumer&);
    void prelabel();
    enum class StoreEdgePolicy { ObjectLowerBound, Deferred };
    void buildVDG(StoreEdgePolicy storeEdges = StoreEdgePolicy::ObjectLowerBound);
    struct VDGBuildContext;
    void removeAllIndirectSVFGEdges();
    void buildIsStoreLoadMaps();
    void buildDeltaMaps();
    bool delta(NodeID location) const;
    bool deltaSource(NodeID location) const;
    void setVersion(NodeID location, NodeID object, Version version, ObjToLocVersionMap&);
    void setConsume(NodeID location, NodeID object, Version version);
    void setYield(NodeID location, NodeID object, Version version);

    ObjToLocVersionMap consume, yield;
    VDGManager vdgManager;
    Map<NodeID, Map<Version, NodeBS>> stmtReliance;
    Set<NodeID> prelabeledObjects, fiObjects;
    Map<NodeID, NodeVector> objStartingNodes;
    std::vector<bool> deltaMap, deltaSourceMap, isStoreMap, isLoadMap;
    u32_t numPrelabelNodes = 0, numPrelabelFIObjs = 0;
    double prelabelingTime = 0, vdgBuildTime = 0;
};

void runSVFGPassProfiling(const LOPAFrontend& pta, const SVFG* svfg);
} // namespace SVF
#endif
