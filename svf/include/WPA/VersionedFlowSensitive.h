//===- VersionedFlowSensitive.h -- Versioned flow-sensitive pointer analysis --------//

/*
 * VersionedFlowSensitiveAnalysis.h
 *
 *  Created on: Jun 26, 2020
 *      Author: Mohamad Barbar
 *
 * The implementation is based on
 * Mohamad Barbar, Yulei Sui and Shiping Chen. "Object Versioning for Flow-Sensitive Pointer Analysis".
 * International Symposium on Code Generation and Optimization (CGO'21)
 */

#ifndef VFS_H_
#define VFS_H_

#include "Graphs/SVFGOPT.h"
#include "Graphs/VDG.h"
#include "MSSA/SVFGBuilder.h"
#include "Util/CommandLine.h"
#include "WPA/FlowSensitive.h"
#include "WPA/WPAFSSolver.h"
#include "MemoryModel/PointsTo.h"
#include <memory>

namespace SVF
{

class AndersenWaveDiff;

/*!
 * Versioned flow sensitive whole program pointer analysis
 */
class VersionedFlowSensitive : public FlowSensitive
{
    friend class VersionedFlowSensitiveStat;

private:
    typedef CoreBitVector MeldVersion;

public:
    /// Per-object location-version map: l -> v.
    typedef Map<NodeID, Version> LocToVersionMap;
    typedef std::shared_ptr<LocToVersionMap> LocToVersionMapPtr;
    /// Object-indexed version map (o:l:v): o -> shared(l -> v).
    typedef Map<NodeID, LocToVersionMapPtr> ObjToLocVersionMap;
    /// (o -> (v -> versions with rely on o:v).
    typedef Map<NodeID, Map<Version, std::vector<Version>>> VersionRelianceMap;

    /// If this version appears, there has been an error.
    static const Version invalidVersion;

    /// Return key into vPtD for address-taken var of a specific version.
    static VersionedVar atKey(NodeID, Version);

    /// Constructor
    VersionedFlowSensitive(SVFIR *_pag, PTATY type = VFS_WPA);

    /// Initialize analysis
    virtual void initialize() override;

    /// Finalize analysis
    virtual void finalize() override;

    /// Get PTA name
    virtual const std::string PTAName() const override
    {
        return "VersionedFlowSensitive";
    }

    /// Methods to support type inquiry through isa, cast, and dyn_cast
    //@{
    static inline bool classof(const VersionedFlowSensitive *)
    {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta)
    {
        return pta->getAnalysisTy() == VFS_WPA;
    }
    //@}

    /// Create single instance of versioned flow-sensitive points-to analysis.
    static VersionedFlowSensitive *createVFSWPA(SVFIR *_pag)
    {
        if (vfspta == nullptr)
        {
            vfspta = new VersionedFlowSensitive(_pag);
            vfspta->analyze();
        }

        return vfspta;
    }

    /// Release flow-sensitive pointer analysis
    static void releaseVFSWPA()
    {
        if (vfspta) delete vfspta;
        vfspta = nullptr;
    }

protected:
    virtual bool processLoad(const LoadSVFGNode* load) override;
    virtual bool processStore(const StoreSVFGNode* store) override;
    virtual bool processGep(const GepSVFGNode* edge) override;
    virtual void processNode(NodeID n) override;
    virtual void updateConnectedNodes(const SVFGEdgeSetTy& newEdges) override;

    /// Override to do nothing. Version propagation is handled via batch propagation on VDG.
    virtual bool propAlongIndirectEdge(const IndirectSVFGEdge*) override
    {
        return false;
    }

    /// Override pushIntoWorklist to route nodes to priority worklists
    virtual inline void pushIntoWorklist(NodeID id) override
    {
        NodeID repId = sccRepNode(id);
        int prio = isStore(repId) ? 2 : (isLoad(repId) ? 0 : 1);
        priorityWorklist[prio].push(repId);
    }

    /// Override isWorklistEmpty to check priority worklists
    inline bool isWorklistEmpty()
    {
        return priorityWorklist[0].empty()
            && priorityWorklist[1].empty()
            && priorityWorklist[2].empty();
    }

    /// Override popFromWorklist to pop from priority worklists  
    inline NodeID popFromWorklist()
    {
        for (int i = 0; i < 3; ++i)
        {
            if (!priorityWorklist[i].empty())
                return sccRepNode(priorityWorklist[i].pop());
        }
        assert(false && "popFromWorklist called on empty worklists");
        return 0;
    }

    /// Override since we want to assign different weights based on versioning.
    virtual void cluster(void) override;

public:
    /// Returns true if l is a store node.
    virtual bool isStore(const NodeID l) const;

    /// Returns true if l is a load node.
    virtual bool isLoad(const NodeID l) const;

    /// Shared code for getConsume and getYield. They wrap this function.
    Version getVersion(const NodeID l, const NodeID o, const ObjToLocVersionMap &lvm) const;

    /// Returns the consumed version of o at l. If no such version exists, returns invalidVersion.
    Version getConsume(const NodeID l, const NodeID o) const;

    /// Returns the yielded version of o at l. If no such version exists, returns invalidVersion.
    Version getYield(const NodeID l, const NodeID o) const;

    /// Returns the statements which rely on o:v.
    NodeBS &getStmtReliance(const NodeID o, const Version v);

    void drawVersionDependencyGraph(const std::string& filename) const;

    /// Dumps maps consume and yield.
    void dumpLocVersionMaps(void) const;

    void solveAndwritePtsToFile(const std::string& filename) override;

    void writeVersionedAnalysisResultToFile(const std::string& filename);

    void readVersionedAnalysisResultFromFile(std::ifstream& F);

    void readPtsFromFile(const std::string& filename) override;

    /// Skip solving when pass-profile mode is enabled.
    void solveConstraints() override;

    /// Dumps a MeldVersion to stdout.
    static void dumpMeldVersion(MeldVersion &v);

private:
    /// Prelabel the SVFG: set y(o) for stores and c(o) for delta nodes to a new version.
    void prelabel(void);
    /// Build VDG in object-major pipeline (includes labeling/materialization/simplify/bind).
    void buildVDG(void);
    /// Melds v2 into v1 (in place), returns whether a change occurred.
    static bool meld(MeldVersion &mv1, const MeldVersion &mv2);

    /// Removes all indirect edges in the SVFG.
    void removeAllIndirectSVFGEdges(void);

    /// Fills in isStoreMap and isLoadMap.
    virtual void buildIsStoreLoadMaps(void);

    /// Fills in deltaMap and deltaSourceMap for the SVFG.
    virtual void buildDeltaMaps(void);

    /// Returns true if l is a delta node, i.e., may get a new incoming indirect
    /// edge due to on-the-fly callgraph construction.
    virtual bool delta(const NodeID l) const;

    /// Returns true if l is a delta-source node, i.e., may get a new outgoing indirect
    /// edge to a delta node due to on-the-fly callgraph construction.
    virtual bool deltaSource(const NodeID l) const;

    /// Shared code for setConsume and setYield. They wrap this function.
    void setVersion(const NodeID l, const NodeID o, const Version v, ObjToLocVersionMap &lvm);

    /// Sets the consumed version of o at l to v.
    void setConsume(const NodeID l, const NodeID o, const Version v);

    /// Sets the yielded version of o at l to v.
    void setYield(const NodeID l, const NodeID o, const Version v);

    inline VDGManager& getVDGManager()
    {
        return vdgManager;
    }

    /// Override solveWorklist to use batch version propagation
    virtual void solveWorklist() override;

    /// Propagate versions batch-wise on all updated VDGs
    void propagateAllVersions();

    /// Consumed versions in object-major layout (o:l:v).
    ObjToLocVersionMap consume;
    /// Yielded versions in object-major layout (o:l:v, store-specific).
    ObjToLocVersionMap yield;
    /// Store-location indexed pending singleton objects whose consume->yield edge
    /// may still need virtual->solid upgrade during solving.
    Map<NodeID, NodeVector> pendingStoreObjsByLoc;

    /// Version dependency graph manager
    VDGManager vdgManager;

    /// o -> (version -> versions which rely on it).
    VersionRelianceMap versionReliance;
    /// o x version -> statement nodes which rely on that o/version.
    Map<NodeID, Map<Version, NodeBS>> stmtReliance;

    /// Priority worklists for staged processing
    /// Priority 0: Load nodes (processed first — produces data for other stmts)
    /// Priority 1: Other nodes (addr/copy/phi/gep — processed second)
    /// Priority 2: Store nodes (processed last — consumes data)
    FIFOWorkList<NodeID> priorityWorklist[3];

    //===--- Caching ---===//

    /// Unified stmt points-to cache by SVFG node id (used by load/gep deltas).
    /// For loads: cache stores seen qpt; bits are selectively reset on reliance.
    /// For geps: cache stores seen srcPts.
    std::vector<PointsTo> stmtPtsCache;

    /// Lazy-init constant object cache: 0=unknown, 1=constant, 2=non-constant.
    /// Avoids upfront scan of all PAG nodes; populated on first query per object.
    mutable std::vector<u8_t> constantObjCache;

    /// Lazy check whether an object is constant (cached after first call)
    inline bool isConstantObjCached(NodeID id) const
    {
        if (id >= constantObjCache.size())
            constantObjCache.resize(id + 1, 0);
        u8_t &entry = constantObjCache[id];
        if (entry == 0)
            entry = pag->isConstantObj(id) ? 1 : 2;
        return entry == 1;
    }

    Set<NodeID> prelabeledObjects;
    /// Objects pre-estimated as non-strong-update candidates.
    Set<NodeID> fiObjects;
    /// Object -> prelabel starting SVFG node ids used by buildVDG step1.
    Map<NodeID, NodeVector> objStartingNodes;

    /// Points-to DS for working with versions.
    BVDataPTAImpl::VersionedPTDataTy *vPtD;

    /// deltaMap[l] means SVFG node l is a delta node, i.e., may get new
    /// incoming edges due to OTF callgraph construction.
    std::vector<bool> deltaMap;

    /// deltaSourceMap[l] means SVFG node l *may* be a source to a delta node
    /// through an dge added as a result of on-the-fly callgraph
    /// construction.
    std::vector<bool> deltaSourceMap;

    /// isStoreMap[l] means SVFG node l is a store node.
    std::vector<bool> isStoreMap;

    /// isLoadMap[l] means SVFG node l is a load node.
    std::vector<bool> isLoadMap;

    /// Additional statistics.
    //@{
    u32_t numPrelabelVersions; ///< Number of versions created during prelabeling.
    u32_t numPrelabelNodes;    ///< Number of load nodes participating in prelabeling.
    u32_t numPrelabelFIObjs;   ///< Number of pre-labeled FI objects.

    double prelabelingTime;  ///< Time to prelabel SVFG.
    double versionPropTime;  ///< Time to propagate versions to versions which rely on them.
    double vdgBuildTime;     ///< Time to execute the full buildVDG pipeline.
    //@}

    static VersionedFlowSensitive *vfspta;

};

} // End namespace SVF

#endif /* VFS_H_ */
