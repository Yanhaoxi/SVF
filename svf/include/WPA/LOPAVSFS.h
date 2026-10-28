//===- LOPAVSFS.h -- LOPA frontend + VSFS-style propagation backend --------//
//
// Ablation variant "B": reuse LOPA's offline compression frontend
// (prelabel + buildVDG) unchanged, but solve with the VSFS object-version
// propagation algorithm instead of LOPA's VDG batch solver.
//
// The solver half is a faithful port of VersionedFlowSensitive's propagation
// (propagateVersion / processLoad / processStore / processNode /
// updateConnectedNodes). Online VDG SCC contraction is deliberately not used.
//
//===----------------------------------------------------------------------===//

#ifndef LOPAVSFS_H_
#define LOPAVSFS_H_

#include "Graphs/SVFGNode.h"
#include "WPA/LOPA.h"

namespace SVF
{

/*!
 * LOPA frontend (offline compression) with a VSFS-style propagation backend.
 */
class LOPAVSFS : public LOPA
{
    friend class LOPAVSFSStat;

public:
    typedef Map<NodeID, Map<Version, std::vector<Version>>> VersionRelianceMap;
    typedef Map<VersionedVar, const DummyVersionPropSVFGNode *> VarToPropNodeMap;

    LOPAVSFS(SVFIR *_pag, PTATY type = LOPA_VSFS_WPA);

    virtual void initialize() override;
    virtual void finalize() override;

    /// Get PTA name
    const std::string PTAName() const override
    {
        return "LOPAVSFS";
    }

    /// Methods to support type inquiry through isa, cast, and dyn_cast
    //@{
    static inline bool classof(const LOPAVSFS *)
    {
        return true;
    }
    static inline bool classof(const PointerAnalysis *pta)
    {
        return pta->getAnalysisTy() == LOPA_VSFS_WPA;
    }
    //@}

    static LOPAVSFS *createLOPAVSFS(SVFIR *_pag)
    {
        if (lopavsfs == nullptr)
        {
            lopavsfs = new LOPAVSFS(_pag);
            lopavsfs->analyze();
        }
        return lopavsfs;
    }

    static void releaseLOPAVSFS()
    {
        if (lopavsfs) delete lopavsfs;
        lopavsfs = nullptr;
    }

    /// Versus LOPA, online compression is disabled for this variant.
    bool usesOnlineCompression() const
    {
        return false;
    }

protected:
    bool processLoad(const LoadSVFGNode* load) override;
    bool processStore(const StoreSVFGNode* store) override;
    bool processGep(const GepSVFGNode* edge) override;
    void processNode(NodeID n) override;
    void updateConnectedNodes(const SVFGEdgeSetTy& newEdges) override;

    /// Revert LOPA's priority worklists to the base FIFO worklist.
    void pushIntoWorklist(NodeID id) override;
    void solveWorklist() override;
    void solveConstraints() override;

    /// Propagate version v of o to every version relying on o:v.
    void propagateVersion(NodeID o, Version v);
    /// Propagate version v of o into version vp of o.
    void propagateVersion(const NodeID o, const Version v, const Version vp, bool time = true);

    /// Versions which rely on o:v (i.e. propagation successors of o:v).
    std::vector<Version> &getReliantVersions(const NodeID o, const Version v)
    {
        return versionReliance[o][v];
    }

    /// Location-major consume version lookup (matches VSFS's access pattern).
    inline Version getConsumeV(const NodeID l, const NodeID o) const
    {
        if (l >= vfsConsume.size()) return invalidVersion;
        const Map<NodeID, Version> &m = vfsConsume[l];
        const Map<NodeID, Version>::const_iterator it = m.find(o);
        return it == m.end() ? invalidVersion : it->second;
    }

    /// Location-major yield version lookup (stores only; non-stores use consume).
    inline Version getYieldV(const NodeID l, const NodeID o) const
    {
        if (isStore(l))
        {
            if (l >= vfsYield.size()) return invalidVersion;
            const Map<NodeID, Version> &m = vfsYield[l];
            const Map<NodeID, Version>::const_iterator it = m.find(o);
            return it == m.end() ? invalidVersion : it->second;
        }
        return getConsumeV(l, o);
    }

private:
    /// Translate the materialized LOPA frontend (compressed VDGs, consume/yield,
    /// per-node stmt reliance) into the VSFS propagation structures.
    void buildVFSStructures();

    /// o -> (v -> versions relying on o:v).
    VersionRelianceMap versionReliance;
    /// o:v -> dummy propagation SVFG node (schedules propagation).
    VarToPropNodeMap versionedVarToPropNode;
    /// Location-major consume/yield version maps (l -> {o -> v}), mirroring VSFS.
    std::vector<Map<NodeID, Version>> vfsConsume;
    std::vector<Map<NodeID, Version>> vfsYield;

    /// Versioned points-to data used by the VSFS propagation.
    BVDataPTAImpl::VersionedPTDataTy *versionedPTD;

    static LOPAVSFS *lopavsfs;
};

} // End namespace SVF

#endif /* LOPAVSFS_H_ */
