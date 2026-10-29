#include "WPA/LOPA.h"
#include "Util/PTAStat.h"
#include "Util/Options.h"
#include <algorithm>

using namespace SVF;

namespace SVF {
class LOPAStat : public PTAStat {
    LOPA* p;
public:
    explicit LOPAStat(LOPA* analysis) : PTAStat(analysis), p(analysis) {}
    void performStat() override {
        endClk();
        PTAStat::performStat();
        collectPointerStats();
        recordPhaseTimes();
        printStat("LOPA Pointer Analysis Stat");
        printGraphCounters();
    }
private:
    void collectPointerStats() {
        uint64_t pointers = 0, pairs = 0, nonempty = 0, maximum = 0;
        for (const auto& entry : *p->getPAG()) {
            if (!p->getPAG()->isValidTopLevelPtr(entry.second)) continue;
            const uint64_t size = p->getPts(entry.first).count();
            ++pointers; pairs += size; nonempty += size != 0;
            maximum = std::max(maximum, size);
        }
        timeStatMap["TopLevelPointers"] = pointers;
        timeStatMap["TopLevelNonempty"] = nonempty;
        timeStatMap["TopLevelPtsPairs"] = pairs;
        timeStatMap["AvgTopLvlPtsSize"] = pointers ? double(pairs) / pointers : 0;
        PTNumStatMap["MaxTopLvlPtsSize"] = maximum;
    }
    void recordPhaseTimes() {
        const auto& copy = p->copySolver.statistics();
        timeStatMap["TotalTime"] = (endTime - startTime) / TIMEINTERVAL;
        timeStatMap["SolveTime"] = p->solveTime;
        timeStatMap["PUSConstructionTime"] = p->constructionTime;
        timeStatMap["LOPAOfflineTime"] = p->offlineTime;
        timeStatMap["LOPAExportTime"] = p->exportTime;
        timeStatMap["PUSValueBuildTime"] = p->valueBuildTime;
        timeStatMap["PUSNodeReductionPct"] = p->parent.empty() ? 0 : 100.0 * copy.merged / p->parent.size();
        timeStatMap["PUSEdgeReductionPct"] = p->copyEdges ? 100.0 * copy.sccEdgesRemoved / p->copyEdges : 0;
        if (Options::LOPAProfile()) {
            timeStatMap["PUSProfileSCC"] = copy.sccTime;
            timeStatMap["PUSProfileMerge"] = copy.mergeTime;
            timeStatMap["PUSProfileCopy"] = copy.copyTime;
            timeStatMap["PUSProfileIndirect"] = p->indirectTime;
            timeStatMap["PUSExportNodeTime"] = p->exportNodeTime;
            timeStatMap["PUSExportCopyTime"] = p->exportCopyTime;
            timeStatMap["PUSExportMapTime"] = p->exportMapTime;
        }
    }
    void printGraphCounters() {
        const auto& copy = p->copySolver.statistics();
        // Keep 64-bit counts exact and always separate long labels from values.
        auto count = [](const char* name, uint64_t value) {
            SVFUtil::outs() << name << " " << value << "\n";
        };
        count("PUSInitialNodes", p->initialNodes);
        count("PUSInitialCopyEdges", p->initialCopies);
        count("PUSMemoryBindings", p->memory.size());
        count("PUSValueBindings", p->values.size());
        count("PUSConstraintGroups", p->constraintGroups.size());
        count("PUSCoalescedGroups", p->coalescedGroups);
        count("PUSLiveConstraintGroups", p->constraintGroups.size() - p->coalescedGroups);
        count("PUSNewFIObjects", p->newFIObjects);
        count("PUSNodes", p->parent.size());
        count("PUSLiveNodes", p->parent.size() - copy.merged);
        count("PUSMergedNodes", copy.merged);
        count("PUSSCCMerges", copy.sccMerges);
        count("PUSMaxSCCMembers", copy.maxSCCMembers);
        count("PUSSCCVisits", copy.visits);
        count("PUSCopyAttempts", p->copyAttempts);
        count("PUSCopyInvalid", p->copyInvalid);
        count("PUSCopySelf", p->copySelf);
        count("PUSCopyDuplicates", p->copyDuplicates);
        count("PUSCopyEdgesInserted", p->copyEdges);
        count("PUSLiveCopyEdges", p->constraints->copyCount());
        count("PUSSCCEdgesTouched", copy.sccEdgesTouched);
        count("PUSSCCEdgesRebuilt", copy.sccEdgesRebuilt);
        count("PUSSCCEdgesRemoved", copy.sccEdgesRemoved);
        count("PUSCopyUnions", p->copyUnions);
        count("PUSRounds", p->rounds);
        count("PUSStrongToWeak", p->strongToWeak);
    }
};
}

PTAStat* LOPA::createStat() { return new LOPAStat(this); }
