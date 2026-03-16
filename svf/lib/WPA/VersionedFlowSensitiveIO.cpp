//===- VersionedFlowSensitiveIO.cpp -- I/O helpers for versioned flow-sensitive PTA ---//

/*
 * VersionedFlowSensitiveIO.cpp
 *
 *  Created on: Mar 13, 2026
 */

#include "WPA/VersionedFlowSensitive.h"
#include "Util/SVFUtil.h"
#include <algorithm>
#include <fstream>
#include <sstream>
#include <system_error>

using namespace SVF;

void VersionedFlowSensitive::drawVersionDependencyGraph(const std::string& filename) const
{
    if (filename.empty())
        return;

    vdgManager.writeToFile(filename);
}

void VersionedFlowSensitive::dumpLocVersionMaps(void) const
{
    SVFUtil::outs() << "# LocVersion Maps\n";
    NodeVector objects;
    objects.reserve(consume.size() + yield.size());
    for (const ObjToLocVersionMap::value_type &ov : consume)
        objects.push_back(ov.first);
    for (const ObjToLocVersionMap::value_type &ov : yield)
        objects.push_back(ov.first);
    std::sort(objects.begin(), objects.end());
    objects.erase(std::unique(objects.begin(), objects.end()), objects.end());

    for (SVFG::iterator it = svfg->begin(); it != svfg->end(); ++it)
    {
        const NodeID loc = it->first;
        bool locPrinted = false;

        auto dumpAtLoc = [&](const bool useYield)
        {
            bool first = true;
            for (const NodeID o : objects)
            {
                const Version v = useYield ? getYield(loc, o) : getConsume(loc, o);
                if (v == invalidVersion) continue;
                if (!locPrinted)
                {
                    SVFUtil::outs() << "  " << "SVFG node " << loc << "\n";
                    locPrinted = true;
                }
                if (first)
                {
                    SVFUtil::outs() << "    " << (useYield ? "Yield   " : "Consume ") << ": ";
                }
                SVFUtil::outs() << (first ? "" : ", ") << "<" << o << ", " << v << ">";
                first = false;
            }
            if (!first) SVFUtil::outs() << "\n";
        };

        dumpAtLoc(false);
        dumpAtLoc(true);
    }
}

void VersionedFlowSensitive::dumpMeldVersion(MeldVersion &v)
{
    SVFUtil::outs() << "[ ";
    bool first = true;
    for (unsigned e : v)
    {
        if (!first)
        {
            SVFUtil::outs() << ", ";
        }

        SVFUtil::outs() << e;
        first = false;
    }

    SVFUtil::outs() << " ]";
}

void VersionedFlowSensitive::readPtsFromFile(const std::string& filename)
{
    /// Initialization for the Solver
    initialize();
    /// Load the pts from file
    if(!filename.empty())
    {
        SVFUtil::outs() << "Loading versioned pointer analysis results from '" << filename << "'...";

        std::ifstream F(filename.c_str());
        if (!F.is_open())
        {
            SVFUtil::outs() << "  error opening file for reading!\n";
            return ;
        }
        readAndSetObjFieldSensitivity(F,"------");

        readVersionedAnalysisResultFromFile(F);

        readPtsResultFromFile(F);

        readGepObjVarMapFromFile(F);

        readAndSetObjFieldSensitivity(F,"");

        // Update callgraph
        updateCallGraph(pag->getIndirectCallsites());

        F.close();
        SVFUtil::outs() << "\n";
    }

    /// finalize the analysis
    finalize();
}

void VersionedFlowSensitive::solveAndwritePtsToFile(const std::string& filename)
{
    /// Initialization for the Solver
    initialize();
    if(!filename.empty())
        writeObjVarToFile(filename);
    solveConstraints();
    if(!filename.empty())
    {
        writeVersionedAnalysisResultToFile(filename);
        writeToFile(filename);
    }
    /// finalize the analysis
    finalize();
}

void VersionedFlowSensitive::writeVersionedAnalysisResultToFile(const std::string& filename)
{
    SVFUtil::outs() << "Storing Versioned Analysis Result to '" << filename << "'...";
    std::error_code err;
    std::fstream f(filename.c_str(), std::ios_base::app);
    if (!f.good())
    {
        SVFUtil::outs() << "  error opening file for writing!\n";
        return;
    }

    for (const VersionedFlowSensitive::ObjToLocVersionMap *lvm :
         {
             &this->consume, &this->yield
         })
    {
        for (const VersionedFlowSensitive::ObjToLocVersionMap::value_type &ovm : *lvm)
        {
            const NodeID o = ovm.first;
            if (!ovm.second) continue;
            for (const VersionedFlowSensitive::LocToVersionMap::value_type &lv : *(ovm.second))
            {
                const Version v = lv.second;
                if (vPtD->getPts(atKey(o, v)).empty()) continue;

                f <<"[ " <<o <<" " <<v<<" ]"<< " -> { ";
                const PointsTo &ovPts = vPtD->getPts(atKey(o, v));
                if (!ovPts.empty())
                {
                    for (NodeID n: ovPts)
                    {
                        f << n << " ";
                    }
                }
                else
                {
                    f << " ";
                }
                f << "}\n";
            }
        }
    }

    f << "---VERSIONED---\n";

    f.close();
    if (f.good())
    {
        SVFUtil::outs() << "\n";
        return;
    }
}

void VersionedFlowSensitive::readVersionedAnalysisResultFromFile(std::ifstream& F)
{
    std::string line;
    std::string delimiter1 = " -> { ";
    std::string delimiter2 = " }";
    while (F.good())
    {
        // Parse a single line in the form of "[ var version ] -> { obj1 obj2 obj3 }"
        getline(F, line);
        if (line == "---VERSIONED---")     break;
        std::string pair = line.substr(line.find("[ ")+1, line.find(" ]"));

        // Parse VersionKey
        std::istringstream ss(pair);
        NodeID nodeID;
        Version nodeVersion;
        ss>> nodeID >> nodeVersion;
        VersionedVar keyPair = atKey(nodeID,nodeVersion);

        // Parse Point-to set
        size_t pos = line.find(delimiter1);
        if (pos == std::string::npos)    break;
        if (line.back() != '}')     break;
        pos = pos + delimiter1.length();
        size_t len = line.length() - pos - delimiter2.length();
        std::string objs = line.substr(pos, len);
        PointsTo dstPts;
        if (!objs.empty())
        {
            std::istringstream pt(objs);
            NodeID obj;
            while (pt.good())
            {
                pt >> obj;
                dstPts.set(obj);
            }
        }

        // union point-to reuslt
        vPtD->unionPts(keyPair, dstPts);
    }

}
