//===- VDG.cpp -- Version Dependency Graph ---------------------------------//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2025>  <Yulei Sui>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.
//
// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//

/*
 * VDG.cpp
 *
 *  Created on: Jan 31, 2026
 *      Author: Codex
 */

#include "Graphs/VDG.h"
#include "Graphs/GraphPrinter.h"
#include "Util/Options.h"
#include "Util/SVFUtil.h"
#include <sstream>

using namespace SVF;

VDGNode::iterator VDGNode::directOutEdgeBegin()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeBegin();
    return solidOutEdges.begin();
}

VDGNode::iterator VDGNode::directOutEdgeEnd()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeEnd();
    return solidOutEdges.end();
}

VDGNode::iterator VDGNode::directInEdgeBegin()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeBegin();
    return solidInEdges.begin();
}

VDGNode::iterator VDGNode::directInEdgeEnd()
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeEnd();
    return solidInEdges.end();
}

VDGNode::const_iterator VDGNode::directOutEdgeBegin() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeBegin();
    return solidOutEdges.begin();
}

VDGNode::const_iterator VDGNode::directOutEdgeEnd() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::OutEdgeEnd();
    return solidOutEdges.end();
}

VDGNode::const_iterator VDGNode::directInEdgeBegin() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeBegin();
    return solidInEdges.begin();
}

VDGNode::const_iterator VDGNode::directInEdgeEnd() const
{
    if (VDG::detectVE())
        return GenericVDGNodeTy::InEdgeEnd();
    return solidInEdges.end();
}

void VDG::setDetectVE(bool flag)
{
    Options::DetectVE.setValue(flag);
}

bool VDG::detectVE()
{
    return Options::DetectVE();
}

void VDG::dump(const std::string& filename)
{
    std::string name = filename;
    if (name.size() >= 4 && name.substr(name.size() - 4) == ".dot")
        name = name.substr(0, name.size() - 4);
    GraphPrinter::WriteGraphToFile(SVFUtil::outs(), name, this);
}

void VDG::view()
{
    SVF::ViewGraph(this, "Version Dependency Graph");
}

namespace SVF
{

template<>
struct DOTGraphTraits<VDG*> : public DefaultDOTGraphTraits
{
    typedef VDGNode NodeType;

    DOTGraphTraits(bool isSimple = false)
        : DefaultDOTGraphTraits(isSimple)
    {
    }

    static std::string getGraphName(VDG*)
    {
        return "VDG";
    }

    static std::string getNodeLabel(NodeType *node, VDG*)
    {
        std::stringstream raw;
        raw << "o=" << node->getObject() << "\\nv=" << node->getVersion();
        return raw.str();
    }

    static std::string getNodeAttributes(NodeType *node, VDG*)
    {
        const bool loadConsume = node->isLoadConsume();
        const bool storeYield = node->isStoreYield();

        std::string attrs;
        attrs += loadConsume ? "shape=box" : "shape=ellipse";
        attrs += ", style=filled";
        attrs += storeYield ? ", fillcolor=mistyrose" : ", fillcolor=white";
        return attrs;
    }

    template<class EdgeIter>
    static std::string getEdgeAttributes(NodeType*, EdgeIter EI, VDG*)
    {
        VDGEdge* edge = *(EI.getCurrent());
        if (edge && edge->isVirtualEdge())
            return "style=dashed";
        return "";
    }
};

} // namespace SVF
