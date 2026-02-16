//===- SmallDenseSet.h -- Small-then-hash set container -------------------//
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

#ifndef SMALLDENSESET_H_
#define SMALLDENSESET_H_

#include "Util/GeneralType.h"
#include <algorithm>
#include <vector>

namespace SVF
{

/// A sparse set optimized for small cardinality:
/// - Small sets: linear scan over compact vector.
/// - Larger sets: transparently enables hash lookup while keeping compact iteration order.
template<typename T, size_t InlineThreshold = 8, typename THash = Hash<T>, typename TEq = std::equal_to<T>>
class SmallDenseSet
{
public:
    using value_type = T;
    using storage_type = std::vector<T>;
    using iterator = typename storage_type::iterator;
    using const_iterator = typename storage_type::const_iterator;

    SmallDenseSet() = default;

    inline bool empty() const
    {
        return values_.empty();
    }

    inline size_t size() const
    {
        return values_.size();
    }

    inline void reserve(size_t n)
    {
        values_.reserve(n);
        if (useHash_)
            hash_.reserve(n);
    }

    inline void clear()
    {
        values_.clear();
        hash_.clear();
        useHash_ = false;
    }

    inline iterator begin()
    {
        return values_.begin();
    }

    inline const_iterator begin() const
    {
        return values_.begin();
    }

    inline iterator end()
    {
        return values_.end();
    }

    inline const_iterator end() const
    {
        return values_.end();
    }

    inline const_iterator cbegin() const
    {
        return values_.cbegin();
    }

    inline const_iterator cend() const
    {
        return values_.cend();
    }

    inline bool contains(const T& key) const
    {
        if (useHash_)
            return hash_.find(key) != hash_.end();
        return std::find(values_.begin(), values_.end(), key) != values_.end();
    }

    inline bool insert(const T& key)
    {
        if (useHash_)
        {
            auto ins = hash_.insert(key);
            if (!ins.second)
                return false;
            values_.push_back(key);
            return true;
        }

        if (std::find(values_.begin(), values_.end(), key) != values_.end())
            return false;
        values_.push_back(key);
        maybePromoteHash();
        return true;
    }

    inline bool erase(const T& key)
    {
        if (useHash_ && hash_.erase(key) == 0)
            return false;
        if (!useHash_ && std::find(values_.begin(), values_.end(), key) == values_.end())
            return false;

        const auto it = std::find(values_.begin(), values_.end(), key);
        if (it == values_.end())
            return false;

        // Swap-pop keeps erase O(1) after lookup; iteration order is intentionally unstable.
        if (it + 1 != values_.end())
            *it = values_.back();
        values_.pop_back();
        maybeDemoteHash();
        return true;
    }

private:
    inline void maybePromoteHash()
    {
        if (useHash_ || values_.size() <= InlineThreshold)
            return;
        hash_.reserve(values_.size());
        for (const T& v : values_)
            hash_.insert(v);
        useHash_ = true;
    }

    inline void maybeDemoteHash()
    {
        if (!useHash_)
            return;
        if (values_.size() > InlineThreshold)
            return;
        hash_.clear();
        useHash_ = false;
    }

    storage_type values_;
    Set<T, THash, TEq> hash_;
    bool useHash_ = false;
};

} // namespace SVF

#endif // SMALLDENSESET_H_
