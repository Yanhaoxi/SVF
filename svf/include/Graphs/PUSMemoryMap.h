#ifndef SVF_PUS_MEMORY_MAP_H
#define SVF_PUS_MEMORY_MAP_H

#include "Util/GeneralType.h"
#include <cassert>
#include <limits>
#include <stdexcept>

namespace SVF {

/// Memory bindings are inserted during construction and only queried afterward.
/// A vacant value marks an empty bucket, so every 64-bit key remains available.
class PUSMemoryMap {
    static constexpr NodeID vacant = std::numeric_limits<NodeID>::max();
    struct Bucket {
        uint64_t key = 0;
        NodeID value = vacant;
    };
    std::vector<Bucket> buckets;
    size_t entries = 0;

    static size_t hash(uint64_t key) {
        // Location occupies the high bits of the packed key; mix all 64 bits.
        key = (key ^ (key >> 30)) * UINT64_C(0xbf58476d1ce4e5b9);
        key = (key ^ (key >> 27)) * UINT64_C(0x94d049bb133111eb);
        return key ^ (key >> 31);
    }
    static size_t slot(const std::vector<Bucket>& table, uint64_t key) {
        const size_t mask = table.size() - 1;
        size_t index = hash(key) & mask;
        while (table[index].value != vacant && table[index].key != key)
            index = (index + 1) & mask;
        return index;
    }

public:
    size_t size() const { return entries; }

    void reserve(size_t expected) {
        if (expected == 0) return;
        size_t capacity = buckets.empty() ? 64 : buckets.size();
        // Keep at least one quarter of the buckets empty for linear probing.
        while (expected > capacity - capacity / 4) {
            if (capacity > buckets.max_size() / 2)
                throw std::length_error("PUS memory binding table is too large");
            capacity *= 2;
        }
        if (capacity == buckets.size()) return;
        std::vector<Bucket> grown(capacity);
        for (const Bucket& bucket : buckets)
            if (bucket.value != vacant) grown[slot(grown, bucket.key)] = bucket;
        buckets.swap(grown);
    }

    bool insert(uint64_t key, NodeID value) {
        assert(value != vacant && "Memory bindings must name a live solver node");
        if (buckets.empty()) reserve(1);
        size_t index = slot(buckets, key);
        if (buckets[index].value != vacant) return false;
        if (entries + 1 > buckets.size() - buckets.size() / 4) {
            reserve(entries + 1);
            index = slot(buckets, key);
        }
        buckets[index] = {key, value};
        ++entries;
        return true;
    }

    NodeID lookup(uint64_t key) const {
        return buckets.empty() ? vacant : buckets[slot(buckets, key)].value;
    }
};

} // namespace SVF
#endif
