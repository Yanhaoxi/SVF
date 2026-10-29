#include "Graphs/PUSMemoryMap.h"
#include <cstdlib>
#include <iostream>
#include <random>
#include <unordered_map>

using namespace SVF;

static void require(bool condition, const char* message) {
    if (!condition) {
        std::cerr << message << '\n';
        std::exit(1);
    }
}

int main() {
    constexpr NodeID missing = std::numeric_limits<NodeID>::max();
    PUSMemoryMap actual;
    std::unordered_map<uint64_t, NodeID> expected;
    require(actual.lookup(0) == missing, "Empty lookup must miss");
    actual.reserve(0);
    actual.reserve(1);
    auto insert = [&](uint64_t key, NodeID value) {
        const bool added = expected.emplace(key, value).second;
        require(actual.insert(key, value) == added, "Duplicate insertion result differs");
        require(actual.size() == expected.size(), "Binding count differs");
        require(actual.lookup(key) == expected.at(key), "Insertion did not preserve first value");
    };

    // Packed keys may use every bit. In particular, these are not sentinel keys.
    for (uint64_t key : {UINT64_C(0), UINT64_MAX, UINT64_MAX - 1,
                         UINT64_C(1) << 32, UINT64_C(1) << 63}) {
        insert(key, 0);
        insert(key, 123);
    }

    // Many locations can share one object: the location is entirely in high bits.
    // Include high object IDs as produced by reverse-dense allocation.
    for (uint64_t location = 0; location != 32768; ++location) {
        insert((location << 33) | (UINT64_C(0xfffffff0) << 1), NodeID(location));
        insert((location << 33) | (UINT64_C(0xfffffff0) << 1) | 1, NodeID(location + 1));
    }
    actual.reserve(expected.size() * 2);
    actual.reserve(1); // A smaller request must not lose existing entries.
    std::mt19937_64 generator(3102026);
    for (unsigned i = 0; i != 65536; ++i)
        insert(generator(), i);
    for (const auto& entry : expected)
        require(actual.lookup(entry.first) == entry.second, "Growth lost a binding");
    for (unsigned i = 0; i != 65536; ++i) {
        const uint64_t key = generator();
        const auto found = expected.find(key);
        const NodeID value = found == expected.end() ? missing : found->second;
        require(actual.lookup(key) == value, "Hit/miss lookup differs");
    }
    std::cout << "PASS " << actual.size() << " packed memory bindings\n";
}
