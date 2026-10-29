# Graph and container regressions

These C++ tests link against an existing SVF build. From the repository root,
configure with the same compiler/toolchain flags used for that build (see
`BUILD.md`). For the documented LLVM 16 / GCC 13 build:

```bash
# The uninstalled SVF export also lists this install-layout include directory.
mkdir -p PUS-build/include/SVF
cmake -S tests/graph -B /tmp/lopa-graph-tests \
  -DSVF_DIR="$PWD/PUS-build/lib/cmake/SVF" \
  -DLLVM_DIR=/usr/lib/llvm-16/lib/cmake/llvm \
  -DCMAKE_C_COMPILER=clang-16 \
  -DCMAKE_CXX_COMPILER=clang++-16 \
  -DCMAKE_C_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13 \
  -DCMAKE_CXX_FLAGS=--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13
cmake --build /tmp/lopa-graph-tests
ctest --test-dir /tmp/lopa-graph-tests --output-on-failure
```

`vdg_scc_representative` checks that union by size updates the SCC topological
order, and that facts held by either the discarded root or the surviving
representative propagate to a downstream load and trigger its notification.
The checks also run in release builds with `NDEBUG`.

`profile_self_loops` compares profiling and production compression on a
store-to-load diamond with a self-loop. It covers must and may self-loops,
checks that isolated endpoints remain in the raw node count, and verifies that
SPC reaches the same one-node result with both store and load annotations.

`pus_memory_map` compares the memory binding table against `std::unordered_map`
through insertion, duplicate insertion, growth, explicit reservation and missing
lookups. Keys cover all 64 bits, high object IDs, and many locations sharing one
object. Checks remain active in release builds.

`pus_graph_lifecycle` compares both directions of the Copy graph and its edge
count against an independent edge set. It covers duplicate and self-edge
insertion, adjacent component contraction, batch detachment, node retirement,
growth with live adjacency, and repeated small/large adjacency transitions.
A 20,000-node bidirectional star exercises high-degree insertion and detachment.
Checks remain active with `NDEBUG`; the header-only graph can also be compiled
directly with AddressSanitizer and UndefinedBehaviorSanitizer.
