# VDG graph regressions

These C++ tests link against an existing SVF build. From the repository root,
configure with the same compiler/toolchain flags used for that build (see
`BUILD.md`). For the documented LLVM 16 / GCC 13 build:

```bash
# The uninstalled SVF export also lists this install-layout include directory.
mkdir -p Release-build/include/SVF
cmake -S tests/graph -B /tmp/lopa-graph-tests \
  -DSVF_DIR="$PWD/Release-build/lib/cmake/SVF" \
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
