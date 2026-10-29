# Building LOPA

This tree is a fork of [SVF](https://github.com/SVF-tools/SVF) that adds the
version dependency graph (VDG) and load-observable flow-sensitive pointer analysis.
In `code/lopa_new`, `-lopa` selects the LOPA solver (PUS scheduling) with a fixed Andersen Wave
preanalysis. VDG construction keeps early merge DSU, then exports simplified
states into a Copy-only graph. Virtual edges are used during offline
simplification; GEP keeps SVF's object and field transfer rules.
This branch uses **LLVM 16**.

Analysis modes, common options and validation commands are documented in
[LOPA 与 CG 使用说明](docs/cg-integration.md).

## Layout

| Path         | Contents                                                          |
| ------------ | ----------------------------------------------------------------- |
| `svf/`       | SVF core library (analysis, graphs incl. `Graphs/VDG.*`)          |
| `svf-llvm/`  | LLVM front-end, tools (`wpa`, `mta`, `saber`, ...), `extapi.c`    |
| `cmake/`     | CMake modules (incl. `Modules/FindZ3.cmake`)                      |
| `docs/`      | [LOPA 与 CG 使用说明](docs/cg-integration.md)                 |
| `tests/solver/` | analysis regressions, see [README](tests/solver/README.md)    |
| `tests/graph/` | VDG and solver-container regressions, see [README](tests/graph/README.md) |

## Dependencies

Tested on Ubuntu 22.04:

- CMake >= 3.23, a build tool (`make` or `ninja`)
- LLVM 16 development files + tools
- Z3 (>= 4.8) development files
- LLVM runtime deps: `zlib1g-dev`, `libncurses-dev`, `libffi-dev`, `libxml2-dev`, `libzstd-dev`

```bash
sudo apt install \
  cmake make ninja-build clang-16 llvm-16-dev libclang-16-dev \
  libz3-dev zlib1g-dev libncurses-dev libffi-dev libxml2-dev libzstd-dev
```

## Configure & build (verified)

```bash
export LLVM_DIR=/usr/lib/llvm-16/lib/cmake/llvm

cmake -S . -B PUS-build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DCMAKE_C_COMPILER=clang-16 \
  -DCMAKE_CXX_COMPILER=clang++-16 \
  -DCMAKE_CXX_FLAGS="--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13" \
  -DCMAKE_C_FLAGS="--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13" \
  -DSVF_WARN_AS_ERROR=OFF \
  -DSVF_ENABLE_ASSERTIONS=OFF \
  -DBUILD_SHARED_LIBS=OFF \
  -DLLVM_DIR=$LLVM_DIR

cmake --build PUS-build --target wpa -j 24
```

Artifacts: `PUS-build/bin/wpa`, libraries under `PUS-build/lib/`, and
`PUS-build/lib/extapi.bc`.

### Toolchain caveats

- `setup.sh` / `build.sh` default to **LLVM 18** and will download it if
  `LLVM_DIR` is unset. For this branch point `LLVM_DIR` at a system LLVM 16
  (`/usr/lib/llvm-16/lib/cmake/llvm`) instead.
- If clang picks up a very new libstdc++ (e.g. GCC 16 headers) the build fails
  with `__normal_iterator ... incomplete type`. Pin the standard library with
  `--gcc-install-dir=/usr/lib/gcc/x86_64-linux-gnu/13` (or use `g++-13`).
  Use the same compiler and standard library for all analysis variants. This
  build includes the SFS, VSFS, LOPA and CG modes used for comparison.
- `SVF_WARN_AS_ERROR` defaults to `ON`; on newer compilers set it to `OFF` to
  avoid unrelated `-Werror` failures.
- `extapi.bc` is located relative to the build tree. When running a binary from
  an unusual working directory, pass `-extapi=<build>/lib/extapi.bc`.

## Run

```bash
./PUS-build/bin/wpa -lopa -ptd=persistent -node-alloc-strat=dense \
  -lopa-cg-store-policy=deferred \
  -extapi=./PUS-build/lib/extapi.bc \
  /home/yhx/PTA/labv1/test/soundness/simple/fs-load-cache-alias-loop.ll
```

Useful options:

- `-lopa` – LOPA
- `-lopa-cgfspta` – LOPA with the CG Wave backend; add `-cg-sfr=true` for CG SFR
- `-lopa-vsfs` – LOPA with the VSFS backend
- `-fspta` – upstream flow-sensitive analysis (baseline)
- `-vdg-stat` – print VDG statistics
- `-vdg-pass-order=SPC` – VDG simplification pass order (e.g. `SPC`, `SPCBLC`)
- `-lopa-cg-store-policy=deferred|object-lower-bound` – Store preservation policy
  for PUS and LOPA+CG; use the same policy in comparisons
- `-ptd=persistent -node-alloc-strat=dense` – shared experiment configuration

PUS and LOPA+CG require `-pre-field-sensitive=true`, `-opt-svfg=false`, and an
empty `-vdg-pass-profile` value, which are the defaults. Keep the build settings,
extapi file, field options and Store policy identical across compared modes.
