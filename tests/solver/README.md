# Analysis regressions

Check that VDG pass profiling preserves the complete points-to sets and actual
VDG summaries for PUS, CG Wave, CG SFR and VSFS:

```bash
python3 tests/solver/check_vdg_pass_profile.py PUS-build/bin/wpa \
  --extapi=PUS-build/lib/extapi.bc
```

The check covers coverage and strategy sweeps, both storage backends, late
recursion and its nonrecursive control, empty Store targets, the object lower
bound off, offline compression off, and empty input graphs. Add
`--reference-wpa=/path/to/pre-change/wpa` to compare the old statistics and
unprofiled analysis results as well. `--output=/tmp/vdg-pass-profile` retains
commands, logs and a JSON summary.

Check mutable and persistent storage in the four CG modes:

```bash
python3 tests/solver/check_cg_ptd.py CGPTD-build/bin/wpa \
  --extapi=CGPTD-build/lib/extapi.bc
```

The check compares complete points-to sets, checks late recursion and its
nonrecursive control, and verifies that CG delta operations reach the persistent
cache. The selected storage backend covers both value and memory cells.

From the repository root, after building `wpa`:

```bash
python3 tests/solver/check_indirect_recursion.py Release-build/bin/wpa \
  --extapi=Release-build/lib/extapi.bc
```

The test checks that discovering an indirect recursive call weakens stores to a
local stack object even when the stores' pointer operands have not changed. It
also checks that the corresponding nonrecursive program retains strong updates.
Both cases run with default compression and with `-lopa-no-offline`. Node IDs are
resolved from the generated PAG, rather than assumed from allocation order.

For the CG adapter, check Store preservation with an empty destination:

```bash
python3 tests/solver/check_empty_target_store.py Integration-build/bin/wpa \
  --extapi=/home/yhx/PTA/labv1/lib/extapi.bc --analysis=-lopa-cgfspta \
  --flag=-cg-sfr=true --output=/tmp/cg-empty-store-regression
```

The preanalysis sees an array object in the Store destination, but a preceding
strong update removes it in the final analysis. The Store must not activate its
bypass while that destination is empty. A nonempty control verifies that weak
updates still preserve both old and new contents. Both cases run with offline
compression enabled and disabled. Logs and PAGs are retained when `--output` is
provided.

Check both selectable Store policies with the same two backends:

```bash
python3 tests/solver/check_store_policy.py Integration-build/bin/wpa \
  --extapi=/home/yhx/PTA/labv1/lib/extapi.bc --output=/tmp/cg-store-policy
```

`-lopa-obj-fs-lower-bound` is enabled by default for LOPA and LOPA+CG.
The check covers default/on/off settings, empty and nonempty Store targets,
compression on/off, and both CG backends plus PUS. Pure CG is checked separately
and is unaffected by the offline lower-bound switch. With the lower bound on,
the empty-target array case retains the old object; with it off, that result is
empty. Run with `--ptd=mutable` and `--ptd=persistent` to check both stores.
