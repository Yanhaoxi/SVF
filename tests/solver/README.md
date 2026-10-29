# Analysis regressions

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

For the CG adapter, check deferred Store bypass with an empty destination:

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

`-lopa-cg-store-policy=deferred` is the default. Explicit
`object-lower-bound` uses the existing LOPA rule and retains the earlier object
in this array example; disabling `-lopa-obj-fs-lower-bound` restores the deferred
result. The check also verifies the nonempty control, that the adapter option
does not affect pure CG, and rejection of an invalid policy value.
