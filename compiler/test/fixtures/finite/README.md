# Finite computation controls

These handwritten programs exercise the Data/Local/Algebra ABI without source
frontend emission. `finite_computation.cpp` checks formation, full compilation,
resource origins, fixed-point dependencies and mutations of actual realization
candidates. `finite_runtime.py` executes compiler-produced authenticated bundles
with independent integer expectations and native failure reports.

Run the compiler controls, including the checked-access prerequisite gate:

```sh
build/compiler/test/zkc-finite_computation-test --checked-access
```

Run the native corpus with matching compiler/runtime builds:

```sh
python3 compiler/test/support/finite_runtime.py \
  --compiler build/compiler/zkc-compile --runtime target/release/zkc \
  --output build/experiments/finite-computation --checked-access
```

The common integration test `kernels/test_finite_computation.py` runs this complete
native corpus. Omitting `--checked-access` is an explicit partial integration
control for builds without `field_array.get` and `matrix.get`; it does not establish
complete container or matrix fallback support.

The fixtures cover strict zip (including ignored, empty, filtered and dead-domain
factors), product versus dependent nesting, predicate/body/eager stop order,
materialization before ordinary reducers, mixed state/item/capture types, affine
successors, branch/match fallback, coordinates including sparse zeros, fixed-size
collection, bounded total lookups and helper-body correspondence. Total zip uses
verified equality and argument substitution. Native recognition is checked for
sum, product, dot, MSM, elementwise fields and selected matrix contractions.

Large controls use 131072 field elements. Only element capacity is increased;
ordinary instruction and loop ceilings remain unchanged. Bulk sum/product/dot
and elementwise materialization must complete. The corresponding generic sum
must still exhaust the ordinary loop budget. This is bounded compiler/native
execution evidence under declared kernel semantics, not a formal refinement or
security theorem.
