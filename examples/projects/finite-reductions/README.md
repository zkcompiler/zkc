# Finite vector reductions

The [Entry](main.zkc) computes the same weighted sum with imported `∑`,
named `finite::sum`, and `vec::dot`. It also computes `∏ x in left, (x + α)`,
which captures the scalar `α` once for all rows. The vector library supplies
vector operations and reexports general finite reduction bindings; importing a
module activates its public notation.

`zip(left, right)` requires equal lengths, including when one vector is empty.
Every collection is evaluated once before the scalar captures. Equal empty
vectors give sum zero and product one. A length mismatch stops execution
before arithmetic, so it produces no completed Entry outputs.

From the repository root, with built tools on `PATH`:

```sh
zkc check --project=examples/projects/finite-reductions/zkc.toml
zkc compile --project=examples/projects/finite-reductions/zkc.toml \
  example::Demo --output=finite-reductions.zkpkg
zkc compile --project=examples/projects/finite-reductions/zkc.toml \
  example::Demo --fuse-vector-reductions --output=finite-reductions-fused.zkpkg
```

Default preparation recognizes checked finite field contractions without the
optional map fusion flag. `--no-simplify` and unrecognized bodies use the ordered
loop fallback. The separate optional
fusion still handles explicit ring `map` followed by native vector sum. Both
paths preserve values and required shape checks under sufficient resources;
resource exhaustion can differ. The [integration controls](../../../common/tests/protocol/test_finite_reductions.py)
exercise these distinctions with independent field arithmetic.

The scalar spelling stays available to analysis before recipe selection. The
compiler recognizes its contraction equation, then selects an installed logical
operation and independently checks the emitted body. An unavailable recipe or
exhausted optional recognition allowance retains the ordered loop. The source
library API and imports are the same on both paths.

See the [language guide](../../../docs/language/notation.md) for scope and imports,
and the [compiler guide](../../../docs/compiler/mathematics.md) for the optimization boundary.
