# Finite vector reductions

The [Entry](main.zkc) computes the same weighted sum with imported `∑`,
named `reduce vec::sum`, and `vec::dot`. It also computes `∏ [x in left] { x + α }`,
which captures the scalar `α` once for all rows. The vector library supplies
both named functions and reduction bindings; importing a module activates its
public notation.

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

The optional fusion can replace the multiply-map/sum with ordered shape checks
and a native dot operation. It preserves values and shape refusals under
sufficient resources; resource exhaustion can differ. Other formulas retain the
ordinary map and reducer path. The [integration controls](../../../tests/protocol/test_finite_reductions.py)
exercise both choices through the common Host, alongside independent field arithmetic.

See the [language guide](../../../docs/language/notation.md) for scope and imports,
and the [compiler guide](../../../docs/compiler/mathematics.md) for the optimization boundary.
