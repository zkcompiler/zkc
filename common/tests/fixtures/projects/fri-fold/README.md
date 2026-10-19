# FRI pair folding

This KoalaBear example applies the public `fri::fold_value` arithmetic to a
batch of prepared `(low, high, inverse_x, next)` records. It returns every folded
value and its residual `folded - next`. The four input vectors must have equal
lengths; a Local builder checks their shapes and constructs the records.

The Math consumer obtains a record projection through `pair_rows(batch)`.
Indices of the original `batch.pairs` read that view, then read the unfiltered
collect result when computing residuals. No record encoding is needed at the
Host boundary. Empty inputs return two empty sequences.

With built tools on `PATH`, run from the repository root:

```sh
zkc run --project=common/tests/fixtures/projects/fri-fold/zkc.toml fri_fold::Demo
```

The supplied [participant inputs](inputs/fri_fold.Demo/P.json) describe
`f(X) = 3 + 2X + X^2 + 4X^3`, `beta = 5`, and the size-four domain with
`omega = 2113994754` over `p = 2130706433`. Natural order pairs `x` and `-x`
across the two contiguous halves. The folded polynomial is `13 + 21Y`;
outputs are `folded = [34, 2130706425]` and `residuals = [0, 0]`.
Increasing the second `next` by one gives residuals `[0, 2130706432]`.

Callers supply valid inverses of two and each nonzero domain point. Domain-point
calculation and inversion remain Local in the complete
[FRI library](../../../../../libraries/protocols/polynomial/fri/lib.zkc); this slice performs no inversion.
It assumes the pair values and claimed next layer are already prepared. It does
not authenticate openings, enforce a degree bound, or implement a complete FRI
proof. Zero residuals establish only these supplied pair equations.

The [native tests](../../../protocol/test_compositional_protocol_math.py)
compare against independently folded polynomial coefficients and the existing
`poly.even_odd_fold` kernel, including shifted cosets, empty inputs, and changed
next-layer values. They select default, `--no-simplify`, `--no-finite-bulk`, and
both flags; arithmetic agreement alone does not show that an optimization ran.
