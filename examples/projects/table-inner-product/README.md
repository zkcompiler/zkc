# Table inner-product claims

This arithmetic component computes two seeded claims over an evaluation table:

- `square_claim = initial + sum(values[i] * values[i])`;
- `weighted_claim = initial + sum(values[i] * (factor * values[i] + offset))`.

Such table inner products occur in Sumcheck and polynomial commitment opening
reductions. This example supplies the arithmetic only, with no commitments,
challenge sampling, proof messages or verification of a claimed value.

The private generic `inner_product_claim` requires `equal_extent(left, right)`.
One call repeats the same vector. The other uses a distinct vector constructed
by an unfiltered total collect over `indices(values)`, which establishes equal
extent. Arbitrary input vectors are not assumed to have equal lengths, and no
runtime `require` supplies a mathematical premise. Nested ordinary helpers
forward the bound index, reorder container arguments and return both reads
before the fold adds their product.

With built tools on `PATH`, run from the repository root:

```sh
zkc run --project=examples/projects/table-inner-product/zkc.toml table_claims::Demo
zkc run --project=examples/projects/table-inner-product/zkc.toml table_claims::ExtensionDemo
```

`Demo` uses KoalaBear; `ExtensionDemo` uses KoalaBear Ext8. The supplied
[base-field inputs](inputs/table_claims.Demo/P.json) construct weights `[5,7,11]`
and return `square_claim = 45`, `weighted_claim = 93`. The
[extension inputs](inputs/table_claims.ExtensionDemo/P.json) have nonzero
extension coordinates. An empty table returns `initial` for both claims.

The [integration tests](../../../common/tests/protocol/test_indexed_callback_selection.py)
compare both fields against independent arithmetic with default compilation,
`--no-simplify`, `--no-finite-bulk`, and both flags. They separately inspect
executable dot-product sites and the indexed collection's vector arithmetic.
See the [finite library guide](../../../libraries/README.md#finite-computations)
for total access and domain formation.
