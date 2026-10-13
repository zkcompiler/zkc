# LogUp row arithmetic

This KoalaBear example compresses tuples and evaluates individual LogUp row
equations. Inputs are a row-major flattened `tuple_values` vector, one `arity`,
equally sized `counts` and `reciprocals` vectors, and challenges `gamma`, `delta`.
A Local builder checks both column lengths and the tuple shape, then constructs
records internally. An arity of zero gives empty tuples with fingerprint zero;
zero rows return empty output sequences.

For each tuple `(t_0, ..., t_(k-1))`, an ordered Math fold carries
`(fingerprint, power)`, initially `(0, 1)`, producing
`fp = sum(delta^j * t_j)`. The returned record projection and the unfiltered
fingerprint collect are both read with indices of the original `batch.rows`.
The public [interaction helpers](../../../../../libraries/air/interaction.zkc) supply:

- `denominators`: `m * (gamma - fp) + 1 - m`;
- `reciprocal_residuals`: `m * (reciprocal * (gamma - fp) - 1)`;
- `boolean_residuals`: `m * (m - 1)`.

With built tools on `PATH`, run from the repository root:

```sh
zkc run --project=common/tests/fixtures/projects/logup-rows/zkc.toml logup_rows::Demo
zkc run --project=common/tests/fixtures/projects/logup-rows/zkc.toml logup_rows::CompressionWeights
```

The supplied [row inputs](inputs/logup_rows.Demo/P.json) use tuples `[1,3]`,
`[4,2]`, `[5,3]`, counts `[1,1,0]`, `gamma = 11`, and `delta = 2`.
Outputs are fingerprints `[7,8,11]`, denominators `[4,3,1]`, and two residual
vectors `[0,0,0]`. Increasing the first reciprocal by one changes its residual
to `4`. The inactive third row has raw denominator zero, but gated denominator
one; the slice does no inversion. Reciprocal residuals do not force an inactive
reciprocal to zero. Boolean residuals remain necessary even when reciprocal
equations vanish.

The separate `CompressionWeights` Entry uses BLS12-381.Fr for native fixed-array
support. `compression_weights(delta)` collects four powers with
`field_array::collect(range(0, forwarded_index(4)), ...)`: the endpoint is an
actual literal forwarded through an identity helper. Its
[sample input](inputs/logup_rows.CompressionWeights/P.json) gives `[1,2,4,8]`;
`delta = 0` gives `[1,0,0,0]`.

This is a mathematical slice with supplied reciprocals and challenges. It does
not build a complete interaction argument, enforce cross-table multiset
equality, or authenticate transcript challenges or openings. The existing full
LogUp construction retains its explicit abort for an active zero denominator.
Zero row residuals are not a complete proof.

The [native tests](../../../protocol/test_compositional_protocol_math.py)
use independent modular tuple sums and reciprocals, including coordinate order,
empty tuples and rows, inactive zero denominators, and perturbed reciprocals.
Both Entries run under default, `--no-simplify`, `--no-finite-bulk`, and both
flags. The fixed-array helper is also tested through a small importing Entry.
These comparisons establish arithmetic agreement, not optimization selection.
