# Finite computations

This client combines ordinary scoped library calls with total mathematics:

- a strict zipped dot product directly inside a protocol;
- a sum of squares using indices with proven bounds;
- record collection and filtering;
- nested total matrix-row traversal.

`finite` callbacks use Local execution. `finite_math` callbacks are total Math;
their closed domain formation and every bounded read are checked before
realization. The matrix traversal is explicit, including empty rows. The dot
product rejects unequal vector lengths before entering its body.

The Entry is `example::Demo`. It selects KoalaBear and one participant P, with
inputs `xs`, `ys` and `matrix`. For `xs = [2, 3]`, `ys = [7, 11]` and the sparse
2-by-3 matrix with coefficients `(0, 0) = 2`, `(1, 2) = 7`, outputs are
`dot = 47`, `square_sum = 13`, `selected_sum = 5`, and `matrix_total = 9`.

See the [library guide](../../../libraries/README.md#finite-computations) and
[finite source contract](../../../docs/spec/language/definitions.md#finite-domains)
for argument order, capture snapshots, filters and mathematical admission.
