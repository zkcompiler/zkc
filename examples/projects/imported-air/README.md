# Imported AIR residuals

This client evaluates an AIR written against Plonky3 through the ordinary `.zkc`
compiler and Entry Host. The [Plonky3 AIR adapter](../../../compiler/adapters/plonky3/README.md)
captures the recurrence AIR maintained in its
[client crate](../../../compiler/adapters/plonky3/client/src/lib.rs) and exports
its constraints as a shared [ring arena](../../../docs/spec/domains/ring-expressions.md).
[`main.zkc`](main.zkc) runs that arena with `ring.rows` and `ring.coefficients`
and returns the residuals as ordinary Entry results. No compiler or runtime code
recognizes the AIR; the program only names the arena's identity.

It is a maintained demonstration of an imported arena running from source. It
is not a proof protocol, and it is not a conformance claim about Plonky3.

## Authority and bindings

Each value the Host substitutes is fixed by a separate step:

1. The adapter evaluates the AIR with the upstream symbolic builder and writes
   [`export.json`](../../../compiler/adapters/plonky3/fixtures/recurrence/export.json).
   An export is a candidate relation: its arena, the slot read by each arena
   input, the fixed column, and the selector guarding each assertion.
2. [`instance.json`](../../../compiler/adapters/plonky3/fixtures/recurrence/instance.json)
   selects that export by its SHA-256 and states the height, 8, and the public
   values `x0`, `y0` and the final accumulator. Choosing it is the verifier
   configuration's decision; here the maintained fixture makes it.
3. The adapter's closed view binds the export to the instance, takes a trace and
   a selector law, and gives every arena input its value: trace cells on the
   current row and, cyclically, the next row; the fixed column from the export;
   public values from the instance; and selector values under the chosen law.
   Each `source-*.json` request carries this fully expanded vector. The adapter
   prepares it under the selected export and instance. A witness does not choose
   what an input means.
4. [`main.zkc`](main.zkc) declares `domain Export = ring(asset export)` over
   the captured `arena.json` and passes `Export` to both kernels. The compiler
   writes the arena's canonical SHA-256 into the static kernel parameter, so
   the identity is part of the compiled package.
5. The Host admits arena bytes from `--evaluators` only under that identity;
   the [manifest](../../../compiler/adapters/plonky3/fixtures/recurrence/ring-assets.json)
   lists the fixture's `arena.json`.

The program checks shapes and the arena identity. It cannot check that a vector
is the closed view of any trace. An all-zero vector sets every selector and
read to zero, so every residual is zero and `satisfied` is true. `satisfied`
therefore states only that every residual of the supplied assignments is zero.
Whether a trace satisfies the AIR rests on the adapter's view of an authorized
instance and that trace.

## Entries

The 14 arena inputs follow the export's `slots`: main columns `x`, `y`, `p`,
`acc` on the current row; `x`, `y`, `acc` on the next row; the fixed column;
the three public values; and the first-row, last-row and transition selectors.
The 9 outputs are the upstream assertions in emission order.

| Entry | Inputs | Kernel | Results |
|---|---|---|---|
| `RowResiduals` | KoalaBear `assignments`, `rows` of 14 values; `rows` | `ring.rows` | `residuals`, `rows` of 9 values; `satisfied` |
| `CoefficientResiduals` | KoalaBear `coefficients`, 14 polynomials of `width` ascending coefficients; `width` | `ring.coefficients` | `residuals`, 9 polynomials of a common width |
| `PointResiduals` | Ext8 `assignments`, `points` of 14 values; `points` | `ring.rows` | Ext8 `residuals`, `points` of 9 values |

The common result width of `CoefficientResiduals` is one plus the largest
output degree when every input has degree `width - 1`: 29 for width 8.
The arena's KoalaBear inputs are interpreted in Ext8 for `PointResiduals`.
At width 8, 112 values are either 8 row assignments or 14 polynomials; the
operation and the view that prepared them decide which, not the storage order.

## Maintained requests

The [fixture driver](../../../compiler/adapters/plonky3/driver/src/source.rs)
writes these requests beside the export, from the honest trace for `x0 = 2`
and `y0 = 5`, a trace with `x` on row 0 increased by one, and an instance with
`x0` increased by one.

| Request | View | Residuals |
|---|---|---|
| `source-rows-honest.json` | Honest trace, row-indicator selectors | All zero |
| `source-rows-changed-trace.json` | Changed trace; row 7 reads row 0 as its next row | Nonzero at rows and assertions (0,0), (0,1), (0,6), (7,8) |
| `source-rows-changed-public.json` | Changed instance | Nonzero at (0,1), (7,8) |
| `source-rows-two-adic.json` | Changed trace, two-adic Lagrange selector values | Different values, same nonzero cells |
| `source-coefficients-honest.json`, `source-coefficients-changed-trace.json` | Trace interpolants, next-row reads as `T(gX)`, Lagrange selector polynomials | Polynomials |
| `source-points-honest.json` | Four Ext8 points off the trace domain, trace openings at `z` and `gz`, closed-form Lagrange selectors | Ext8 values |

[`source-expected.json`](../../../compiler/adapters/plonky3/fixtures/recurrence/source-expected.json)
holds direct evaluations of the AIR's own `Air::eval` for every request, never
values computed from the arena. Coefficient cases list evaluations at the 8
trace-domain points and at as many further points as the result width.
Generation fails unless the adapter's arena interpreter agrees with `Air::eval`
and the nonzero row cells equal the failures the upstream debug checker reports. The adapter's
`regenerate.py check` rebuilds every request and expectation from the pinned
upstream AIR byte for byte. The arena, manifest and requests therefore stay
beside the export rather than in this directory. A change to the export changes
its arena identity; recompiling against the new `arena.json` changes the
compiled package without editing `main.zkc`.

## Run

From the repository root, where the manifest's relative paths resolve:

```sh
zkc compile --entry=imported_air::RowResiduals \
  --module=imported_air=examples/projects/imported-air/main.zkc \
  --asset=export=ring-json=compiler/adapters/plonky3/fixtures/recurrence/arena.json \
  --output=rows.entry
zkc run rows.entry EXPECTED_SHA256 \
  compiler/adapters/plonky3/fixtures/recurrence/source-rows-changed-trace.json \
  --evaluators=compiler/adapters/plonky3/fixtures/recurrence/ring-assets.json \
  --results=results.json
```

`results.json` uses `zkc.entry-outputs/0` with the role `Evaluator`; vectors
are framed KoalaBear or Ext8 values.

The [integration tests](../../../tests/protocol/test_imported_air.py) read the
committed fixtures without building the adapter. They run every request through
each Entry with default compilation, `--no-simplify` and `--release-storage`,
and decode the results independently. Row residuals must equal the direct
evaluations, with nonzero cells equal to the upstream failures. Each residual
polynomial must have the width computed from `arena.json` and agree with the
direct evaluations at at least that many distinct points, which determines it
exactly. Ext8 residuals must equal the direct values. Controls cover wrong
vector lengths, row counts and widths, the provider's width limit, a KoalaBear
frame for an Ext8 port, a missing manifest, another export's manifest, a stale
or edited arena under the bound identity, and the all-zero vector.

The coefficient provider accepts widths up to 65 and output degrees up to 64,
so this arena's polynomials fit heights up to 16. Lookups, permutation
arguments, quotient construction, commitments and FRI are outside this client.
