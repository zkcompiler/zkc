# Imported AIR residuals

This client evaluates the [recurrence AIR](../../../compiler/adapters/plonky3/client/src/lib.rs)
from Plonky3 through ordinary `.zkc` source and the Entry Host. The
[adapter](../../../compiler/adapters/plonky3/README.md) exports both a deterministic
[relation Bundle](../../../docs/spec/domains/relation-bundles.md) and a
[ring arena](../../../docs/spec/domains/ring-expressions.md) for polynomial
substitution. No compiler or runtime code recognizes the recurrence protocol.

## Actual trace and prepared polynomial views

`TraceResiduals` accepts the actual trace, configuration column, public values,
and height. Its captured `Recurrence` Bundle determines the read offsets,
column authorities, assertion scopes and fixed height. The kernel derives
current and next-row reads internally and inserts zero in inactive assertion
slots. Callers cannot supply selector values or substitute a vector of
expanded reads for the trace.

`DisclosedTraceProof` sends the whole trace from P to V. V supplies the
configuration, height and public values and accepts when all table residuals
are zero. Its source target is a Bundle-backed relation whose formal ABI is
derived from the captured contents. This is a transparent reference protocol
that exercises the proof Host; it offers neither succinctness nor zero
knowledge. The source restricts the Bundle to one table and no channels, and
its exact relation ABI requires the fixture's required, fixed-height table.
The generic table kernel does not establish interaction or presence obligations.

The other Entries consume **prepared polynomial assignments**. They remain
useful for coefficients and extension-field evaluations, but do not establish
that the assignments came from any trace. In particular, an all-zero prepared
assignment gives zero residuals because it also zeros the selectors.

| Entry | Inputs | Evaluation | Results |
|---|---|---|---|
| `TraceResiduals` | 32 trace elements, 8 configuration elements, 3 public elements, height 8 | `relation.table_rows` | 72 row-major residuals and `satisfied` |
| `DisclosedTraceProof` | Trace at P; configuration, public scalars and height at V | Send trace, then `relation.table_rows` at V | Authored proof and acceptance |
| `RowResiduals` | KoalaBear `assignments`, 14 per row; `rows` | `ring.rows` | 9 residuals per row and `satisfied` |
| `CoefficientResiduals` | 14 polynomials, each with `width` ascending coefficients | `ring.coefficients` | 9 residual polynomials of a common width |
| `PointResiduals` | Ext8 `assignments`, 14 per point; `points` | `ring.rows` | 9 Ext8 residuals per point |

The ring's 14 inputs are four current-row and three next-row trace reads, the
configuration column, three public values, and three selectors. Its nine
outputs are the AIR assertions in emission order. The common coefficient
result width is one plus the largest output degree with each input weighted
`width - 1`: 29 for width 8. The coefficient provider admits input widths up
to 65 and output degrees up to 64. The prepared ring view permits substitution
of KoalaBear inputs into Ext8; the actual table view requires the declared
column fields exactly.

## Capture and authority

[`main.zkc`](main.zkc) declares `Export = ring(asset export)` and
`Recurrence = bundle(asset recurrence)`. Generic helpers take `Ring` or
`Bundle` terms as static parameters. The compiler checks their fields and
table index and retains their canonical contents in the Entry package.
The Host independently admits those contents and preflights every reachable
reference before execution. The package also retains the Bundle behind its
relation declaration, even when the selected Entry uses only the ring view.

The package's expected SHA-256 authorizes these definitions. Runtime inputs
supply values under their declared roles; they cannot install another arena,
change a read binding or choose another column's authority. The transparent
proof's V inputs determine the public statement and configuration.

## Run

From the repository root:

```sh
zkc compile --project=examples/projects/imported-air/zkc.toml \
  imported_air::TraceResiduals \
  --output=trace.zkpkg
zkc run --package=trace.zkpkg --sha256=EXPECTED_SHA256 --session=recurrence \
  --input=Evaluator=compiler/adapters/plonky3/fixtures/recurrence/source-trace-changed-trace.json \
  --results=results.json
```

Use the package digest returned by `compile`. `results.json` has format
`zkc.entry-outputs/0`; vectors contain decimal KoalaBear values or Ext8 coordinate arrays. The package
contains its assets, so subsequent execution does not depend on fixture paths.

## Maintained evidence

The [fixture driver](../../../compiler/adapters/plonky3/driver/src/source.rs)
generates honest, changed-trace and changed-public requests for both trace and
prepared row views. It also generates coefficient and Ext8 point requests.
[`source-expected.json`](../../../compiler/adapters/plonky3/fixtures/recurrence/source-expected.json)
contains direct `Air::eval` expectations. Coefficient cases compare at enough
distinct points to determine each bounded-degree polynomial. The adapter's
`regenerate.py check` reproduces these fixtures byte for byte from pinned
upstream sources.

The [integration tests](../../../tests/protocol/test_imported_air.py) exercise
the Entries with default compilation, `--no-simplify` and `--release-storage`.
Controls cover changed trace, public and configuration values; malformed
shapes and heights; missing, stale and edited packaged assets; prepared
assignments passed as traces; and valid and invalid disclosed-trace proofs.
Additional tables or channels refuse in the reference protocol's source
bounds. Native tests separately cover finite and cyclic windows, scopes,
column authorities, exact field compatibility and execution limits.

These are executable correspondence checks on maintained cases. They do not
prove adapter adequacy or native implementation correctness. The [STARK example](../air-stark/README.md) composes quotient construction,
commitments and FRI with the same imported relation.
