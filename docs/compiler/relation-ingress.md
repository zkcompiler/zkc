# Relation ingestion and protocol consumers

zkc consumes a relation as domain data and compiles the protocol that proves it.
The relation frontend and proof protocol remain separate. This lets the same
rank-one protocol consume different circuits while arithmetic-trace and group
protocols retain the structure their own consumers need.

The selected [constraint meanings](../spec/domains/constraints.md) and
[encoding adequacy](../spec/properties/relations.md#source-encoding-adequacy) own
the semantic contracts.
The [compiled-relation authoring design](../language/relations.md) adds explicit
source declarations, immutable snapshots and checked generated views.

## Boundaries

```text
Circom / Halo2 frontend                 Other relation producers
             │                                     │
             ▼                                     │
       pinned LLZK process                         │
             │ parsed subset + interface checks     │
             ▼                                     ▼
       ordinary R1CS artifact ──────────► zkc relation model
                                             │
                                    relation.r1cs symbol
                                             │
                              inspect / normalize / specialize
                                   ┌─────────┴─────────┐
                                   ▼                   ▼
                         fixed local programs    public matrix data
                                   └─────────┬─────────┘
                                             ▼
                            authored PIR proof protocol
                                             │
                         construction / role extraction / plan
                                             │
                                  Rust library backends
```

The external adapter uses its own compatible LLVM/LLZK toolchain. It is not
linked into the main MLIR process when their LLVM versions differ. The examined
LLZK revision needs local corrections before it accepts the programs used here;
the corrections are maintained with the adapter, and each wider accepted subset
needs its own checks. The ordinary
R1CS reader validates the target format and exact field; it cannot determine
whether a source constraint disappeared upstream. Therefore source-operation
and interface checks occur before potentially erasing lowering. Successful
witness computation or successful R1CS export is not an adequacy test.

`relation.r1cs` is a structured symbol definition. Its field, ordered public
layout, dimensions and sparse row triples are inspectable. It has no hidden
witness generator, prover, verifier or transcript. The pass
`--zkc-deduplicate-relations` removes only exact normalized duplicate row triples.
Its mathematical basis is row coverage; native correctness is tested separately.
It changes the normalized subject identity and may change protocol dimensions,
so dependent code and artifacts must be rebuilt.

An AIR view instead retains expression reads, degree and first/last/transition
scope. Its selective evaluation plan consumes those facts directly. It is not
advertised as a STARK prover or forced through the rank-one representation.
`relation.air` preserves this structure as an MLIR symbol. The native API
derives read support and trace-expression degree; selector/domain degree remains
a separate obligation for future quotient consumers.

## Local computation and staging

The general `rank_one` view exposes assignment assembly, matrix products and
constraint residuals. The separately selected `multilinear` consumer adds
challenge-weighted row contraction and verifier point evaluation.
Assignment and public-binding helpers preserve the layout
`[ONE, public outputs, public inputs, private/auxiliary coordinates]`.
The proof protocol still owns commitments, sumcheck rounds, challenge order,
public-coordinate openings and final checks.

Two staging choices share this interface:

| Choice | Coefficients | Appropriate use |
|---|---|---|
| Specialized | Fixed in generated vector operations | Small fixed relations and compile-time inspection/specialization |
| Public matrices | Immutable `matrix:F` inputs; generated views fix dimensions/layout and canonical content digests | Larger relations without coefficient-sized code |

Resolved relation views check canonical matrix content identities before use;
same shape is insufficient. The SHA-256 identity covers the nominal field,
dimensions and normalized coefficients, rather than the input filename or
original binary spelling. This is content binding under a collision-resistance
assumption, not a theorem that an external compiler preserved its source circuit.

Visibility and protocol binding belong to the consumer. The multilinear proof
uses verifier-owned matrices and binds them with the statement in its public
root/transcript. Groth16 instead uses a public verification key; its verifier
does not need raw matrices or a witness. Prover-local relation checks do not
replace the assumption that this verification key was derived for the intended
relation. Proving keys are public parameters even when only the prover loads
them; the witness and blinding coins are private.

The logical matrix type has no backend name. Its first physical representations
use canonical sparse COO storage, backed by immutable shared allocations. Matrix
products, transpose products and bilinear evaluation use the same mathematical
contracts across the installed scalar fields. Physical sparse representation is
not a requirement that every future kernel use sparse storage. Structured
formula evaluators, dense kernels and accelerators require their own lawful
implementation and cost evidence.

An ordinary unstructured matrix evaluation costs linear work in its nonzeros.
The multilinear imported-relation verifier pays that cost. This path does not install
Spartan's sparse-matrix commitment machinery or claim a succinct verifier for
arbitrary large circuits. Fixed structured formulas can have a different cost.

## Developer commands

The main compiler accepts binary R1CS v1 or the versioned canonical relation
transport. It rejects unknown/custom-gate binary sections and unsupported exact
field moduli. It does not reinterpret a BN254 circuit as BLS12-381 merely because
both have roughly 256-bit field elements.

```sh
zkc-compile relation-read circuit.r1cs > circuit.relation.json
zkc-compile relation-inspect circuit.r1cs
zkc-compile relation-import circuit.r1cs Circuit > circuit.mlir
zkc-opt --zkc-deduplicate-relations circuit.mlir > unique.mlir
zkc-compile relation-lower unique.mlir > fixed-locals.pir
zkc-compile relation-lower-data unique.mlir > matrix-locals.pir
zkc-compile relation-matrices circuit.r1cs > matrices.json
zkc-compile relation-evaluate circuit.r1cs statement.json assignment.json
```

The separate AIR commands use a bounded arena of arithmetic expressions:

```sh
zkc-compile relation-air-import trace.air.json Trace > trace.mlir
zkc-compile relation-air-export trace.mlir
zkc-compile relation-air-inspect trace.air.json
zkc-compile relation-air-plan trace.air.json 4
zkc-compile relation-air-polynomial trace.air.json 4 4 3
zkc-compile relation-air-evaluate trace.air.json trace.json statement.json
```

Unknown lookup/phase behavior is not accepted as ordinary arithmetic.

`relation-air-polynomial` takes the original height, interpolation domain size
and trace-polynomial degree bound. It derives original active rows, complement
selector degrees, individual quotient bounds, coefficient-chunk count and a
shared read footprint without expanding the trace. A null quotient degree means
an exactly divisible numerator must be zero; an inactive constraint has no
obligation. This is a conditional degree analysis, not satisfaction checking,
domain construction or a proof protocol. Distinct points, interpolation and
shift adequacy must be supplied by its consumer. The analysis currently bounds
dimensions by `2^24`; the separate dense evaluator retains its smaller resource
limits. Refusals distinguish malformed parameters (`air-polynomial-parameter`),
height, domain size, trace degree and illegal finite windows.

Use the same optimized relation when generating code and matrix payloads; the
commands above illustrate alternatives, not interchangeable files. To produce
matrix payloads after optimization, first `relation-export unique.mlir` and pass
that result to `relation-matrices`.

Canonical transport uses strings for naturals and coefficients:

```text
["zkc.relation.r1cs/1", field, columns, publicOutputs, publicInputs, rows]
row = [A_terms, B_terms, C_terms]
term = [column, coefficient]
```

Columns in each canonical form are strictly increasing; coefficients are
nonzero canonical field values. The binary reader can normalize repeated/zero
terms into this form; the canonical JSON reader rejects them. Source labels and
provenance are recorded separately. Normalization does not reorder public slots
or pretend to decide arbitrary algebraic equivalence.

Native limits are explicit: 64 MiB relation input, 65,536 rows/columns and
1,048,576 total sparse terms. Generated source retains the existing 1 MiB limit.
Fixed specialization also respects the native 16,384-attribute ceiling: a
matrix with 16,384 or more entries refuses fixed specialization; explicitly
select public-matrix staging instead. The
logical relation reader and mathematical Lean model do not share this execution
ceiling; admission in one layer does not waive another layer's resource policy.
The first proof library authenticates public coordinates individually and caps
that selected consumer at 128 public values. These are implementation limits,
not restrictions on the abstract family. Increasing a dimension does not waive
artifact, PCS, output-memory or reference-execution limits.

## Assurance and extensions

Four questions have separate answers:

1. Does the imported representation mean the intended source relation, in both
   witness directions and with the correct statement map?
2. Does the mathematical proof protocol establish that relation under its stated
   assumptions and adversary model?
3. Does compiler lowering preserve the selected protocol execution?
4. Do native operations/codecs implement their mathematical contracts?

The Lean relation library proves algebraic and layout laws and supplies an
independent executable reference. Native differential tests, malformed-input
controls, protocol-source replay and selected equation comparisons address
specific parts of the other boundaries. They do not establish all four at once.
The current imported proof uses non-hiding commitment behavior and development
setup; it is not a production zero-knowledge circuit prover.

A new relation frontend should provide a pinned source interpretation, exact
field and public layout, explicit unsupported-feature handling, and adequacy
evidence at its claimed scope. It should reuse a supported domain view when
that view preserves the information its consumer needs. Otherwise define a new
view and consumer rather than silently flattening away lookups, phases or row
structure. A new backend implements operation/representation contracts; it does
not acquire authority to choose the application's relation.
