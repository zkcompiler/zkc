# Relation ingestion

R1CS and AIR enter as immutable domain data. The compiler validates their exact
field, dimensions, public layout and arithmetic structure independently of the
protocol that uses them. [Constraint semantics](../spec/domains/constraints.md)
and [encoding adequacy](../spec/properties/relations.md#source-encoding-adequacy)
own the mathematical obligations.

## Supported boundaries

| Input or adapter | Result |
|---|---|
| Canonical R1CS JSON or supported binary R1CS v1 | Normalized sparse constraints and ordered assignment/public layout |
| Canonical AIR JSON | Trace expressions, read support and first/last/transition scopes |
| `.zkc` explicit Assets | Bounded immutable capture available to source relation declarations |
| Relation MLIR import/export | Structured `relation.r1cs` or `relation.air` data |
| Native R1CS/Sumcheck adapter | Bounded mathematical MLIR with explicit reduction and terminal computation |
| Optional LLZK integration | External generic relation translation in its separate compatible toolchain |

The native [composition adapter](relation-composition.md) is a bounded consumer
of relation data.

`relation.r1cs` has no hidden witness generator, prover, verifier or transcript.
Its field, sparse rows and public layout are inspectable. Exact duplicate-row
normalization determines the identity and dimensions used by dependent artifacts.
AIR retains its own expression and row-scope structure instead of being
silently flattened to rank-one constraints.

## Commands

After the [native build](../development/README.md), run from the repository root
with `build/compiler` on `PATH` and supply the named input files:

```sh
zkc-compile relation-read circuit.r1cs > circuit.json
zkc-compile relation-inspect circuit.json
zkc-compile relation-import circuit.json > circuit.mlir
zkc-compile relation-export circuit.mlir > roundtrip.json
zkc-compile relation-matrices circuit.json > matrices.json
zkc-compile relation-evaluate circuit.json statement.json assignment.json
```

The binary reader rejects unsupported sections and exact field moduli. It never
reinterprets a BN254 relation as BLS Fr. `.zkc` captures use the explicit formats
in [Relation Assets](../language/relations.md). See installed command help for
AIR data inspection/evaluation and the
[native reduction guide](relation-composition.md) for its narrower field/size limits.

## Adapter and authority obligations

The external frontend must preserve the intended source relation before any
lowering erases unsupported operations. Target-format validity cannot detect a
constraint dropped upstream. Witness generation or successful import is not a
proof of source encoding adequacy.

Canonical contents identify relation data; file paths and equal shapes do not.
Protocol declarations, public inputs, setup material and actual terminal checks
must retain their intended association. A relation clause or key label supplies
no satisfaction or setup-integrity theorem. LLZK's source subset and toolchain
are owned by its [adapter](../../compiler/adapters/llzk/README.md).
