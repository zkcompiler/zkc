# Compiled relation authoring

The [relation ingress contract](../compiler/relation-ingress.md) is authoritative for R1CS
and AIR ingestion; this page states what authoring a compiled relation requires.

For declaration syntax, start with
[compiled relation declarations](reference.md#compiled-relation-declarations)
and the [maintained relation examples](../../examples/relations/README.md).

## Objective and boundaries

An author supplies a compiled relation and a protocol that consumes its
declared representation. Import resolves the relation's field, statement
layout and arithmetic representation. Protocol execution consumes compiled
algorithms and immutable prepared data; it does not interpret Circom or LLZK.

The principal end-to-end case is BN254 Groth16 for a Circom Poseidon Merkle
membership circuit, using the original R1CS, witness and snarkjs prepared key.
The complete prover algorithm must remain visible in PIR: polynomial
evaluation and interpolation, vector arithmetic, MSMs, blinding and verification
pairings. Optimized arithmetic belongs to the backend. A whole-prover foreign
call would not exercise the intended compiler architecture.

AIR remains a separate relation representation and a contrasting consumer.
Neither AIR nor rank-one constraints are the universal relation IR. Ordinary
protocols with no imported relation acquire no relation-specific obligation.

## Rules

1. **Relation ownership.** A resolved relation is immutable compilation input,
   with a typed family-specific representation. File paths are locators, not
   semantic identities. Resolved contents and public layout must survive the
   authoring boundary; shape equality cannot authorize substitution.
2. **Staging.** Both static specialization and immutable data are required.
   Large coefficient arrays and keys must not become thousands of source
   operations or consume the small protocol-source byte budget. Staging is a
   consumer choice, independent of the relation's mathematical meaning.
3. **Dependency loading.** Parsing and formatting remain free of filesystem
   effects. A separate, bounded loading/linking boundary resolves requested
   assets and libraries. It must not concatenate source strings, create
   declaration-order-sensitive names, or silently select a different field.
4. **Retained abstraction.** Relation declarations and the algorithms that
   consume them need explicit ownership before realization. MLIR symbols and
   symbol references are the natural declaration/use mechanism; SSA values
   carry local computational data. Typed generated functions are selected;
   the resolved snapshot and native MLIR retain their relation association.
5. **Prepared artifacts.** A verification key is sufficient for Groth16's
   verifier. It does not require the verifier to receive or interpret the
   entire constraint matrix. Key association includes exact field, ordered
   assignment/public layout and QAP convention. Merely matching dimensions,
   or attaching a hash label to an unrelated key, is insufficient.
6. **Noninteractive execution.** Groth16 already has a one-way proof flow.
   Endpoint projection and proof serialization must support that flow without
   manufacturing a verifier RNG or applying Fiat–Shamir. This is distinct
   from the existing challenge-to-transcript construction.
7. **Assurance.** Executable correspondence, relation translation, setup
   integrity and the cryptographic security theorem are separate obligations.
   Cross-verification and controlled-randomness equality test the implementation;
   they do not establish a Groth16 security theorem or ceremony trust.

## Alternatives considered

| Choice | Benefit | Cost or failure to avoid |
|---|---|---|
| Opaque runtime relation interpreter | One broad host API | Hides family algorithms and compiler opportunities; not selected |
| Frontend-generated function text | Quick experiments | Loses typed dependencies, source ownership and robust linking; replace |
| Typed generated algorithm interfaces | Reuses local-call machinery | Must retain and validate their relation association, not merely origin labels |
| Family-specific relation operations | Explicit high-level uses and lowering | Requires coordinated source, native IR and independent-reader contracts |
| Universal relation handle | Convenient nominal reference | Must not imply all relation families offer the same operational interface |
| External prepared-key adapter | Reuses ecosystem setup | Exact encoding and QAP correspondence are additional checked boundaries |

Typed generated functions reuse existing call, type, projection and analysis
machinery. Their signatures and arithmetic bodies are checked against immutable
relation data. Family-specific relation operations remain a future option when
a consumer needs structure that these views erase. A relation symbol alone is
not a proof of correct generation. A backend profile is not a relation identity.

## Selected compilation boundary

```text
readable PIR with relation locators
  -> bounded dependency resolution
  -> immutable typed relation snapshot + authored protocol
  -> relation symbols and associated ordinary functions in MLIR
  -> explicit relation-view materialization
  -> ordinary common protocol -> participant projection -> physical plan
  -> separately running producer and verifier
```

Parsing and formatting stop before dependency resolution. Resolved snapshots
include canonical relation data and requested view records under
`zkc.relations/1`; generated functions are reconstructed and verified, not
accepted merely because their names look generated. A relation captured as a
static association also appears inside type identities; every relation named
there must be one of the snapshot's own table entries, or the snapshot refuses
with `relation-snapshot-subject`, since the table alone rebuilds the view code.
The `rank_one` view exposes
the rank-one family, `multilinear` adds its Boolean-cube consumer, and `arithmetic`
exposes finite AIR residuals. Relation declarations are not runtime handles.

Explicit materialization verifies relation ownership before lowering to ordinary
source. Independent readers that do not support the snapshot envelope refuse
it. Subsequent Lean source/participant checks concern the materialized ordinary
source; they do not prove the preceding native relation-view generator correct.
Independent relation arithmetic and mutation tests address that separate boundary.

Matrix data carries canonical content checks in generated code. Prepared keys
travel through bounded format adapters into existing typed values. Key checks
distinguish decoded/header facts, recoverable A/B correspondence, and full
key derivation or ceremony assumptions. There is no catch-all "verified key"
flag. The noninteractive path checks the actual reachable endpoint graph,
requires one-way proof flow and a serializable verifier interface, and selects
an explicit Boolean acceptance output. This policy is not a security theorem.

## Interoperability experiment

The [maintained interoperability fixture](../../tests/groth16/README.md) uses
Circom 2.2.2, snarkjs 0.7.5 and pinned circomlib Poseidon circuits at depths 2
and 16. It retains one original R1CS and prepared key for both implementations. An LLZK-produced equivalent
relation is a separate adapter test: it cannot silently reuse the original
key if constraints or assignment coordinates change.

The reference producer's only deterministic-test change is explicit injection
of the same blinding scalars. The reference verifier remains unmodified.
Compare public signals, intermediate QAP values, proof coordinates, and a
specified canonical serialization. Ordinary fresh proofs need not have equal
bytes. Run cross-verification in both directions and corrupt public inputs,
proof points, witness layout and prepared-key associations deliberately.

The snarkjs prover stores A/B evaluation coefficients, appends public-input
rows, and uses a transformed H-query basis. Textbook coefficient-form quotient
MSM cannot be substituted without checking the exact basis conversion. This
is an implementation convention, not a change in the relation semantics.

## Primary references

- [MLIR symbols and symbol tables](https://mlir.llvm.org/docs/SymbolsAndSymbolTables/):
  declaration ownership, explicit symbol users, scoped lookup and mutation.
- [MLIR dialect conversion](https://mlir.llvm.org/docs/DialectConversion/):
  legality at lowering boundaries and explicit conversion responsibilities.
- [snarkjs 0.7.5 prover](https://github.com/iden3/snarkjs/blob/v0.7.5/src/groth16_prove.js)
  and [verifier](https://github.com/iden3/snarkjs/blob/v0.7.5/src/groth16_verify.js):
  exact interoperability target, not the compiler's normative semantics.
- [Circom circuit compilation](https://docs.circom.io/getting-started/compiling-circuits/):
  R1CS and witness generation as separate outputs.
- [Groth, EUROCRYPT 2016](https://eprint.iacr.org/2016/260): preprocessing
  pairing argument and QAP/security setting. Its security result is a theorem
  to connect under explicit assumptions, not a consequence of compiling the
  verifier equation or matching an implementation's proof bytes.
