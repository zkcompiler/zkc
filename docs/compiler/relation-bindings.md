# Structured relation bindings

The [mathematical profile](../spec/profiles/compiler/mathematical-protocols.md#statements-and-retention)
owns relation meaning; the [proof profile](../spec/profiles/compiler/native-proofs.md)
owns independent deployment admission. Immutable configuration, public statement
and witness values now use the existing logical types throughout these boundaries.

## Representation and binding

`relation.declare` remains a non-callable external identity, one MLIR function
type and an ordered purpose list. Types include matrices, vectors, static field
arrays, sequences and nominal records/sums over admitted data leaves. Its input
purposes apply to whole ports. Canonical logical encodings make equality exact
across MLIR contexts, including domains, static extents and nominal payload order.
Current compiler commands check declarations within one unit. The public C++
consistency API also compares explicitly supplied units across MLIR contexts;
this is API coverage, not a new multi-unit linker. No additional dialect, stage, runtime
instruction or relation-specific executor is added.

```text
relation R(configuration: sequence<matrix<F>> parameter,
           public: vector<F> statement,
           assignment: vector<F> witness) -> bool

protocol Check(configuration at V, public at V, assignment at P):
    bind R(configuration at V, public at V, assignment at P) to result[1]
    received = send P -> V(assignment)
    accepted at V = validate(configuration, public, received)
    return(false at V, accepted at V)
```

The declaration records the interface; `validate` explicitly checks its
predicate. The example deliberately sends its witness and is not zero knowledge.

The binding chain uses existing mechanisms:

1. A statement operand is an actual entry argument with an explicit role selector.
2. Projection retains the original signature, purpose order, selected port indices
   and acceptance result, plus actual participant port/result maps.
3. Lowering and physical selection preserve that record. Source-relative checking
   compares the candidate to the original module; internal consistency alone
   cannot detect swapping same-typed operands.
4. Proof admission requires the declared acceptance to match the selected validator
   result, configuration/statement ports to be validator-bound, and witness ports
   to be unavailable as validator entry inputs, including shared ports.
5. The host checks actual role inputs against their public bindings and decodes
   canonical frames. The deployment pin authenticates deployment bytes, including
   the producer-recorded source digest and selected policy. It does not establish
   derivation from that source. The runtime does not independently re-interpret
   declarations.

Keeping one declaration schema avoids duplicating type, projection and runtime
metadata. A separate relation-port model would become useful only if a required
consumer needs an interface the current typed entry ports cannot represent. Data
permission is deliberately separate from copyability, total mathematics and wire
permission. In particular, copyable verifier keys are not ordinary relation data.

## Executed clients

| Client | Inputs and actual computation |
|---|---|
| [R1CS](../../compiler/test/fixtures/mathematical/relation-r1cs.mlir) | Three sparse matrices supplied as a sequence, a public vector and a full assignment. Check matrix count and dimensions, the ONE coordinate, public-prefix equality and every row of `(Az) * (Bz) = Cz`. The sequence makes its three-element arity an explicit checked value property. |
| [AIR](../../compiler/test/fixtures/mathematical/relation-air.mlir) | A nominal coefficient record, four public boundary coordinates and a sequence of trace rows. Check nonempty trace, two columns per row, first/last coordinates and `x' = y`, `y' = alpha*x + beta*y`. |

Both clients use the general local operations, structured control, proof host and
interpreter. Malformed dimensions stop explicitly with `reject` before indexing
or matrix multiplication. False constraints return false at the actual acceptance
port. No compiler or runtime branch dispatches on relation kind or key.

[Compiler controls](../../compiler/test/native_relation_bindings.py) cover normal,
unsimplified and storage-release lowering, reordered entry arguments, renamed
roles/identities, shared configuration and transcript derivation. A constant-true
decoy result, producer-only public relation input, verifier-visible witness,
swapped source bindings and changed actual terminal operands are refused.
The existing public-coin view accepts structured ports in its total-verifier
profile; authored validator local calls retain `public-coin-verifier-local`.
This analysis limit does not prevent proof construction or execution.

The [runtime client](../../crates/zkc-tools/examples/native_relation_bindings.rs)
checks 0, 1, 3, 17 and 128 constraint rows and 1, 2, 3, 17 and 128 trace rows.
R1CS assignments vary between 3 and 17 columns. Direct reference evaluators use
actual host values, scalar sums and adjacent-row checks independently of kernel
dispatch. Mutations cover configuration, public values, witnesses, empty or
malformed shapes, shared-input mismatch, truncated and trailing proofs.
[Cross-build tests](../../tests/protocol/test_native_mathematical.py) run separate
producer and validator CLI processes. The source-route Lean
`interactive-protocol --check-generic` checker explicitly refuses both the native
deployment and its embedded program.

## Limits and next work

- These two clients use BLS12-381 Fr and `zkc.native-proof-policy/4`. The
  [composition clients](mathematical-composition.md) execute BN254 matrix inputs
  and KoalaBear trace inputs under the same relation-binding contract. Each
  complete type still requires an installed codec.
- Dynamic matrices use the existing sparse COO limits: 65536 rows/columns and
  an absolute 1048576-nonzero ceiling. Native capacity defaults to 65536 numeric
  elements across a complete nested frame, including all matrices together. Deployment and invocation JSON inputs are limited
  to 16 MiB; hexadecimal frame text and public-value copies consume that budget.
  The tested ranges above are bounded evidence, not capacity guarantees up to
  the frame limits. Existing cumulative value/work budgets still apply.
- Configuration is supplied and bound by the application. The relation key names
  its contract; it is not an inferred digest of the matrices. Renaming identity
  changes source/deployment binding without changing executable mathematics.
- These are direct relation-checking clients. They establish neither succinctness,
  zero knowledge nor security of a SNARK/STARK. The derived challenge exercises
  transcript construction; the direct predicates do not use it for compression.
- Native Lean semantics, frontend ingress, mixed purposes within one aggregate,
  and relation-schema introspection at the runtime boundary remain later work.
  Broader domain/service and multiple authorized setup support are implemented
  at the scope of the [structured proof contract](../spec/profiles/compiler/structured-proof-messages.md).
  The [roadmap](../roadmap.md) owns the remaining consumer migration.
