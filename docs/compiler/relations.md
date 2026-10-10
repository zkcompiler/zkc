# Relations

Relations describe statement/witness conditions; protocols compute and exchange
the values used to establish them. Importing relation data does not insert a
prover, witness generator or terminal check. [Constraint semantics](../spec/domains/constraints.md)
and [relation contracts](../spec/relations.md) own those distinctions.

## Import and identity

R1CS and AIR enter as immutable domain data with exact fields, dimensions, public
layout and arithmetic structure. R1CS retains sparse rows; AIR retains trace
expressions, read support and row scopes. Canonical contents identify data;
equal shapes and file paths do not.

After the [native build](../development/README.md), put `build/compiler` on
`PATH` and supply the named inputs:

```sh
zkc-compile relation-read circuit.r1cs > circuit.json
zkc-compile relation-inspect circuit.json
zkc-compile relation-import circuit.json > circuit.mlir
zkc-compile relation-export circuit.mlir > roundtrip.json
zkc-compile relation-matrices circuit.json > matrices.json
zkc-compile relation-evaluate circuit.json statement.json assignment.json
```

The binary reader supports a bounded R1CS v1 container and admitted exact field
moduli; it never reinterprets BN254 constants as BLS Fr. `.zkc`
[Assets](../language/relations.md) capture explicit relation formats.
The optional [LLZK adapter](../../compiler/adapters/llzk/README.md) owns its separate
source subset and compatible toolchain. The optional
[Plonky3 AIR adapter](../../compiler/adapters/plonky3/README.md) captures AIRs on a
pinned Plonky3 release into shared ring-expression views with a feature inventory
and refuses features it does not represent. The
[accumulator-machine adapter](../../compiler/adapters/accumulator-machine/README.md)
exports executions of a small external machine as a multi-table Bundle and emits
staged interaction reductions from its channel descriptors. Successful import cannot detect a
constraint already lost by an external frontend.

## Relation bundles

`zkc/Relation/Bundle.h` in `Zkc::Relation` admits the
[relation bundle](../spec/domains/relation-bundles.md) carriers. `readBundleText`
forms a `Bundle`; `readBundleConfiguration`, `readBundleInstance` and
`readBundleWitness` decode the supplied data against it. `Bundle::admit` checks
authority, presence, heights, every read window and the work bounds before any
value is parsed; `Bundle::evaluate` adds the reference interpretation and
reports residuals, balance sums and multiplicity range failures. `embedAIR`
and `embedAIRData` map a finite AIR and trace into a one-table bundle.
`StagedProgram` forms and evaluates a challenge-indexed staged program for
supplied challenges and claims. The Rust `zkc_runtime::relation` module admits
the same carriers independently and evaluates them through a supplied field
algebra.

A source declaration `relation R(...) = bundle(asset name);` binds a captured
bundle. `zkc/Language/RelationABI.h` derives the formal list such a declaration
must spell from the admitted bundle alone; the source checker compares the
declaration against it, and the interface reader repeats the derivation
against the retained interface record and native declaration. The derivation
is a pure function of the bundle; it carries no evaluator.

## Declaration and binding

`relation.declare` is a non-callable identity with one function type and an
ordered purpose list. Purposes apply to whole ports. Complete logical types
retain domains, extents, nominal identity and payload order across MLIR contexts.
The consistency API can compare explicitly supplied units; it is not a linker.

```text
relation R(configuration parameter, public statement, assignment witness) -> bool

protocol Check(configuration at V, public at V, assignment at P):
    bind R(configuration at V, public at V, assignment at P) to result[1]
    received = send P -> V(assignment)
    accepted at V = validate(configuration, public, received)
    return(false at V, accepted at V)
```

This client discloses its witness. The declaration identifies the intended
condition; `validate` explicitly computes it. A relation label neither proves
satisfaction nor authorizes setup material.

The [IR contract](../spec/ir/protocols.md#statements-and-retention) retains
actual entry coordinates, role selectors, purpose order and acceptance result.
Projection and lowering preserve those maps. Source-relative checking detects
same-typed substitutions that internal metadata consistency cannot.

Proof admission requires the selected relation decision to match the validator's
acceptance result. Configuration/statement ports must be validator-bound; witness
ports must be unavailable as validator entry inputs, including shared ports.
The Host binds actual canonical inputs. Its deployment pin authenticates bytes,
including the recorded source digest, without independently interpreting the
original relation declaration.

## Static reduction and terminal composition

`protocol.apply` has explicit roles and an interaction interface. Pure
`func.call` remains restricted to total mathematics. Static expansion connects
actual residual outputs to terminal inputs through ordinary SSA, retaining role
substitution, service state and failure propagation. Separately deployed or
dynamically selected components would need another handoff contract.

The bounded R1CS adapter exposes ordinary mathematical definitions:

```sh
zkc-compile relation-protocol circuit.json > circuit.mlir
zkc-compile relation-requirements circuit.json > requirements.json
zkc-compile protocol-checked-bundle circuit.mlir \
  --requirements=requirements.json --entry=main > checked.json
```

C++ callers use `authorR1CSSumcheck` and `r1csSumcheckRequirements` from
`zkc/Translation/Relations.h` in `Zkc::Translation`. Requirements come from the
independently supplied relation. The adapter specializes matrices into bounded
field operations and arrays; its [limits](../spec/ir/limits.md) are narrower
than the general bulk matrix kernels.

The weighted residual follows [Spartan's R1CS reduction](https://eprint.iacr.org/2019/550.pdf).
Weights prevent unweighted cancellation from being mistaken for satisfaction.
Formal products of MLEs remain distinct from the MLE of table products. The
assignment binds ONE, the public prefix and witness; the reference terminal can
evaluate the disclosed relation data directly.

## Checked reduction

The [mathematics contract](../spec/ir/mathematics.md) defines a bounded
structural recognizer on admitted participant form before polynomial folding.
It checks the actual subject and recipe; each received round polynomial;
`q_i(0) + q_i(1)` against the current scalar; the subsequent challenge;
`q_i(r_i)` and the ordered residual point; and the actual terminal decision.
Every independently supplied requirement is checked. Omitted requirements
cannot be discovered from that document.

For the true polynomial `h_i`, the exceptional event is a passed guard with
`q_i != h_i` but `q_i(r_i) = h_i(r_i)`. The reduction relates actual residuals
up to that event. A quantitative bound additionally needs the degree and
challenge experiment; query order alone proves no uniform sampling law.

The recognizer is an optional analysis, not a special execution instruction.
Equivalent unsupported rewrites can refuse. [Adjacent checks](verification.md)
separately compare lowering and publication. [Native tests](../../common/tests/native.md)
cover R1CS/AIR inputs, actual terminal decisions and same-shaped substitutions.
They do not establish succinctness, zero knowledge or an upstream encoding proof.
