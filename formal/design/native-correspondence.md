# Rust and backend correspondence

**Target design.** This chapter implements the boundary choices of the
[realization reference](../../docs/guides/realization.md). Mathematical
backend contracts remain the interface; verification of a particular native
implementation is an independently strengthen-able assurance component.

## 1. What a backend theorem should say

Separate mathematical algebra, a logical operation model, the actual native
adapter and the protocol client. For example, a field law says multiplication
obeys the chosen field structure. An adapter theorem says that a Rust operation
on its actual limb representation produces a related result and permitted state
and error behavior. A protocol theorem then uses the field/operation contract.

```text
native operation on NativeState and NativeValue
       │ representation and operation correspondence
logical handler on LogicalState and FieldValue
       │ common module and compiler laws
interpreted PIR client and its property experiment
```

Switching from Arkworks to another backend that satisfies the same sufficiently
strong contract does not require redoing the generic compiler proof. It requires
instantiating the implementation boundary: a proved adapter, a reused proof for
that implementation/configuration, or a stated trust assumption. Changes to
representation, field, wire encoding, randomness, errors or observable behavior
may change the contract instance and therefore its applicable client theorems.

Neither ArkLib nor CompPoly is the native Arkworks implementation. Their Lean
mathematics can provide targets for algebraic correspondences and protocol
reasoning. Optional adapters can relate those definitions to zkc meanings; they
do not discharge a Rust implementation boundary by being imported.
[S37](sources.md#s37)

## 2. A compositional contract with actual representations

The maintained [simulation module](../Zkc/Realization/Simulation.lean) now supplies
`PIR.Execution.Relates`, with separate reply types and a value relation indexed
by both actual final states. Its `follow`, `trans` and `of_related` laws compose
continuations, representation boundaries and the existing equal-reply relation.
The [controls](../Tests/Simulation.lean) distinguish allocated/loaded results,
stale heaps, rollback, omitted observations and changed stops. These are checked
mathematical laws and small instances; an actual native adapter and its progress
theorem remain obligations below. The [Rust foundation](../../crates/zkc-runtime/README.md)
is a concrete implementation target, not yet an extracted correspondence proof.

The implementation package should provide the following, with names selected
when the first client is implemented:

| Contract component | Concrete content |
|---|---|
| Value relation | Limb/word/byte representation, field modulus, canonicality, sizes and index interpretation |
| State relation | Registry and input snapshots, ownership, live buffers, cache contents, resources, transcript/provider state and remaining input |
| Operation correspondence | Related arguments and states lead to related complete outcomes, states and observations |
| Progress obligation | Termination or the precisely allowed divergence/exhaustion behavior under the relevant preconditions |
| Codec laws | Successful parsing and rejected/partial input, consumed offsets, framing, canonical encodings and output relation |
| Foreign-call contract | ABI, aliasing, lifetime, mutation, panic/unwind and reentrancy assumptions actually used |
| Initialization law | Joint initial state/distribution, including persistent correlated resources and seeds |

Use explicit implementation records for semantic choices. Typeclass inference
is useful for algebraic laws; it should not accidentally choose an observer,
backend configuration or deployment trust policy. Keep conversion lemmas from
each generated Rust model to these records in the adapter package.

A deterministic implementation theorem can first quantify over an explicit
random tape or provider state. A separate theorem relates the actual initial
distribution to the required law. This is often easier than proving a native
OS entropy source random, while still exposing exactly what must be assumed.
For adaptive draws, the tape allocation and dependency/conditioning discipline
must match the protocol experiment. Equal individual marginals do not establish
the joint law. Couplings provide a compositional tool when randomized executions
are related; they are not an automatic license to resample correlated state.
[S30](sources.md#s30)

### 2.1. Default validation route

The [assurance policy](../../docs/assurance.md#6-implementation-correspondence-policy)
adopts differential testing for the native connection. Drive actual MLIR
import, transformation and export, then execute the resulting admitted plan in
Lean and Rust. Compare against source execution or an independent evaluator
where feasible: running both interpreters on the same wrongly exported plan
alone would miss a shared source-to-plan defect. An eventual generated-code
route needs its own execution comparison.

For each supported slice, define executable representations and the comparison
relation, connected by Lean laws to its mathematical meaning where a separate
reference evaluator is needed. Compare outcomes, failure states and selected
events, including cache/handle validity and provider consumption where present.
Generate programs, inputs and admissible initial states; retain explicit cases
for invalid inputs, aliasing, failed writes, exhaustion and phase errors.
Exercise direct and optimized routes. Record semantic-path coverage and native
instrumentation separately, the untested dimensions, and source/build identity.
Preserve replayable disagreements and reduce them to regression cases. A
deliberately changed observation must fail the comparator.

Investigate a mismatch across the source contract, Lean evaluator, exporter,
native runtime and harness; Lean execution is not an infallible oracle for human
intent or its own compiled I/O. Shared random tapes isolate deterministic
execution behavior. If a transformation changes draws or their joint law, first
establish the required coupling/property relation rather than forcing identical
seeds to stand for security preservation.

Native proofs below are selective extensions of this method; their absence does
not prevent delivering a tested native slice under its stated implementation
assumptions.

## 3. The first native slice

Choose a real zkc-owned wrapper that binds immutable inputs, prepares or looks
up a factor, invokes a module, updates state and returns through a recoverable
failure branch. The arithmetic primitive inside the call may initially remain
contracted/trusted. Test the wrapper that zkc actually adds, where a mistake
would invalidate otherwise correct backend mathematics.

Make the first runtime a coarse-grained plan interpreter when feasible. A plan
instruction should invoke a useful kernel, batch or module action; a mandatory
dispatch for every field multiplication would unnecessarily constrain performance.
The interpreter is an execution engine, not an independent Rust authority for
PIR semantics. Its actual behavior must be related to the Lean plan meaning.

This provides a stable baseline for generated execution. If interpretation is
too expensive, keep it as a correctness/reference route and add a generated
route with its own correspondence or explicit downstream compiler trust. Do not
claim that a proof about the interpreter verifies generated code that bypasses
it. Backend kernel acceleration can be shared by both routes.

Validate the actual capture order, state/error handling, bounds and cache
invalidation of the wrapper through the differential route. Then add one
field-materialization operation to exercise machine arithmetic and representation
invariants. Choose a second backend only after the first implementation is factored
through a reusable contract; the second should measure reuse, not duplicate an
entire protocol proof.

## 4. Rust-to-Lean extraction as an optional proof route

Aeneas is the first candidate for an owned safe Rust core; hax is the deliberate
comparison candidate. Both produce proof-assistant representations, but their
supported fragments and extraction mechanisms differ. Tool choice is decided by
the actual wrapper rather than an assumption that every Rust crate translates.
[S17–S19](sources.md#s17)

If a native proof is pursued, its required chain is:

```text
actual Cargo source + lockfile + features + cfg + target
  → pinned extraction input and generated Lean definitions
  → theorem about those generated definitions
  → common zkc realization contract
  → existing source/compiler/property theorem
```

The correspondence theorem has roughly this shape:

```text
representation arguments state
∧ reachedCallPreconditions arguments state
∧ declaredExternalModelsHold
⇒ generatedRustFunction arguments state
     implements logicalOperation arguments state
```

The generated function is the theorem subject. The extraction tool and its
input semantics remain in the trust story unless their connection is separately
verified. Rustc/LLVM, native linking and execution also remain downstream
boundaries. Handwritten external models need their own assumptions or proofs;
a generated template with a desirable definition is not native verification.

A 2026 Rust-to-Lean experience report is especially relevant: it describes
cryptographic targets, Lean mathematical specifications and substantial
toolchain/extraction friction. Some targets use rewritten monomorphic models.
Its lesson for zkc is a viable proof workflow and a concrete correspondence risk:
if a production function is rewritten for extraction, equality to the production
function needs separate evidence. We do not treat that report as a verified
zkc integration or a blanket guarantee about current extractors.
[S20](sources.md#s20)

If extraction cannot handle the actual implementation, there are three honest
outcomes: simplify the implementation and execute that simplified implementation;
prove a relation to an extraction-friendly model; or retain an explicit trusted
boundary. Quietly proving a nearby model is not a fourth implementation proof.

## 5. Package design and maintenance

Retain the main-package architecture in [DESIGN](../DESIGN.md). Create a separate
optional package only when an external proof tool introduces its own dependency
and toolchain requirements. Suggested initial organization:

```text
formal/                         canonical mathematical library
formal/integrations/arklib/      optional external mathematical correspondences
formal/integrations/aeneas/      optional generated models and native proofs
```

The ArkLib integration is implemented as a separately resolved package; the
Aeneas path remains an implementation target. A hax prototype
may live in its own isolated experimental package; do not add both extraction
ecosystems to the default build before choosing a supported route. Module prefixes
such as `ZkcAeneas` identify an adapter ecosystem, while contract declarations
remain in `Zkc.Realization`. External result/heap/scalar types do not appear in
the main library's public APIs. A main import never depends on optional packages.

Generated definitions and handwritten correspondence proofs must be separate.
Regenerate from pinned actual inputs; never hand-edit the generated function to
make its theorem easier. Whether generated output is checked in or reproduced
as a build product can follow repository policy, but every claimed proof build
must identify and regenerate the exact input/output relation. Recording a hash
alone does not prove the generator correct.

Select mutually compatible exact versions of Lean, Mathlib, extraction backend,
Charon/rustc or hax/rustc, crate dependencies and target configuration. Compatibility
is an empirical result of an actual build, not an inferred property of separately
working tools. Isolate toolchain upgrades from semantic changes. If two packages
cannot coexist, either find a common supported revision or introduce and verify
a data boundary; copying theorem names across incompatible environments is not
proof composition.

For an extracted proof package, use three additional maintenance checks: a clean
regeneration/proof build, an audit of theorem assumptions and external models,
and artifact/build-input matching. Continue differential tests and relevant
sanitizer checks across actual execution, including parser, foreign-call and
build boundaries that the theorem may not cover.

## 6. Unsafe code, cryptographic assumptions and side channels

Rust ownership can establish useful aliasing and lifetime invariants. It does not
establish protocol freshness, independence, transcript validity or authorized
disclosure. A runtime capability can prevent copying a token while still issuing
that token for the wrong semantic resource.

When a needed implementation uses unsafe pointers, interior mutability,
concurrency or reentrancy beyond the selected extraction fragment, consider
Verus, Creusot, SAW or separation-logic-based Rust verification for that specific
boundary. Their results require an explicit logical/semantic bridge to the zkc
contract. Merely proving two tools' versions of a similarly named specification
does not prove those specifications equivalent.
[S21–S23](sources.md#s21), [S28–S29](sources.md#s28)

For arithmetic and primitives, existing verified implementations or generators
such as Fiat-Crypto, HACL* and Jasmin may reduce proof work. Reuse only their
actual proven scope and supported targets. Correct implementation of a hash
function does not prove the random-oracle model; constant-time claims depend on
the specific leakage/architecture model. A field operation's functional equality
does not by itself preserve native cache, timing or allocation observations.
[S25–S27](sources.md#s25)

The default finite PIR observer should remain unchanged by a performance backend.
If a claim includes stronger leakage observations, add a relation for those
observations and a compositional theorem. Native concurrency requires a separate
semantic extension where the actual implementation can expose interleavings;
an atomic function signature alone cannot hide them.

## 7. Backend independence has a precise limit

Consider a contract saying only “returns an element of the field.” A backend
returning zero and one returning one both satisfy it. They are not interchangeable
for a caller that branches on the result. Shared membership in a weak unary
contract is not pairwise observational equivalence.

The remedy is to choose the contract for the promised client result. Deterministic
algebra may use a functional specification. Stateful or randomized modules may
need a relational specification or a common sufficiently determinate abstract
model with proven composition. This is where backend independence comes from:
the exact contract and transport theorem, not the number of implementations
that expose the same Rust trait.
