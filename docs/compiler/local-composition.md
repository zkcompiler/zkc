# Local algorithm composition

Local functions can call closed helpers, generic definitions and partial or closed
configurations. Generic libraries compose under checked public requirements. The
native compiler retains typed callable structure, expands it on actual MLIR SSA,
then projects and lowers to the existing executable subset. The selected
[observation/accounting profile](../spec/profiles/compiler/local-algorithms.md)
is `canonical-expanded-locals/1`.

```text
module {
  fn Twice<F: Field>(x: F::Element) -> F::Element {
    [sum] let y = field::add(x, x);
    return y;
  }
  configure Selected = Twice();
  fn Four<F: PrimeField>(x: F::Element) -> F::Element {
    [first] let a = Selected(x);
    [second] let b = Twice::<F>(a);
    return b;
  }
  configure Bls = Four(F = "bls12-381.fr");
  configure Koala = Four(F = "koala-bear");
}
```

This declaration-only library admits with `protocol-source`; the
[notation guide](../language/reference.md#module-and-local-algorithms) supplies a runnable
protocol around `Twice` and `Four`. The portable local instruction remains
`["apply", site, callee, static_arguments, inputs, outputs]`, distinct from a
role-owned protocol `local` action and a dependency `call`. `apply` is a common
record tag, not authoring syntax.

## Generic application and formation

`F: Field` emits the public capability `Field(F)`; `F: domain Field` supplies only
the sort. The example's `PrimeField(F)` entails `Twice`'s `Field(F)`. Static
arguments can be inferred from operands or a local result annotation, but not by
inverting associated members or searching installed domains. The frontend does
not infer stronger public promises from bodies.

Applications use the operation syntax for ordered static arguments, without
operation attributes. The arguments of a configuration fill its still-unbound
parameters in the base definition's declaration order. A fixed assignment cannot
be supplied again. Generic bodies supply parameter terms or associated-member
projections; closed bodies supply installed nominal identities. An ordinary
closed helper takes no static arguments. Generic bodies target generic definitions
or configurations. Zero-parameter generic definitions provide helpers with
domain-independent public ports; domain-specific fixed helpers use configurations. Calling an ordinary `Function` from a generic body
is outside this fragment.

Formation substitutes the callee's public input/result types and requirements.
The caller must entail every residual requirement and every nominal equality
needed at its operand/result boundary. For example, `PrimeField(F)` entails the
callee's `Field(F)` through the existing installed implication; the converse is
refused. A selected configuration does not provide a new assumption. Its fixed
roots are nominal constants, excluded from residual parameter arity. Fully ground
obligations are checked against installed domain facts; symbolic obligations
still require the caller's public promise. Constants cannot equate an arbitrary
caller parameter to a selected field. Affine arguments are consumed at each
application, including when the callee merely returns them.

All declarations and configurations are checked before demand selection,
including unused bodies, forward references, cycles through configurations and
shared suffix depth. Body obligations are collected from every primitive and helper
application and checked against the declared public requirements. Implementation choices attach only to primitive sites; choose a
helper configuration to select its implementation, rather than attaching a
primitive implementation to an `apply` site.

Demand starts at protocol-local configurations and every ordinary local body,
then closes transitively over concrete helper applications. It specializes types,
static arguments, field literals and operation bindings, emits shared closed
functions with original definition/static-binding origins, and retains typed
`AlgorithmCall`s. Both the native compiler and independent Lean preparation bound
demand visits and newly emitted instructions at 32768, in addition to existing
4096-definition/binding and module byte limits. The native path imports these
calls as actual `func.call`s; the existing SSA expansion pass then applies.

The six-field `apply` record is the admitted form for codecs, identity consumers
and tests. Other arities fail closed. Static
arguments must be empty after specialization. There is no compatibility decoder
or additional runtime interpreter.

## Design choice

Early frontend macro expansion would reuse today's flat executable bodies, but
would erase callable boundaries before native analysis and transformation.
Retaining calls all the way into the runtime would preserve a distinct frame
model, requiring new runner, resource and accounting semantics. This slice
retains callable structure in common MLIR and makes its expansion an explicit
native transformation. It neither adds a universal IR nor changes protocol calls
into ordinary function calls.

[MLIR's Func dialect](https://mlir.llvm.org/docs/Dialects/Func/) provides isolated
functions, typed symbol references and callable/call interfaces. The dedicated
`--zkc-expand-algorithms` pass uses these operations, SSA mappings and cloned
primitive operations. It bounds work, keeps primitive order and locations,
verifies the candidate, and publishes the new module only after success.
`--zkc-project-participants` invokes the same pass on a private copy before
projection. Generic inlining, CSE or DCE does not receive a new preservation
license; [MLIR inliner interfaces](https://mlir.llvm.org/docs/Interfaces/#dialectinlinerinterface)
are mechanisms, not a proof of this profile's origin/accounting obligations.

The starting formal model is
[`Definitions`](../../formal/Zkc/Source/Definitions.lean).
[`DefinitionInlining`](../../formal/Zkc/Compiler/DefinitionInlining.lean) already
proves complete execution equality for capture/reference renaming and a single
retained continuation. It preserves arbitrary primitive handlers, including
stopped outcomes, state and events. It explicitly excludes independently added
call-boundary observations. The new bounded raw adapter in
[`Algorithms.lean`](../../formal/Tools/Interactive/Algorithms.lean) independently
expands admitted source for source-relative checking and reference execution.
It is not a proof that the C++ pass implements that theorem.

## Implemented route

`protocol-source` retains applications. `protocol-import` emits `func.call` in
common algorithm bodies. `protocol-export` round-trips that intermediate form
with full admission. `protocol-expand` emits expanded common source and
`protocol-algorithm-map` reports its primitive occurrences. `protocol-prepare`
retains source protocol port names while specializing and expanding local bodies
for construction consumers. Final participant/physical export refuses residual
applications.

Construction expands through the same native MLIR pass, transports declaration
selectors to their occurrence sets, and preserves ordinary whole local bodies
where its existing resource/replay conditions permit. Affine bodies still use
the existing conservative construction helpers. This does not solve general
cross-call storage lifetime optimization or change the construction machine's
own charges.

Independent Lean preparation checks raw signatures and affine use before
expansion, then checks/elaborates the primitive-only result. Rust executes that
checked result with its ordinary runner. Artifact consumers obtain the expanded
preparation view and authenticate it against the recomputed construction;
original source remains the identity subject. Rust and Lean normalized identity
include transitively called helpers.

## Evidence

[`local_algorithms.py`](../../compiler/test/local_algorithms.py) exercises textual
and JSON authoring, native call transformation, import/export, idempotent
expansion, repeated occurrence maps, malformed calls, nominal-type/affine errors,
unused recursion, exponential empty-call limits, final-stage refusal,
construction selection and independent candidate rejection after a removed guard
or a substituted same-signature callee.

The [group/linear fixture](../../tests/fixtures/local-algorithms.pir)
reuses scalar and group helpers. The
[authentication fixture](../../tests/fixtures/local-authentication.pir)
reuses guards and threads a nonce through commit and response. Native/Lean nonce
comparisons cover successful outputs, guard failures before/after consumption,
resource-budget exhaustion, exact origin traces, post-state and frame cleanup.
The [linear fixture](../../tests/fixtures/local-linear.pir) reuses a
multilinear fold; the independent physical interpreter compares instructions,
retained bytes, active frames, operation attempts, primitive failures and output
allocation exhaustion. Group equations remain explicit primitive-service
premises in the Lean nonce reference.

The [artifact regression](../../tests/protocol/test_local_composition.py) produces
and validates proofs from [nested draws](../../tests/fixtures/local-construction.pir)
with both exact and normalized identity. It compares full native/Lean traces,
proof cursor and transcript-budget stops, checks distinct challenges, compares
Rust/Lean identity, and validates an existing normalized proof after nested site
relabeling. SHA256 and Merlin are supplied by the existing public primitive
service; reference control/expansion does not reuse native event answers.

The [generic regression](../../tests/protocol/test_generic_composition.py) checks
requirement entailment, partial configurations, forward references, associated
static substitution, nominal/affine refusals, unused declarations, recursion,
depth and empty-call expansion bounds. The Rust `generic_reference` suite executes
[the same nested algorithm](../../tests/fixtures/generic-composition.pir)
in BLS12-381's scalar field and KoalaBear, including different modular wraparound,
and compares results and complete primitive traces with Lean. The artifact
regression also accepts [generic nested draws](../../tests/fixtures/generic-construction.pir),
with original generic-definition selectors, normalized identity, transitive
partial-configuration closure and proof reuse after site relabeling.

The [formal controls](../../formal/Tests/SourceDefinitions.lean) additionally
instantiate primitive-budget exhaustion and complete-result inlining equality.
They are scoped typed laws, not native allocation or cryptographic proofs.

## Limits and extension points

Recursion, indirect calls and external callbacks remain unsupported.
[Structured local branches and finite loops](local-control.md) retain explicit
regions through expansion; their entered bodies have separately charged frames. Generic bodies call generic definitions/configurations; ordinary
closed bodies can also call those targets with concrete residual arguments.
Long nested paths can exceed the 128-byte site limit and are refused. Expansion may hit instruction/byte ceilings even for a
compact DAG. There is no expansion cost improvement claim.

Callable effect summaries are conservative: every primitive is retained.
Connecting the main compiler's shared contract facets to algorithm summaries is
future work; this change does not define a second contract catalog. Native
elaboration/expansion adequacy, general frame-preserving calls, cross-call
lifetime optimization and whole-protocol security remain unproved or
unimplemented. Existing operation and backend limits remain in force.
