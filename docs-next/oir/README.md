# OIR and Endpoint Semantics

> **Document kind:** Domain index
> **Document state:** Active bounded K3-D target
> **Target alignment:** Minimum PIR-to-OIR semantic and projection boundary
> selected; full Stage 4B remains unactivated
> **Provisional owner:** `oir`
> **Authority:** None during transition. Current endpoint semantics remain
> governed by the [Endpoints](../../docs/spec/endpoints.md),
> [Boundaries](../../docs/spec/boundaries.md), and
> [Carrier](../../docs/spec/carrier.md) specifications.

## Purpose

`oir/` owns canonical prover and verifier endpoint meaning. It separates:

- source-independent endpoint validity;
- exact source-relative projection correctness;
- the static role contract needed by a later verifier/prover consistency
  judgment; and
- the abstract behavior a concrete realization must preserve.

The bounded K3-D target is specified by the
[OIR Endpoint and Projection Contract](projection-contract.md). PIR owns the
purpose-specific source views in
[Endpoint Projection Views](../pir/endpoint-projection-views.md). Full OIR
syntax, carrier encoding, general optimization, and concrete realization are
not selected here.

## Owns

- joint ownership with PIR of the canonical bridge graph schema: role,
  dependencies/types, constants/pure nodes, slot-centric ABI, action spine,
  static FS semantics, complete claims/reductions/terminals, and reachable Plan
  graph; PIR owns source extraction while OIR owns target formation/admission;
- the shared exact `EndpointContractLawV0` evaluator deriving one closed
  `DerivedEndpointContractBody`—static obligations, exact requirements, and
  completion interface—from that graph;
- canonical semantic `OirId` and exact semantic dependency closure;
- standalone OIR authentication and admission under `LocalOirValid`;
- the unauthoritative `ProjectEndpoint` operation;
- the independent semantic `ProjectionProposition`, request-specific
  `ValidateProjection`, and their qualified outcomes;
- exact canonical graph equality for the bounded no-rewrite relation profile,
  with negative role/dataflow constraints enforced during graph admission;
- process-local `ProjectedOirCapability` on affirmative correspondence only;
- the explicit deferral contract for source-independent verifier/prover
  pairing; and
- the static preservation boundary consumed by Realization, while Stage 4B
  retains ownership of dynamic OIR execution.

## Does not own

- Protocol, `ProtocolInterface`, `ProverPlan`, their admission, or their
  purpose-specific source views;
- relation truth, witness correspondence, Analysis properties, or Compiler
  selection;
- protocol transformations such as Fiat--Shamir conversion,
  arithmetization, commitment selection, or IOP compilation;
- concrete suppliers, generated artifacts, libraries, devices, services,
  deployment, invocation, or sessions;
- evidence appraisal or consumer reliance; or
- current backend support.

Endpoint semantics and endpoint implementations remain distinct even when a
reference interpreter executes OIR directly.

## Minimum selected boundary

```text
exact admitted PIR sources
  -> pre-view support classification
  -> affirmative PIR-owned purpose-specific source views
  -> unauthoritative OIR candidate
  -> OIR authentication and local admission
       establishes LocalOirValid(O)
  -> semantic proposition formation
  -> independent request-specific projection validation
       establishes ProjectionCorrect(source, O) only on Affirmative
  -> later Realization preservation boundary
```

`LocalOirValid` and `ProjectionCorrect` are non-interchangeable. A coherent
standalone endpoint with no live source authority may still omit, duplicate,
reorder, or alter a base graph action from which a static source obligation is
derived. Conversely, malformed target bytes never become a
projection proposition merely because a producer supplies a source map.

`OirId` commits to the canonical base graph and exact used semantic
dependencies. It does not commit to whole source IDs, source maps, projectors,
checkers, capabilities, evidence, or runtime receipts. The exact source tuple,
manifest, live authorities, checker, and limits bind the validation
request and its process-local capability. The semantic proposition itself
binds only purpose, the complete source-view ID, target OIR ID, and relation
profile; equivalent exact sources yielding the same view may share it. The
bounded exact-equality profile has no producer correspondence witness. Both
profiles select and rerun the same exact endpoint-contract law, so the
complete static obligations, requirements, and completion interface cannot
drift outside the equality check. Runtime presence, state versions, draws,
wire packaging, and reached outcomes remain explicit Stage 4B non-claims.

## Bounded support

K3-D supports FS verifier and FS Plan-specialized prover endpoints over the
base K2 non-Oracle, non-module effect language and base Plan recipes. Fresh,
generic prover, native Oracle, and every module-effect path are recognized
typed `Unsupported` cases before view extraction, with no partial target. Once
a proposition forms, validation cannot return feature `Unsupported`. A legacy imported-verifier
carrier lacking a supported K2 module-effect contract stops earlier at PIR
admission; it cannot be described as an OIR refusal.

This conservative table is a bounded closure, not a rejection of later
profiles. Any extension must define its source view, target effect law,
coverage rule, identity effect, execution rule, and negative tests.

Local OIR admission is source-blind but not evidence-free. It independently
reauthenticates exact dependency preimages, reruns
`EndpointContractLawV0`, and requires a total K3-B admission-evidence map for
every and only General codec node. Certificate checks remain admission-only;
runtime endpoint requirements contain only the resolved encoder/decoder uses.

## Dependencies

- `foundation/` for identities, semantic bases, authentication, admission,
  capabilities, canonical values, evaluation, and qualified outcomes;
- `pir/` for exact admitted Protocol, Interface, optional Plan and
  `CheckedPlanRealizes`, plus affirmative owner-derived endpoint views; and
- exact domain-owned semantic contracts named by the endpoint body.

The base projection has no Relation, Analysis, Compiler, Evidence, authoring
history, or realization-artifact premise. A later variant that reads another
owner must define a complete exact authority envelope and a new closed purpose
profile; a foreign ID or carrier label is insufficient.

## Consumers and outputs

- `realization/` consumes admitted OIR and its exact derived requirement set,
  keyed by `(OirId, OirRequirementBody)`, then checks concrete preservation
  independently;
- `relations/` may consume a projected verifier endpoint only through a
  separately specified relation-facing bridge;
- `evidence/` may record projection, interpreter, conformance, and execution
  observations without changing their meaning; and
- guides may expose projection, local admission, and inspection workflows;
  pairing remains a Stage 4B design subject.

## Lifecycle and persistence

Candidate production grants no OIR authority. Local OIR admission grants no
source-relative authority. Only an affirmative completed projection validation
mints a live projection capability. The capability is not serialized; cold
recovery reauthenticates and readmits every exact source and target and reruns
support classification, source-view extraction, proposition formation, and
validation.

K3-D selects no durable projection certificate because no named independent
v0 consumer requires one. A future certificate must bind the complete
proposition and qualified result and still cannot serialize live authority.

## Target documents

- [OIR Endpoint and Projection Contract](projection-contract.md)
- [PIR Endpoint Projection Views](../pir/endpoint-projection-views.md)
- [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md)
- [Interactive Core and Causal Execution](../pir/interactive-core.md)
- [Fiat--Shamir Construction](../pir/fiat-shamir.md)

## Deferred questions

- final MLIR grammar, canonical encoding, and bytecode profile;
- abstract execution detail beyond the bounded semantic skeleton;
- Fresh, generic-prover, Oracle, and standardized module-effect profiles;
- optimization/refinement relations over complete OIR programs;
- exact source-independent endpoint-pair normalization, duality, and
  authority;
- whether a named consumer justifies a portable projection result; and
- Stage 4B Realization, deployment, invocation, and backend support.
