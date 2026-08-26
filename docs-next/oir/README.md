# OIR and Endpoint Semantics

> **Document kind:** Domain index
> **Document state:** Scaffold
> **Target alignment:** Stage 3 package boundary selected; the minimum
> PIR-to-OIR read seam is active as semantic-kernel pressure, while full Stage
> 4B OIR design remains unactivated
> **Provisional owner:** `oir`
> **Authority:** None during the transition. Current endpoint semantics remain
> governed by the [Endpoints](../../docs/spec/endpoints.md),
> [Boundaries](../../docs/spec/boundaries.md), and
> [Carrier](../../docs/spec/carrier.md) specifications.

> **K3-B alignment notice — 2026-08-27:** The projection/local-validity split
> remains selected, but K3-B rejected whole-`ProverPlanId` coupling and did not
> select a generic purpose-view constructor. Its source-ID-free
> `PlanWitnessSurface` serves only the Relations witness-attachment seam and is
> not an OIR input by default. K3-D must define any OIR-specific Interface or
> Plan view, its closed purpose grammar, exact read manifest, adequacy law,
> checked extraction, and identity effect. The `InterfaceAndPlan` schema below
> is retained as a historical pre-K3 candidate, not a current target contract.

## Purpose

`oir/` owns canonical prover and verifier endpoint subjects derived from an
exact admitted Protocol, admitted `ProtocolInterface`, endpoint role, and
explicit projection basis. It owns OIR meaning, identity, local admission,
source-relative projection correctness, endpoint ABI, protected effects, and
the abstract execution contract a realization must preserve.

It stops where concrete supplier designation, generated artifacts, deployment,
and invocation begin.

## Owns

- endpoint kinds and semantic roles;
- `ProjectEndpoint` and relation-specific `CheckProjection` contracts;
- `ProjectionCorrect(P, I, role, basis, O)`, including exact source-obligation
  coverage and protected-effect correspondence, together with the projection
  check's distinct qualified outcomes;
- the eventual explicit projection-basis contract and its complete source read
  manifest, without ambient Plan access; K3-D has not yet selected its exact
  variants;
- OIR program, carrier, canonical identity, and identity-authenticated endpoint
  ABI;
- standalone OIR authentication and admission under `LocalOirValid(O)`;
- proof-stream and statement interfaces;
- protected transcript, challenge, check, hole, claim, artifact, and terminal
  effects;
- projected `check_call` and `hole_call` behavior;
- verifier/prover duality and counterparty consistency;
- abstract supplier requirements and hole interfaces;
- abstract execution semantics and typed result taxonomy; and
- endpoint-specific preservation obligations that a realization must satisfy.

## Does not own

- Protocol meaning, admission, or source projection-obligation definition;
- `ProtocolInterface` meaning or `ProverPlan` meaning and coverage;
- relation truth or runtime witness ownership;
- property judgments or compiler transformations;
- selection or authority of concrete libraries, kernels, services, devices,
  transports, or other suppliers;
- emitted source trees, packages, or binaries;
- deployment, invocation, session, or concrete runtime lifecycle;
- realization correspondence, attributed operational records, evidence
  appraisal, or consumer reliance; or
- current backend support.

Endpoint semantics and endpoint implementations remain distinct even when a
reference interpreter executes OIR directly. The abstract execution relation
belongs here. A reference interpreter is a concrete realization and an
observation producer; its implementation does not become semantic authority.

## Projection boundary

The following pre-K3 candidate records the boundary that motivated the K3-B
reconciliation. It is historical where it selects `InterfaceAndPlan`; the
alignment notice above governs until K3-D supplies the replacement:

```text
ProjectionInput =
    AdmittedProtocol[P]
  + AdmittedProtocolInterface[I -> P]
  + EndpointRole
  + ProjectionBasis =
      InterfaceOnly
    | InterfaceAndPlan(
        AdmittedPlan[L -> P],
        affirmative CheckedPlanRealizes[L -> P])
  + OirSemanticRegime
  + exact dependency closure
  + declared source read set
  + source-owned view adequacy

ProjectEndpoint(ProjectionInput)
  -> Qualified<CanonicalOirCandidate, ProjectionAudit>

AuthenticateAndAdmitOir(candidate, exact OIR dependencies and checkers)
  -> AdmittedOir[O] establishing LocalOirValid(O)

CheckProjection(ProjectionInput, AdmittedOir[O], exact checker basis)
  -> Qualified<CheckedProjection>

affirmative CheckedProjection only
  -> ProjectedOirCapability[P, I, role, basis, O]
     carrying ProjectionCorrect(P, I, role, basis, O)
```

Verifier projection does not consume a Plan. The historical candidate allowed
a generic prover-obligation skeleton to use `InterfaceOnly` and a specialized
prover OIR to use `InterfaceAndPlan`; neither spelling is a current K3-B
selection. In particular, `PlanWitnessSurface` cannot substitute for an
OIR-owned purpose-specific source contract. K3-D must make every permitted read
explicit and prove the corresponding adequacy and identity effect. Information
classified by that exact reader as realization-only remains outside OIR and is
supplied explicitly to realization. The same Plan fact may not arrive
ambiently at both boundaries.

Carrier labels, compiler state, retained projector state, and process-global
defaults cannot substitute for the Interface, Plan, role, regime, or cited
dependency closure.

## Local validity and source-relative correctness

These judgments are deliberately non-interchangeable:

```text
LocalOirValid(O, OirSemanticRegime, local_dependency_closure)

ProjectionCorrect(P, I, role, basis, O)
```

Local admission can authenticate OIR identity, grammar, role frame, endpoint
ABI, linear resources, local references, and protected-effect
well-formedness. It cannot quantify over an omitted Protocol obligation set.
An embedded source ID or source map is useful data, not proof that no source
obligation was omitted.

A successful projection therefore returns a paired process-local capability
while the exact admitted source subjects and OIR coexist. Serialization
preserves OIR content and ordinary source references, not that capability. A
source-free consumer may establish only `LocalOirValid`. To recover
source-relative coverage after reset, it reauthenticates and readmits every
exact source and reruns the projection check. A future consumer-justified
durable result must still bind the complete source tuple, basis, maps, regimes,
checker, qualified outcome, and dependency/read closure; it is not a portable
live capability or a default v0 artifact.

The default projection schema does not yet include a relation-facing source.
Any Stage 4B variant that adds one must define a complete OIR-owned intake
envelope: the exact admitted `RelationInterface` or exact affirmative checked
correspondence value, its complete `ExactAdmittedSubjectAuthorityBinding` or
`ExactCheckedResultAuthorityBinding`, inert `OwnerCapabilityRequirement`,
authenticated `OwnerOperationPolicyDisposition`, canonical total transitive
source-policy closure, a separately supplied fresh binding-matched capability,
and an exact OIR `NamedConsumer` plus typed operation purpose. The checked-
result binding and separately supplied capability must retain the same
affirmative polarity. The transition must freshly
authorize every bound policy and every explicit no-policy contract/ABI branch
before reading the source. A relation ID, capability name, or source read set
alone is not a legal intake. This paragraph reserves the complete boundary; it
does not activate the variant or select its operation contract or result.

A completed negative projection retains only its exact mismatches and
unaffected agreements. `Unsupported`, `CannotAnswer`, `Refused`, `Malformed`,
and `CheckerFailure` remain distinct from both A and N and mint no checked
projection capability. None invalidates an independently admitted Protocol or
Interface or constitutes verifier rejection.

## Dependencies

- `foundation/` for identity, authentication, admission, encoding, capability,
  and evolution mechanisms;
- `pir/` for exact admitted Protocol authority and purpose-specific views of
  events, ports and occurrences, values and objects, protected observations,
  challenges, checks, claims, failures, terminals, endpoint and prover
  obligations, and challenge-interpretation facts, plus the PIR-owned admitted
  `ProtocolInterface` and optional `ProverPlan` views under their exact
  dependent identities;
- `relations/` only for a separately declared relation-facing projection
  variant that adds the complete exact source-authority envelope, fresh matching
  capability, OIR consumer/purpose authorization, and complete read set stated
  above; and
- domain-owned contract definitions cited by endpoint operations.

The default projection tuple has no relation-correspondence or composition-
history premise and reads no authoring provenance. Neither history nor checked
authority may be recovered from a Protocol view, carrier metadata, or a source
ID.

Projection has no semantic dependency on compiler selection: any suitable
admitted Protocol may be projected regardless of how it was authored or
selected.

## Consumers and outputs

- `realization/` consumes admitted OIR, abstract supplier requirements, and
  the preservation contract;
- `relations/` may consume a verifier endpoint through a separately owned
  descent bridge;
- `evidence/` may record projection, interpreter, conformance, and execution
  observations without changing their meaning; and
- guides expose projection, local admission, and endpoint-inspection
  workflows.

## Bridge ownership

`oir/` owns three non-interchangeable transitions: unauthoritative endpoint
candidate production, standalone OIR authentication/admission establishing
only `LocalOirValid`, and the exact source-relative projection check. Protocol/
PIR owns the source obligations and the PIR-owned Interface and Plan retain
their meanings; OIR owns exact coverage, target construction, target identity,
and qualified projection outcomes. Candidate production grants no OIR
admission, and local admission grants no `ProjectionCorrect` authority.

The OIR-to-concrete-realization bridges belong to `realization/`. OIR states
what must be preserved; realization designates suppliers, produces exact
artifacts, and returns a qualified target-specific preservation result. Only
its exact affirmative variant may mint realization authority.

## Candidate internal topics

- projection contracts, exact coverage, and source maps;
- OIR programs, carrier, identity, and ABI;
- standalone OIR admission;
- verifier semantics;
- prover semantics, construction holes, and plan-specialized projection;
- abstract execution and result taxonomy; and
- preservation interface to realization.

## Open design questions

- What exact OIR grammar, canonical encoding, and local admission basis realize
  this boundary?
- What exact protected-trace and source-map facets constitute
  `ProjectionCorrect`?
- Which individual `ProverPlan` fields change canonical prover OIR, and which
  remain explicit below-OIR realization inputs?
- Which remaining CheckContract and HoleContract fields belong to Protocol
  citation and routing, abstract endpoint behavior, or concrete realization
  binding?
- Which parts of the abstract requirement vocabulary belong to OIR, and which
  are target-specific realization constraints?
- Does a named independent consumer justify a durable source-bound projection
  result, or is source re-admission and direct rechecking sufficient?
- When does an optimization remain OIR-preserving scheduling, and when does it
  change Protocol behavior and require a checked Protocol transition?
