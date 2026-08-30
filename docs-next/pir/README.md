# Protocol IR

> **Document kind:** Domain index
> **Document state:** Active target-domain index
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current protocol semantics remain
> governed by the relevant [normative specifications](../../docs/spec/overview.md).
> **Closure interpretation:** This index records a selected package-resolution
> target. `Selected`, `target`, and `exact` describe intended role, scope, and
> ownership; they do not assert integrated definition closure or semantic
> freeze. The [v0 Semantic Design Program](../project/v0-design-program.md#14-progress-and-change-control)
> owns the live gate.

## Purpose

The design program selects `pir/` as the conceptual owner of a distinct small
closed canonical Protocol level in MLIR. In the selected target, PIR denotes
exactly one Protocol under one typed semantic regime, with one physically
canonical carrier bijective to a finite language-independent operational
model. Rich authoring, import, and synthesis forms remain in an upstream MLIR
workbench; they are not admitted PIR merely because they use MLIR or share
some canonical operations.

The selected [Protocol IR Architecture](../project/protocol-ir-architecture.md)
defines the subject factorization, identity algebra, and canonical-level
contract. The selected
[Transition and Bridge Architecture](../project/transition-and-bridge-architecture.md)
fixes the Protocol lifecycle and its downstream authority boundaries. The
selected [Protocol and Relations Architecture](../project/protocol-and-relations-architecture.md)
records the package-selection snapshot and alternatives. The completed
research packages, routed through the
[temporary workspace inventory](../notes/README.md#working-note-inventory),
preserve the comparative evidence. Current normative Protocol semantics
remain under `docs/` until explicit cutover.

Native-oracle pressure now also selects a distinct, exact
[Oracle-Commitment Construction](oracle-commitment-construction.md). It maps
one admitted logical-Oracle Core to one independently admitted committed Core
through deterministic bounded elaboration and total static maps. This is a
Core-changing construction, unlike the same-Core Fresh/Fiat--Shamir
construction, and it establishes no cryptographic property by itself.

The durable target now aligns the canonical carrier, `ProtocolInterface`, and
`ProverPlan`, including the narrow source-ID-free `PlanWitnessSurface` needed
for relation-witness attachment. Minimum Analysis consumers, purpose-specific
endpoint views, and the joined owner-view/read/authority boundary have also
been reconciled without changing the verifier-observable Core or the
Fresh/Fiat--Shamir factorization. This bounded closure does not freeze the
integrated kernel: broader protocol-family pressure and independent freeze
review remain pending.

## Owns

- the exact `InteractiveCore`, challenge interpretation, and complete abstract
  Protocol semantics realized bijectively by canonical PIR;
- exact `InitialOracle` and `ProverOracle` origins, finite exact-domain logical
  access, owner-local initial-input preparation, and causal Oracle lifetimes;
- transcript spine ordering and protected protocol effects;
- claims, reductions, checks, challenges, material bindings, routes, and
  terminal closure;
- protocol-specific vocabularies, profiles, policies, and extension points;
- exact portable verifier computations and supported module-effect citations,
  their Protocol-facing ABI, observation, decision, influence, replay,
  terminal, and dependency meaning; the selected base Plan has no opaque hole;
- the direct typed declaration manifest, semantic-authority graph, and distinction
  from opaque referenced subjects;
- the workbench transitions that author, import, resolve, and normalize
  proposals, including exact resolution closure and unauthoritative side
  outputs;
- the closed canonical PIR grammar and the complete lifecycle
  `AuthoringUnit -> ResolvedAuthoringUnit -> CanonicalProtocolCandidate ->
  AuthenticatedCanonicalProtocol -> AdmittedProtocol`;
- separately identified `ProtocolInterface` and `ProverPlan` subjects,
  including their Protocol-dependent identities, authentication, admission,
  codecs or construction descriptors, and the separate `PlanRealizes` bridge;
- Protocol authentication, whole-Protocol admission, official admitted-only
  persistence, decoding, re-authentication, and re-admission;
- question-scoped authenticated Protocol views whose definitions remain owned
  by PIR and whose additional judgment semantics remain with each consumer;
- the causal, purpose-bound, whole-carrier confidential initial-Oracle view;
- reopening as an independent mutable branch that inherits no output authority;
- structural formation, well-formedness, linearity, binding, closure,
  canonical authentication, and whole-Protocol admission judgments;
- projection obligations exported to endpoint consumers;
- authoring `link` as proposal construction, and semantic Protocol composition
  through an independently admitted `CoreCompositionSpec`, construction and
  whole-Protocol admission of a new `InteractiveCore`, and an exact
  `CheckedCoreComposition` structural result;
- separately admitted `TranscriptConstruction`, deterministic Fresh-to-Fiat--
  Shamir construction, independently admitted target Protocol, and exact
  `CheckedFSConstruction` structural result, while Analysis retains ownership
  of exact theorem applicability and property-specific transport (the
  historical packages' `FSCompile` umbrella);
- separately admitted exact Oracle-commitment constructions that elaborate a
  logical-Oracle source Core into an independently admitted commitment-and-
  opening target Core, together with total occurrence maps, construction-owned
  advice, intrinsic bounds, process-local checked authority, and inert
  execution receipts;
- PIR carrier semantics, the canonical Protocol identity projection, and
  artifact format; and
- authenticated structural facts explicitly exported to later consumers.

## Does not own

- relation satisfaction, relation-source compilation, or witness generation;
- rich authoring, import, macro, or synthesis languages merely because they
  lower into PIR;
- runtime Interface inputs, private witness values, concrete secrets, provider
  capabilities, or live Plan execution state;
- soundness, knowledge, completeness, zero knowledge, or their bounds;
- compiler search, scoring, or selection merely because it produces PIR;
- OIR or realized endpoint coverage;
- backend emission, deployment, invocation, or concrete runtime suppliers;
- evidence grades or current implementation support; or
- MLIR classes and pass structure as architectural boundaries.

Structural predicates such as formation, `WF`, linearity, binding, closure,
canonical authentication, whole-Protocol admission, and link remain here even
though they are judgments. The top-level `analysis/` domain does not own every
proposition written with an inference rule.

## Dependencies

- `foundation/` for identity, authentication, admission, encoding, and common
  lifecycle rules; and
- domain-owned vocabulary entries for any admitted external extension.

PIR carries relation-shaped anchors and identities opaquely. Protocol
normalization, authentication, and admission do not load a RelationContract or
import later relation-interface facts.

`ProtocolInterface` and `ProverPlan` are separately formed, authenticated, and
admitted dependent subjects. PIR does not absorb either into `ProtocolId`.
Every downstream edge that reads one must cite its exact dependent identity;
Protocol-only consumers remain independent of both. A Plan is additionally
subject to a separate `PlanRealizes` judgment over the exact admitted Protocol,
admitted Plan, owner-derived `StrategyDecisionView`, and matching
`DependentAdmissionBasis`. It cannot change verifier-visible Protocol
behavior. PIR may derive a source-ID-free `PlanWitnessSurface` for the narrow
Relations attachment seam; its checked extraction retains source authority
without placing the Plan ID or Plan-local references in the surface identity.

PIR must remain meaningful without depending on the compiler or endpoint
realization. A Protocol may be authored, authenticated, and admitted without
first being found by the optimizer or successfully projected to every target.

## Consumers and outputs

- `analysis/` consumes exact admitted Protocol subjects and narrow PIR-owned
  authenticated views; it adds an admitted `TranscriptConstruction`,
  affirmative `CheckedFSConstruction`, exact checked Oracle-commitment
  construction, admitted `CoreCompositionSpec`, affirmative
  `CheckedCoreComposition`, Interface, or Plan only when its exact family
  question or rule reads that structural satellite or result; none of those
  PIR-owned structural results establishes a property by itself;
- `relations/` consumes an admitted Protocol, independently admitted relation
  subjects, and a `ProtocolRelationBinding` for structural correspondence. A
  separate `PlanWitnessBinding` may attach relation-witness occurrences to one
  source-ID-free `PlanWitnessSurface`. An admitted `ProtocolInterface` is an
  additional operand only for questions about external presentation; it is not
  a universal relation dependency. Checked artifact, equation, commitment, and
  run-grounding prerequisites—including any exact Oracle-commitment
  construction view and matching live authority—remain question-specific. A
  confidential initial logical Oracle is available only through the PIR-owned
  `ConfidentialInitialOracleView` and its matching causal, purpose-bound live
  capability; raw observations and replay candidates cannot substitute for
  either checked result;
- `compiler/` may propose successors, but PIR alone authenticates and admits
  each target; a separate relation-specific checker must then relate exact
  predecessor and successor subjects;
- `oir/` consumes affirmative checked purpose-specific
  [endpoint views](endpoint-projection-views.md) over an exact admitted
  Protocol and Interface and, for a plan-specialized prover, an exact admitted
  Plan plus affirmative `CheckedPlanRealizes`. Neither a whole source ID nor
  the Relations-specific `PlanWitnessSurface` enters OIR semantics;
- `evidence/` binds conformance observations to exact PIR subjects.

## Target documents

- [Selected Protocol IR Architecture](../project/protocol-ir-architecture.md)
- [Selected Protocol and Relations Architecture](../project/protocol-and-relations-architecture.md)
- [Interactive Core and Causal Execution](interactive-core.md) — active target
  definition owner for Core, Protocol, causal execution, public coin, and the
  standard Oracle lifecycle, including initial/prover origins, logical access,
  and the confidential initial-Oracle view
- [Fiat--Shamir Construction](fiat-shamir.md) — active target owner for
  transcript semantics and the same-Core Fresh/FS construction
- [Oracle-Commitment Construction](oracle-commitment-construction.md) — exact
  logical-Oracle-to-committed-Core elaboration, admission, authority, and run
  validation boundary
- [Canonical PIR](canonical-pir.md)
- [Protocol Interfaces and Prover Plans](interfaces-and-plans.md)
- [Endpoint Projection Views](endpoint-projection-views.md)
- [Protocol Semantic Model](protocol-model.md) — superseded semantic snapshot
- [Fiat--Shamir Construction and Semantic Core Composition](fiat-shamir-and-composition.md)
  — superseded FS snapshot and historical composition candidate
- [Candidate Protocol Subject and Lifecycle](protocol-lifecycle.md)

The two project architecture pages are selected non-normative research
decisions. Later revalidation replaced the Core/Protocol and Fiat--Shamir
definition surfaces with the first two active target pages above. A
narrow reclosure preserved that architecture while repairing exact transcript
bodies and evidence boundaries; its validation record owns the details.
The carrier and Interface/Plan pages are the current non-normative target
definitions at that bounded scope. The two explicitly marked snapshots remain
research history, not parallel authority. Bounded Analysis sources and exact
OIR-purpose reads, quotient identities, adequacy, and checked extraction now
consume these owners; the target relation remains independently owned by OIR.
The lifecycle page is the
superseded baseline candidate and remains useful for current-model
reconstruction. None replaces the current Protocol Kernel, Carrier,
Boundaries, Vocabularies, or Versioning specifications before normative
cutover.

## Lifecycle and bridge ownership

PIR owns proposal formation and closure, normalization, Protocol
authentication and admission, representation changes, authority loss, and
abstract composition semantics. Authentication and admission remain logically
distinct even when one implementation shares a traversal. Official Protocol
persistence is admission-gated; a workbench cache must use an unmistakably
unauthoritative envelope. Decoding produces a carrier, not authority, and
reopening preserves only lineage.

PIR owns every exported Protocol view's source facts and checked derivation.
The consumer owns its closed read manifest, adequacy requirement, and
additional proposition:

- a PIR-owned fact view plus an Analysis question is interpreted by
  `analysis/`;
- admitted Protocol plus exact Interface and role, together with the exact
  affirmative purpose-specific endpoint views, belongs to
  `oir/`;
- Protocol-to-relation correspondence and Plan-witness attachment belong to
  separate `relations/` bindings; an external Interface enters only a question
  that reads its presentation;
- PIR facts used by compiler constraints belong to the compiler ingress or
  constraint contract.

For a checked Protocol change, the producer forms a proposal, PIR
authenticates and admits the target, the relation-specific bridge checks the
predecessor/successor relation, and only then may Compiler select or Analysis
transport a property. Target admission alone proves no source/target relation.

## Reopened integrated-closure and later-owner questions

The current package closes executable Foundation/PIR semantics, dependent
Interface/Plan and Relations seams, minimum Analysis contracts, bounded OIR
projection, and the joined owner-view/read/authority paths at their stated
resolutions. It includes exact static views, an affirmative checked FS
construction and issued FS view, an Interface correspondence view, and an
affirmative `CheckedPlanRealizes` path. It is not yet a protocol-portfolio
freeze. Later work includes:

- broader Analysis theorem profiles, independent proof authority, checkers,
  and producers beyond the selected finite applicability profile;
- OIR syntax and execution beyond the bounded semantic skeleton, followed by
  concrete supplier, deployment, and runtime meaning in Realization;
- exact normative wording, stable semantic encodings, hash primitives,
  compatibility policy, and authority cutover; and
- implementation correspondence and migration work.
