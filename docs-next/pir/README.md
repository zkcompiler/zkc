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

Stage 1 selected `pir/` as the conceptual owner of a distinct small closed
canonical Protocol level in MLIR. Stage 3 selected and promoted a candidate at
its package resolution: in that candidate, PIR denotes
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
records the Stage 3 package-selection snapshot and alternatives. The completed
research packages, routed through the
[temporary workspace inventory](../notes/README.md#working-note-inventory),
preserve the comparative evidence. Current normative Protocol semantics
remain under `docs/` until explicit cutover.

## Owns

- the exact `InteractiveCore`, challenge interpretation, and complete abstract
  Protocol semantics realized bijectively by canonical PIR;
- transcript spine ordering and protected protocol effects;
- claims, reductions, checks, challenges, material bindings, routes, and
  terminal closure;
- protocol-specific vocabularies, profiles, policies, and extension points;
- identity-bearing CheckContract and HoleContract citations, their
  protocol-facing ABI, and route or attachment meaning;
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
  of `FSCompile` property meaning;
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
subject to a separate
`PlanRealizes(AdmittedProtocol, AdmittedPlan, PlanRealizesRegime)` judgment and
cannot change verifier-visible Protocol behavior.

PIR must remain meaningful without depending on the compiler or endpoint
realization. A Protocol may be authored, authenticated, and admitted without
first being found by the optimizer or successfully projected to every target.

## Consumers and outputs

- `analysis/` consumes exact admitted Protocol subjects and narrow PIR-owned
  authenticated views; it adds an admitted `TranscriptConstruction`,
  affirmative `CheckedFSConstruction`, admitted `CoreCompositionSpec`,
  affirmative `CheckedCoreComposition`, Interface, or Plan only when its exact
  family question or rule reads that structural satellite or result; none of
  those PIR-owned structural results establishes a property by itself;
- `relations/` consumes an admitted Protocol, the exact admitted
  `ProtocolInterface`, an independently admitted relation interface and
  binding, an exact correspondence question, and conditionally required
  checked artifact-comparison/grounding prerequisites to derive post-admission
  correspondence without changing the Protocol; a raw artifact observation
  cannot substitute for those checked prerequisites;
- `compiler/` may propose successors, but PIR alone authenticates and admits
  each target; a separate relation-specific checker must then relate exact
  predecessor and successor subjects;
- `oir/` consumes an admitted Protocol, an exact admitted Interface, its
  projection obligations, and a tagged `InterfaceOnly` or
  `InterfaceAndPlan(admitted Plan, checked PlanRealizes capability)` basis when
  prover projection actually reads a Plan;
- `evidence/` binds conformance observations to exact PIR subjects.

## Target documents

- [Selected Protocol IR Architecture](../project/protocol-ir-architecture.md)
- [Selected Protocol and Relations Architecture](../project/protocol-and-relations-architecture.md)
- [Interactive Core and Causal Execution](interactive-core.md) — active K2
  definition owner for Core, Protocol, causal execution, public coin, and the
  standard Oracle lifecycle
- [Fiat--Shamir Construction](fiat-shamir.md) — active K2 definition owner for
  transcript semantics and the same-Core Fresh/FS construction
- [Canonical PIR](canonical-pir.md)
- [Protocol Interfaces and Prover Plans](interfaces-and-plans.md)
- [Protocol Semantic Model](protocol-model.md) — pre-K2 semantic snapshot
- [Fiat--Shamir Construction and Semantic Core Composition](fiat-shamir-and-composition.md)
  — pre-K2 FS snapshot and historical composition candidate
- [Candidate Protocol Subject and Lifecycle](protocol-lifecycle.md)

The two project architecture pages are selected non-normative Stage 1 and
Stage 3 decisions. K2 revalidated and replaced the Core/Protocol and
Fiat--Shamir definition surfaces with the first two active K2 pages above. A
narrow reclosure preserved that architecture while repairing exact transcript
bodies and evidence boundaries; its validation record owns the details.
The carrier and Interface/Plan pages remain dependent candidates awaiting
reconciliation; the two explicitly marked snapshots remain research history,
not parallel authority. Stage 4A's Analysis/Compiler source bindings must be
rechecked against the new views in K3. The lifecycle page is the superseded
baseline candidate and remains useful for current-model reconstruction. None
replaces the current Protocol Kernel, Carrier, Boundaries, Vocabularies, or
Versioning specifications before normative cutover.

## Lifecycle and bridge ownership

PIR owns proposal formation and closure, normalization, Protocol
authentication and admission, representation changes, authority loss, and
abstract composition semantics. Authentication and admission remain logically
distinct even when one implementation shares a traversal. Official Protocol
persistence is admission-gated; a workbench cache must use an unmistakably
unauthoritative envelope. Decoding produces a carrier, not authority, and
reopening preserves only lineage.

PIR owns every exported Protocol view's source facts and adequacy boundary, but
not the consumer's additional proposition:

- a PIR-owned fact view plus an Analysis question is interpreted by
  `analysis/`;
- admitted Protocol plus exact Interface, role, and tagged Plan basis to OIR
  belongs to `oir/`;
- Protocol plus Interface plus relation-interface correspondence belongs to
  `relations/`;
- PIR facts used by compiler constraints belong to the compiler ingress or
  constraint contract.

For a checked Protocol change, the producer forms a proposal, PIR
authenticates and admits the target, the relation-specific bridge checks the
predecessor/successor relation, and only then may Compiler select or Analysis
transport a property. Target admission alone proves no source/target relation.

## Reopened integrated-closure and later-owner questions

Stage 3 selected the Core/Protocol grammar, canonical carrier, Interface, Plan,
Fiat--Shamir construction, and structural Core-composition candidate at its
then-current resolution. Post-selection revalidation reopened the exact kernel
closure. K1 and the narrowly reclosed K2 have now closed executable Foundation
and PIR semantics at their bounded resolutions. Before integrated freeze, K3
must treat these as source declarations rather than assumed correspondence,
reconcile the dependent bindings, and test the minimum Relations, Analysis,
and OIR read questions. K4 and K5 must then complete the bounded protocol
portfolio and independent freeze. Later work includes:

- Stage 4A selected the exact Analysis model families and theorem/profile
  architecture for `FSCompile`, composition properties, and property
  transport, together with Compiler relations and selection boundaries, and
  reconciled the four PIR semantic pages with its exact cross-owner source-
  binding contract;
  concrete theorem instances, profiles, checkers, and producers remain later
  work;
- Stage 4B classifies Plan use, defines OIR behavior and projection, and then
  assigns concrete supplier, deployment, and runtime meaning in Realization;
- Stage 7 selects exact normative wording, stable semantic encodings, hash
  primitives, compatibility policy, and authority cutover; and
- Stage 8 establishes implementation correspondence and migration work.
