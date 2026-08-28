# Protocol and Relations architecture

> **Document kind:** Architecture decision
> **Document state:** Active
> **Target decision status:** Selected Stage 3 package result; integrated
> semantic-kernel closure remains under revalidation
> **Provisional owner:** `project`
> **Authority:** Non-normative target architecture for `docs-next/`. The
> current specifications under [`docs/`](../../docs/README.md) remain
> authoritative until normative consolidation, review, and explicit cutover.
> This decision does not claim implementation or migration.
> The [v0 Semantic Design Program](v0-design-program.md#14-progress-and-change-control)
> owns the live integrated-closure gate.
> **Frozen research basis:** target model SHA-256
> `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b`;
> equal-resolution candidate portfolio SHA-256
> `ce4f71e88741f71d126c81ce8afeb2cb29da83f856bb13fdf032a702756b9923`.

> **K1/K2/K3-D reconciliation notice — 2026-08-28:** K1 owns the
> executable Foundation and K2 owns the active Interactive Core and
> Fiat--Shamir construction. They do not ratify this historical Stage 3
> consumer model. Public-coin-Core, port, object, randomness,
> abstract-prover-obligation, authored FS-map, and pre-K1 identity notation
> below are historical where they conflict with the active owners. K3-B has now
> selected current non-normative targets for
> [Interface and Plan](../pir/interfaces-and-plans.md), the
> [canonical carrier](../pir/canonical-pir.md), the
> [relation model](../relations/relation-model.md), and
> [Protocol correspondence](../relations/protocol-correspondence.md), including
> split Protocol/Plan bindings and the three distinct value-bridge lanes. Those
> exact owners supersede conflicting Stage 3 examples. K3-D additionally
> selected [PIR-owned endpoint views](../pir/endpoint-projection-views.md) and
> the bounded [OIR projection contract](../oir/projection-contract.md), without
> freezing the integrated kernel or activating full Stage 4B.

## 1. Decision

The v0 target is a **small language-independent Protocol semantic kernel, one
physically canonical bijective MLIR PIR carrier for that Protocol, and
independently identified typed satellites**.

The integrated topology is:

```text
InteractiveCore + exactly one ChallengeInterpretation = Protocol
                               |
                               v
             one closed canonical MLIR PIR graph
                  with one pir.protocol root

separately identified satellites
  TranscriptConstruction[CoreId, ProtocolSemanticRegime]
  ProtocolInterface[ProtocolId]
  ProverPlan[ProtocolId]
  Relation subjects, bindings, and checked correspondence
  FSConstruction[source ProtocolId, target ProtocolId]
  CoreComposition[ordered child occurrences, target CoreId]

admitted Stage 3 subjects and exact checked structural results
  +--> Stage 4A Analysis, then Compiler
  `--> Stage 4B OIR, then Realization
```

The language-independent algebra is the selected target mathematical meaning,
intended to become normative only through explicit consolidation and cutover;
it is not a second serialized production artifact. MLIR remains the sole
canonical v0 Protocol carrier in that target and the primary transformation
infrastructure. MLIR syntax, registries, passes, printer behavior, and bytecode
do not define semantic meaning, identity, admission, or correctness.

This decision selects the Stage 3 typed-satellite model. It imports the useful
typed-event discipline from the event-calculus alternative without selecting
a universal effect language or handler runtime. A generative module language
is deferred to an optional authoring layer whose output must elaborate away
before ordinary authentication and admission.

## 2. Semantic and carrier topology

### 2.1 Interactive Core and Protocol

`InteractiveCore` owns one finite verifier-visible public-coin interaction. It
contains the exact closed families for semantic dependencies, roles, ports,
values, objects, randomness, challenges, events, causal edges, one total event
schedule, claims, reductions, checks, failures, terminals, endpoint
obligations, prover obligations, and prover-obligation failures.

The Core is occurrence-native:

- ports expand to exact occurrences; input `PortValue`s and output
  `OutputValues` have different semantics, and an output grouping creates no
  exposure, path availability, event occurrence, or role knowledge;
- the fourteen-form value algebra includes canonical `GuardDecision` and
  selected-branch `GuardedMerge`; stored guards use one canonical finite
  decision representation;
- objects have closed ownership, visibility, availability, and protected-use
  contracts rather than ambient runtime meaning;
- the seven event kinds share one six-field `EventDecl` envelope whose actor,
  inputs, protected observations, activation guard, endpoint-contract basis,
  and optional prover-construction basis are exact and kind-derived;
- execution distinguishes attempt from successful action occurrence, performs
  prover preparation before action, and gives challenge attempts explicit
  success and failure semantics;
- claims are global actorless semantic resources with deterministic least
  saturation, not hidden role knowledge; and
- verifier failures, prover nonproduction, malformed invocation, refusal, and
  checker failure remain distinct outcome families.

A `Protocol` is exactly that Core plus one challenge interpretation:

```text
ChallengeInterpretation = FreshPublicCoins
                        | FiatShamir(TranscriptConstructionId)
```

Fresh and Fiat--Shamir interpretations over the same `CoreId` have different
`ProtocolId`s. A Fiat--Shamir Protocol carries only the exact construction
reference and dependency; `TranscriptConstruction` remains a separately
identified subject.

`CoreId` is an embedded semantic subidentity, not a second official artifact
root. The canonical graph has one `pir.protocol` root containing the Core and
selected challenge interpretation. `Lower_R` and authoritative `Read_R` are
bijective with the bounded language-independent Protocol form modulo only the
explicitly permitted in-memory operation identity and required SSA
alpha-renaming.

### 2.2 Identity and algorithms

Each semantic family has an exact typed regime. Semantic identity is a
domain-separated digest of that regime and an injective canonical semantic
encoding. Transport bytes, source names, locations, producer metadata,
process objects, checker builds, and tool releases do not enter the semantic
preimage unless a later contract explicitly promotes a fact into meaning.

Every semantic algorithm field is a `CanonicalAlgorithmSpec`: either a closed
finite typed total term with declared evidence or a regime-qualified
content-addressed contract reference with exact ABI and direct dependency IDs.
Live callbacks, registries, implementations, and checker capabilities cannot
stand in for algorithm identity.

Authoring normalization may search, infer, and erase only when it emits a
capability-neutral audit that classifies each lost distinction as retained,
extracted to a typed satellite, proved neutral in the declared finite quotient,
or rejected before erasure. A normalized output remains a candidate until its
ordinary owner authenticates and admits it.

## 3. Independently owned satellites

### 3.1 Protocol Interface

`ProtocolInterface[ProtocolId]` owns external naming and representation. It
does not own verifier meaning. Several Interfaces may coexist for one
Protocol, and substituting one cannot change Core schedule, values,
challenges, checks, terminal behavior, or transcript semantics.

The active K3-B subject owns exact codecs and their law admission, total public
plus verifier-private invocation assignment, scoped Statement presentation,
role-qualified message/challenge/Oracle/module transport with uniform
`Inactive | Active(T)` presence, and total Core-terminal plus FS-failure
completion presentation. Admission checks declared presentation but does not
assert that every endpoint role is projectable. K3-D therefore derives an
exact role quotient and separately checks `InterfaceAdequateForEndpoint`; a
missing proof transport or codec cannot be filled by OIR.

### 3.2 Prover Plan

`ProverPlan[ProtocolId]` owns finite recipes for the exact K2 prover-decision
boundary, not verifier meaning or live providers. The active base subject
contains typed witness ingress, advice and confidential context; private
randomness availability; persistent strategy state; portable typed acyclic
decision recipes; and separately exposed derived-witness outputs. It contains
no opaque hole, supplier, resource, callback, artifact, or runtime value.

Plan admission proves local grammar, typing, acyclicity, ABI and dependency
closure. The separate `PlanRealizes` relation checks one recipe and legal move
for every potential K2 decision. Neither proves witness truth, algorithm
correctness, termination, honest-prover completeness, cost, secrecy, or proof
acceptance.

K3-D derives a whole-source-provenance-free Plan-specialized endpoint quotient from the
transitive closure reachable from decision moves and state-after roots. Dead
declarations and nodes and derived witness exports do not rotate OIR; reachable
algorithms, randomness, state and move semantics do. The selected base Plan
has no below-OIR field branch. Stage 4B later completes execution and concrete
realization; it does not reclassify the selected base Plan ambiently.

## 4. Relations and artifact ingress

Relations owns distinct identity and authority boundaries for:

```text
RelationDefinitionRef
RelationInterface
RelationInstance
PrivateWitnessAssignment occurrence
RelationBinding
RelationArtifactProfile
RelationAdapterContract
RelationArtifactObservation
```

A relation interface is occurrence-indexed and carries its exact typed least
dependency closure. Public and witness bindings are total and injective over
relation occurrences but need not exhaust Protocol occurrences. Each entry
owns exact bidirectional value-domain bridge algorithms and round-trip laws.
Committed-object grounding is total over relation committed-object
occurrences, may map several independently checked occurrences to one Protocol
object, and claims neither inverse injectivity nor coverage of every Protocol
object.

Relation authoring normalization produces only independently authenticated
candidates plus a capability-neutral audit. Profile admission, adapter
admission, byte interpretation, completed observation authentication,
artifact/interface comparison, binding, grounding, structural
correspondence, instance correspondence, and satisfaction are separate
operations. An observation is formed only by completed interpretation; a raw
artifact, adapter assertion, observation, or binding cannot substitute for a
checked comparison or correspondence result.

Structural correspondence asks any selected subset of four base clauses:

```text
PublicPorts
WitnessPorts
ResultBindingReferenceShape
CommittedObjectGrounding
```

It may additionally ask one optional artifact question. The result-binding
clause checks only the closed constructor/reference shape for a claim, check,
or accepting terminal; the base subset may be empty only when that artifact
question is present. It does not interpret a relation-result domain or prove
behavioral equivalence. Value-level instance correspondence requires an
affirmative public-port structural capability, admitted bridge views and exact
bridge execution authority, and the dependent Protocol public assignment
before comparing converted values.

Nothing in this seam establishes relation truth, satisfiability, witness
validity, or a cryptographic property. A private witness assignment remains an
occurrence-local confidential capability rather than a mandatory public
content-addressed object.

## 5. Fiat--Shamir construction

`TranscriptConstruction` is a separately authenticated subject under one exact
Core's Protocol semantic regime. It owns total public-context initialization,
injective framing, one action per Core event, every-and-only same-event input
absorption, action-occurrence challenge prefixes, a total linked failure map,
and standalone or exact composed context.

Each Core challenge already owns its construction-neutral potential
action-occurrence prefix template. A transcript construction must directly
match its stored prefix to the exact action-wise image of that Core template
and derive the runtime action-occurring subsequence; it cannot select a causal
subset or rewrite Core meaning.

Initialization, context binding, framing, and absorption are total and
infallible. Only challenge squeezing may produce the declared typed sampling
failure. Derivation occurs on challenge attempt; value publication requires
success. Independent and joint annotations are intended distribution
contracts checked structurally at construction time, not proofs of the
induced Fiat--Shamir distribution.

The lifecycle is deliberately three-step:

```text
ConstructFS(admitted Fresh Protocol, admitted TranscriptConstruction)
  -> target Protocol candidate + FSConstructionMaps

independently authenticate and admit the target Protocol

FinalizeFSConstruction(source, target, construction, maps, regime)
  -> qualified CheckedFSConstruction
```

For composed targets, construction formation occurs only after target Core
formation and consumes the exact same-invocation scoped composition authority.
Cold replay reconstructs the Core from the admitted composition spec and
children, mints and consumes a fresh same-invocation scoped authority, admits
the Protocol, and only then finalizes the A/N composition check. Only that
final affirmative composition result may later supply checked-composition
context authority. Separately, only an affirmative checked FS construction may
feed later exact theorem-applicability checking; neither capability proves a
theorem or property by itself, and applicability remains separate from
property-specific transport.

## 6. Semantic Core composition

Composition is a checked construction of a new Core, not graph union. An
identity-bearing `CoreCompositionSpec` contains the target Protocol regime,
ordered child occurrences, sequence-valued occurrence faces, complete origin
and causal provenance, one target-event permutation, total challenge,
private-randomness, failure, and reach policies, an exact terminal combiner,
and the complete local target fragment.

v0 composition requires child and target Core semantics under the same
Protocol regime. Target dependencies are the deterministic least
target-required reachable closure selected from child views plus disjoint
authenticated local supplies; unused child history is dropped. Events,
obligations, obligation failures, and causal edges are recomputed after every
rewrite.

Challenge policy distinguishes independent, joint-member, shared, derived,
and imported cases. Private randomness distinguishes preserved, joint,
derived, and externally supplied cases. Sharing requires exact coactivation;
joint groups have one noncircular base and ordered conditional steps;
substitution removes all stale randomness, failure, obligation, observation,
and owner-basis structure. Failure and reach handling is total. Capture is an
explicit intentional change, is claim-quiescent, suppresses the complete child
suffix, records the exact typed exit tuple, and cannot capture an intrinsic
explicit Protocol abort.

The terminal combiner has an authenticated finite result domain, exact result
and public-output functions, deterministic projections and route order, and a
canonical-true last fallback. Every propagated or captured source resolves
before a final combiner route, and all required child outcomes exist before a
final attempt.

Formation has three authority phases:

1. construct and transactionally subadmit the target Core;
2. form and independently authenticate/admit the Fresh or exact composed-FS
   target Protocol; and
3. compare the admitted target with the spec and children.

No caller-supplied provisional map record crosses these phases. Final
comparison is total and returns either
`Affirmative(ResolvedCoreCompositionMaps)` or a negative payload with nonempty
typed mismatches and unaffected agreements. Only the affirmative result keeps
resolved maps or grants composition-context authority. A negative result is a
real checked conclusion but cannot authorize construction use.

## 7. Authority, outcomes, and persistence

Every identity-bearing subject follows the same local pattern:

```text
candidate
  -> physical and dependency authentication
  -> domain admission
  -> opaque immutable process-local capability
```

Canonical PIR authentication performs structural checks, exposes only a
diagnostic unauthoritative read, authenticates exact dependency preimages,
recomputes Core/construction/Protocol IDs, establishes graph/ID consistency,
and only then exposes the authoritative bijective read. Protocol admission
uses exact retained dependency views, composition-context authority, and
branch-specific Core/transcript law-checker capabilities. Core authority is a
transaction witness during Protocol admission and an attenuated view
afterward, never a separately persisted official root.

Each satellite repeats the exact authentication, dependency, and admission
path its owner requires. A checked relation instead consumes already admitted
operands; an operation that executes a referenced algorithm also requires an
identity- and ABI-matched execution capability. Every durable consumer has an
owner-specific cold-replay path. IDs, bytes, signatures, stored results,
audits, package membership, provenance, and matching digests cannot launder a
live capability. Serialization or process reset requires replay from raw
material.

Owner outcomes distinguish:

```text
Affirmative
Negative(retained exact facts)
Unsupported
CannotAnswer
Refused
Malformed
DeterministicLimitExceeded
CheckerFailure
```

Only completed affirmative or negative checks mint their exact `Checked*`
capability. Unsupported questions, missing semantic basis, missing authority,
malformed input, and operational failure mint none. Affirmative-only consumers
must receive the affirmative variant rather than merely a completed check.

## 8. Why this model is selected

The historical Stage 3 package-selection decision passed four independent
design gates: target
type/operation/authority closure, equal-resolution five-candidate and IR-case
comparison, named-scenario falsification, and cross-cutting identity,
dependency, authority, outcome, and persistence matrices. Those gates closed
the architecture comparison at that package's declared design resolution.
They did not establish K1 alignment or integrated semantic-kernel closure, and
they are not implementation, mechanization, or cryptographic evidence.

This topology is the only compared center that satisfies the fixed Stage 1 and
Stage 2 boundaries without turning its principal risk into a permanent global
discipline:

- within that historical comparison, the semantic center was judged small
  enough for clean-room interpretation and complete enough to preserve every
  verifier-visible and refusal-sensitive distinction;
- physical canonicality has one carrier and one owner, while meaning remains
  independent of MLIR implementation details;
- Interface, Plan, Relations, transcript construction, and composition evolve
  under their own identities and authorities without changing Protocol
  meaning by co-location;
- exact structural maps survive for later consumers without pre-approving
  satisfaction, security, compiler, or endpoint conclusions;
- several formal models and authoring languages can target one closed subject
  without becoming competing production authorities; and
- complexity is visible at typed seams, dependency manifests, and narrow
  checks instead of hiding in a representative quotient, package convention,
  ambient registry, or universal handler.

The decisive factor is ownership, not document size or packaging convenience.
These subjects have different substitution laws, identity pressures, refusal
conditions, and consumers. A transport package may carry several of them; it
does not create a shared semantic root or transitive authority.

## 9. Capabilities enabled

The selected architecture enables, without strengthening their claims:

1. independent executable or formal interpretations of one specified Core
   algebra while MLIR remains the production carrier;
2. multiple Interfaces and Plans over one stable Protocol;
3. several Fresh or Fiat--Shamir Protocols over one Core with exact
   event/challenge/prefix maps;
4. late relation artifacts and honest negative disagreement without confusing
   interpretation failure, missing basis, or relation satisfaction;
5. repeated-child, bounded-branching, early-exit, shared/joint/substituted-
   randomness composition without graph-union ambiguity;
6. identical intrinsic target identity reached through distinct normalization,
   FS, or composition histories while checked maps and provenance remain
   separate;
7. narrow Analysis, Compiler, OIR, and Realization readers that can refuse an
   omitted basis instead of reconstructing a shadow Protocol; and
8. future generative modules that elaborate to closed ordinary subjects and
   disappear before admission.

## 10. Costs and required discipline

The decision accepts these costs deliberately:

| Cost | Required discipline |
|---|---|
| More subject, regime, dependency, and checked-result IDs | Use typed references, exact manifests, and owner-specific admission; do not replace them with strings or one package ID |
| More assembly at API boundaries | Keep packages transport-only and authenticate/admit every consumed member independently |
| A demanding authoring-to-canonical boundary | Produce exact satellites and a pre-erasure audit; explain refusal before information is lost |
| A complete semantic and carrier conformance burden | Maintain one production carrier and test its bijection with the language-independent model |
| Large occurrence, FS, and composition maps | Derive and directly compare maps; never accept proposed or serialized authority-bearing maps |
| Process-local authority and cold replay | Reauthenticate dependencies and recompute checked relations after serialization or reset |
| Explicit qualified outcomes | Preserve negative truth, unsupportedness, missing basis, refusal, malformedness, and operational failure as different states |
| Delayed convenience | Keep security, satisfaction, compiler, OIR, and runtime conclusions unavailable until their exact later owner supplies the missing basis |

These are specification and trust-surface costs, not evidence of implementation
effort already completed.

## 11. Alternative dispositions

### 11.1 Rich admitted carrier plus semantic quotient

The rich-quotient alternative remains the current-preserving reopening
control. It authenticates and admits an exact rich physical representative,
then gives meaning and identity through a canonical semantic projection.
Several different admitted carriers may share one `ProtocolId`.

It is rejected as the v0 center because every consumer must maintain a
complete representative read set and prove that projection or pre-erasure
normalization preserves every refusal-sensitive distinction. It may be
reconsidered only by formally reopening the one-physical-carrier decision and
demonstrating that this lifetime quotient burden is lower than the selected
closed-carrier burden.

### 11.2 Canonical multi-subject bundle

The bundle alternative gives reusable non-occurrence subjects one additional
canonical package while retaining member IDs and admissions. Occurrence-local
private witnesses, artifact bytes, and artifact observations remain outside
the authoritative package.

It is rejected as a semantic center because no named consumer justifies a
normative package root, package closure risks apparent transitive authority,
and unrelated member evolution creates compatibility churn. A bundle may
remain a non-authoritative transport convenience.

### 11.3 Typed event calculus as the center

The event-calculus alternative contributes finite typed effects, explicit
inputs, and mechanizable transition rules. Those techniques are adopted inside
Core.

The universal center is rejected because domain-owned claims, Interface,
Plan, Relations, FS, and composition would become encodings inside one handler
framework. It remains an alternate research direction only if a complete
finite syntax, total normalizer, decidable equality, and executable
owner-specific simulations become materially smaller and clearer than the
selected direct objects.

### 11.4 Generative protocol modules

The module alternative is retained as optional authoring research. A module
may parameterize relations, dependencies, transcript construction, and
composition, then deterministically elaborate a closed selected-model subject.

The module, assignment, and elaborator are not Protocol meaning and cannot be
required by ordinary interpretation or admission. Termination, parameter and
variance closure, exact elaborator auditing, and refusal diagnostics remain
open obligations before such an authoring layer can be selected.

## 12. Reversal triggers

This decision must be reopened if concrete evidence establishes any of the
following:

1. A required bounded interactive protocol cannot be represented without an
   ambient semantic read or moving verifier behavior into a satellite or host
   handler.
2. Core becomes a general optimizing language or its admission checker must
   import most authoring, compiler, plugin, or backend machinery.
3. Two legal canonical PIR graphs under one regime share a semantic encoding
   beyond the explicitly allowed carrier trivia, or canonicalization must
   erase a required refusal-sensitive distinction before it can be checked.
4. A named independent full-Protocol consumer needs a complete non-MLIR
   production package under an explicit trust, retention, and compatibility
   contract that narrow views cannot satisfy.
5. Interface or Plan substitution changes a result declared to depend only on
   `ProtocolId`, or their producer and consumer read sets cannot be closed.
6. Relation correspondence cannot be expressed over admitted Protocol and
   Interface views without redefining a Protocol-owned fact or importing
   hidden relation-owner authority.
7. Typed satellite admission creates an unavoidable authority cycle.
8. A credible composition case cannot close every target family, dependency,
   schedule, randomness policy, failure, obligation, terminal, or challenge
   interpretation under the selected exact construction.
9. A finite event calculus gives a materially smaller, complete, and more
   reviewable account of every selected domain subject without ambient
   authority or normalization ambiguity.
10. A named whole-package consumer demonstrates lower total cost with no
    authority transitivity or irrelevant compatibility debt.
11. Purpose-specific views collectively recreate a complete second Protocol
    schema and erase the benefit of the one-carrier boundary.
12. A Stage 4 reader supplies an exact counterexample showing that the Stage 3
    view omits a semantic input it genuinely requires.

A trigger starts an explicit review. It does not authorize an ambient
exception, generic metadata escape hatch, widened `valid` result, or silent
compatibility promise.

## 13. Stage 4 split and handoff

Stage 4 is split into two coordinated branches. This Stage 3 decision activated
neither branch. Stage 4A was subsequently activated and completed its bounded
package through the
[Selected Analysis and Compiler Architecture](analysis-and-compiler-architecture.md);
Stage 4B remains unactivated. Each branch consumes the same admitted Stage 3
subjects and preserves the selected ownership and noninterference rules.

### 13.1 Stage 4A: Analysis, then Compiler

Analysis owns semantic questions, properties, assumptions, models, theorem
bases, derivations, and judgments. The Stage 4A package candidate defines:

- equivalence, refinement, intentional change, distributional, and property
  questions over exact admitted views;
- exact theorem- or model-applicability and property-specific transport
  relations, kept separate from theorem truth and source-property authority;
- consumption of exact Relations-owned occurrence-local satisfaction results
  inside family-specific property judgments, without redefining or widening
  satisfaction; and
- the exact identity, replay, residual trust, and portability of derivations
  and judgments.

Relations owns the base `RelationSatisfies` meaning, occurrence-local witness
binding, and qualified satisfaction result. Compiler then owns predecessor/
successor relations, transform-family authority, proposal and selection roles,
legality, preservation, objectives, and replay. Compiler policy cannot become
property meaning, and a constructed target must be independently authenticated
and admitted before a checked source-to-target relation is issued.

Stage 4A receives no pre-approved theorem: Stage 3 exports exact subjects,
observers, regimes, maps, structural results, and qualified signatures only.

### 13.2 Bounded K3-D OIR seam, then Stage 4B

K3-D now gives OIR a minimum target-semantic endpoint body, local admission,
source-relative projection, and identity split. It:

- consumes affirmative PIR-owned purpose views over exact admitted sources;
- distinguish standalone `LocalOirValid` from source-relative
  `ProjectionCorrect` and coverage;
- derives exact static endpoint obligations and retains their source action and
  anchored claim/reduction laws while deferring dynamic execution to Stage 4B;
- identifies endpoint semantics independently from whole source provenance;
  and
- supports only FS verifier and Plan-specialized prover endpoints over the
  bounded base effect/recipe profile, with explicit unsupported rows.

Full Stage 4B must still select concrete OIR syntax and complete execution,
optimization, Fresh/Oracle/module/generic-prover profiles, and preservation
interfaces before Realization activates.

Realization follows with suppliers, target artifacts, behavioral
correspondence or refinement, deployment, invocation, sessions, results,
resources, and operational refusal. Concrete suppliers and live runtime
capabilities cannot flow backward and change OIR or Protocol meaning.

Neither K3-D nor Stage 4B receives a pre-approved endpoint or implementation claim. Stage 3
exports admitted source subjects, exact endpoint/prover obligations, failure
and occurrence structure, Plan constraints, and explicit judgment signatures.

### 13.3 Cross-branch checkpoint

Stage 4A performed this package checkpoint against the dormant Stage 4B
boundary and retained a candidate handoff contract rather than inventing OIR
facts. Before Stage 4B closes, its selected design must reconcile the same
items against the then-frozen Stage 4A package output and any changes accepted
by integrated revalidation:

- protected observations and effect classes;
- Protocol, Interface, Plan, successor, and OIR identity dependencies;
- property-transport and projection-correctness assumptions;
- verifier-visible order, challenge, and transcript behavior; and
- every field treated as semantic by one branch and configuration or runtime
  state by the other.

Neither branch may repair a missing Stage 3 input through ambient state. A real
counterexample returns to the reversal process in Section 12.

## 14. Exact non-claims

This decision does **not** establish or promise:

- activation of Stage 4B, any claim that this Stage 3 decision itself activated
  Stage 4A, or permission to skip a branch's separate activation decision and
  entry contract;
- normative authority before explicit documentation and specification
  cutover;
- implementation correspondence, feasibility, completeness, performance, or
  current code support;
- an implementation sequence, migration plan, compatibility window, cost
  estimate, or identity preservation across semantic regimes;
- concrete MLIR operation spelling, byte grammar, hash primitive, serializer,
  checker API, or test vectors;
- representability of every existing or future proof protocol;
- relation truth, satisfiability, witness validity, or relation satisfaction
  from a reference, binding, artifact, observation, or admitted Protocol;
- soundness, knowledge soundness, completeness, zero knowledge,
  non-malleability, Fiat--Shamir security, or a quantitative bound;
- that structural composition preserves a property, is associative or
  commutative, or commutes with Fiat--Shamir;
- compiler preservation, legality, optimality, backend correctness, OIR
  validity, projection correctness, endpoint support, provider correctness,
  deployment success, or runtime availability;
- prover termination, honest-prover success, secrecy, cost, or proof
  production from Plan admission or `PlanRealizes`;
- adequacy or authority of any external formal model, theorem, proof assistant,
  transcript implementation, or surveyed system;
- portable authority, reliance, or truth from persisted results, signatures,
  provenance, evidence, package membership, or matching digests; or
- selection of a universal transition language, compatibility dialect,
  canonical multi-subject bundle, generic fact root, checker registry,
  certificate envelope, or admitted module language.

## 15. Relationship to durable architecture

This page refines, and does not replace, the
[Protocol IR Architecture](protocol-ir-architecture.md): that decision owns the
language-independent meaning, canonical MLIR level, identity, and satellite
factorization selected in Stage 1.

The [Transition and Bridge Architecture](transition-and-bridge-architecture.md)
owns the shared authentication/admission distinction, narrow capabilities,
qualified outcomes, target-independent construction ordering, replay, and
persistence rules selected in Stage 2.

The [v0 Semantic Design Program](v0-design-program.md) owns the cross-stage
sequence and the coordinated Stage 4A and Stage 4B research program. Exact
future Stage 4 and later schemas, and all eventual normative rules, belong with
their domain owners under `pir/`, `relations/`, `analysis/`, `compiler/`,
`oir/`, and `realization/`.

The reconciled candidate is split across exact durable owners:

- [Interactive Core](../pir/interactive-core.md) owns active Core, Protocol,
  execution, failure, claim/reduction, Oracle, and admitted-view semantics;
- [Fiat--Shamir Construction](../pir/fiat-shamir.md) owns the active
  challenge-interpretation and static construction views;
- [Canonical PIR](../pir/canonical-pir.md) owns the closed MLIR profile,
  semantic/carrier bijection, authentication, admission, and replay;
- [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md) owns
  the two dependent satellites and `PlanRealizes`;
- [Endpoint Projection Views](../pir/endpoint-projection-views.md) owns the
  bounded OIR-purpose source quotients and checked extraction;
- [Relation Model](../relations/relation-model.md) owns relation subjects,
  artifact ingress, binding, grounding, and the satisfaction boundary; and
- [Protocol Correspondence](../relations/protocol-correspondence.md) owns
  structural and instance correspondence questions, results, and replay.

This page owns the durable high-level Stage 3 decision: the integrated
Protocol/Relations topology, why it was selected, its accepted costs and
capabilities, alternative dispositions, reversal triggers, non-claims, and
Stage 4 handoff.
