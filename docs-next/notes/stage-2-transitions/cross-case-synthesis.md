# Stage 2 cross-case synthesis

> **Document kind:** Temporary integrative research note
> **Document state:** Convergent synthesis recommendation; not ratified
> **Authority:** None. This page compares reconstructed current behavior,
> external mechanisms, and clean-sheet candidates. It recommends a target
> architecture for Stage 2 convergence, but it does not define a normative
> transition, mint authority, select a wire format, authorize implementation,
> or begin Stage 3.
> **Inputs:** The selected
> [Stage 1 Protocol architecture](../../project/protocol-ir-architecture.md),
> [current transition catalog](current-transition-catalog.md),
> [lifecycle spine](lifecycle-spine.md),
> [semantic-bridge dossier](semantic-bridges.md),
> [endpoint and operational-bridge dossier](endpoint-operational-bridges.md),
> [external-case dossier](cases/transition-and-checking-models.md), and
> [equal-resolution candidate portfolio](candidate-frameworks.md).
> **Disposition:** Use as an input to the target catalog, scenario evaluation,
> and convergence review. Promote only reviewed conclusions into durable
> domain owners, then delete this page with the Stage 2 package.

## 1. Synthesis result

The strongest coherent target is a **disciplined hybrid**, not one global
transition algebra:

```text
project-wide descriptive contract schema and invariants
        |
        +--> capability-centric Protocol and local-authority lifecycle
        |
        +--> domain-owned semantic subjects, relations, and judgments
        |
        +--> direct recomputation for small closed predicates
        |
        +--> proposal + relation-specific validator for search-heavy edges
        |
        +--> explicit trusted boundary when no smaller checker exists
        |
        `--> purpose-specific durable result only for a named consumer

effectful operations
        -> typed occurrences and observations
        -> evidence records
        -> policy-qualified appraisal
        -> use-specific reliance
```

In candidate terms:

- Candidate A supplies the global ownership model: concrete contracts remain
  with their semantic domains, while the project owns a common review schema
  and cross-cutting invariants.
- Candidate C supplies the in-process lifecycle model: successful
  authentication, admission, projection, binding, and operation gates mint
  narrow capabilities whose authority does not survive serialization.
- Candidate D supplies a selective checking strategy: a complex producer may
  propose a result, but only a relation-specific validator can authorize that
  edge when checking is genuinely smaller and independently specified.
- Direct recomputation remains preferable to either a validator protocol or a
  certificate for small deterministic predicates.
- Effectful operations and policy decisions remain typed domain events. They
  are not forced into the pure checked-relation model.
- Candidate B's universal runtime algebra and transition artifact are not the
  v0 default. They remain a reversal option if a real uniform consumer and
  genuinely shared composition laws appear.

Candidate letters on this page refer only to the Stage 2 transition-framework
portfolio. They are unrelated to candidate letters used during the completed
Stage 1 IR comparison.

The hybrid is not “use a different mechanism whenever convenient.” It is
governed by one positive mechanism-selection rule in Section 7. Every edge
must first expose the same authority, closure, identity, outcome, replay, and
composition questions. The answers, not the directory or current API shape,
choose the mechanism.

## 2. Evidence and recommendation discipline

This synthesis keeps five epistemic classes distinct.

### 2.1 Fixed Stage 1 decisions

The following are selected architecture inputs, not Stage 2 discoveries:

- Protocol meaning is language-independent; MLIR is the primary v0
  structural carrier.
- A rich authoring workbench is separated from a small closed canonical PIR
  level.
- `Protocol = InteractiveCore + ChallengeInterpretation`.
- `InteractiveCore` owns one total observable schedule.
- Fresh-public-coin and Fiat--Shamir interpretations produce different
  Protocols related by theorem-backed `FSCompile`.
- `ProtocolInterface` and `ProverPlan` are separately identified dependent
  subjects over one exact `ProtocolId`.
- semantic regimes are typed and identity-bearing;
- admitted authority is opaque, immutable, and process-local;
- purpose-specific views are preferred to a universal fact root;
- protected observations and named relation families are
  noninterchangeable; and
- source-free OIR cannot establish omitted source coverage by inspection of
  the target alone.

Stage 2 may decide how transitions establish and carry claims over those
subjects. It may not move fields or authority across those subject boundaries
by choosing a convenient checker representation.

### 2.2 External source facts

The external cases establish the following mechanisms within their own
scopes:

| Source fact | Mechanism demonstrated | Transfer limit |
|---|---|---|
| [CompCert](https://compcert.org/doc/) proves preservation for specified source and target semantics and accepted compiler executions | A checked-change claim is meaningful only after its observable behaviors, direction, assumptions, and accepted domain are exact | It does not define interactive-protocol, cryptographic, probabilistic, or zkc-specific relations |
| [Alive2](https://users.cs.utah.edu/~regehr/alive2-pldi21.pdf) checks bounded refinement for individual LLVM transformations and exposes unsupported or bounded cases | Producer search can be separated from per-result checking; incompleteness must remain visible | Its LLVM refinement relation cannot be reused as Protocol equivalence or `FSCompile` |
| [Proof-carrying code](https://doi.org/10.1145/263699.263712) and [LRAT](https://www.cs.cmu.edu/~mheule/publications/lrat.pdf) attach checkable evidence to a precise claim | An expensive producer can be outside the trusted boundary when a smaller checker and exact witness exist | A certificate is useful only for the property and checker it encodes; it does not establish source/target correspondence automatically |
| [MLIR dialect conversion](https://mlir.llvm.org/docs/DialectConversion/) establishes legality relative to a configured target; the [Transform dialect](https://mlir.llvm.org/docs/Dialects/Transform/) orchestrates transformations and failure propagation | MLIR can enforce structural closure and organize producers | Legality, handle validity, and pass success do not establish a zkc semantic relation |
| [Capsicum](https://www.cl.cam.ac.uk/research/security/capsicum/papers/2010usenix-security-capsicum-website.pdf) and [WebAssembly resources](https://github.com/WebAssembly/component-model/blob/main/design/mvp/WIT.md) make authority dependent on scoped, live handles | Local authority should be carried by unforgeable, attenuated capabilities with explicit lifetime rules | Kernel or runtime handles do not define zkc semantic identity or cross-process authority |
| [CBOR deterministic encoding](https://www.rfc-editor.org/rfc/rfc8949.html), [OCI descriptors](https://github.com/opencontainers/image-spec/blob/main/descriptor.md), and [StableHLO compatibility](https://github.com/openxla/stablehlo/blob/main/docs/compatibility.md) separate encoding, byte binding, and a maintained compatibility promise | A durable format requires an application profile, consumer, version policy, and tests | A digest, decoder, or wire-compatible schema does not establish semantic admission |
| [W3C PROV](https://www.w3.org/TR/prov-dm/), [in-toto validation](https://github.com/in-toto/attestation/blob/main/docs/validation.md), and [IETF RATS](https://www.rfc-editor.org/rfc/rfc9334.html) separate lineage, authenticated statements, appraisal, and relying decisions | Evidence and policy form a chain of differently owned claims | Authenticated provenance does not prove the predicate, and appraisal does not authorize every consumer |

These are source facts and narrow transfers. None establishes that zkc's
current implementation has the proposed target property, and no external
architecture is adopted wholesale.

### 2.3 Current-repository observations

The reconstruction dossiers support these bounded observations about the
current checkout:

1. The current artifact lifecycle already distinguishes decoded from admitted
   PIR and requires re-admission after persistence. Opaque immutable handles
   are therefore an implemented correspondence pattern, not merely a target
   metaphor.
2. Current seal combines logical resolution, identity construction, semantic
   checks, and carrier-state change in one operation. A logical split can be
   specified without requiring four implementation traversals.
3. The current admitted artifact retains a complete
   `ProtocolEnvironment`, although Protocol identity closes over only the
   cited subset. Later consumers can therefore obtain more provider context
   than the target minimal-closure rule permits.
4. Static link returns a new raw Open PIR that must be sealed normally. Child
   admission is not inherited by the composite.
5. The compiler path already reopens, transforms, reseals, re-admits, and
   replay-checks a successor. Its replay shares the producer-side semantics
   and configured authorities, so it is useful validation but not evidence of
   an independent checker.
6. Current relation correspondence, Analysis derivations, compiler checks,
   and OIR projection already establish different result classes. They do not
   form one latent universal relation.
7. Relation correspondence and OIR projection currently read carrier labels
   that Protocol identity intentionally erases. The Stage 1
   `ProtocolInterface` boundary is needed to close those target contracts.
8. `ProjectedOirArtifact` retains source and target together in process,
   whereas standalone OIR admission establishes only target-local facts. This
   is an implemented example of paired source-relative authority degrading at
   serialization.
9. Execution profiles and emitter bindings currently close supplier choices
   for bounded paths, but there is no admitted general supplier-binding,
   realization, deployment, invocation-binding, evidence-appraisal, or
   reliance architecture implemented end to end.
10. Current tests and replays are correspondence evidence for their named
    paths. They do not turn structural admission into soundness, a checked
    successor into universal preservation, or one run into realization or
    reliance evidence.

These observations constrain migration analysis later. They are not reasons
to preserve a current API, hidden read, or fused transition in the ideal
model.

### 2.4 Cross-case inferences

The following are deductions from the fixed architecture, external cases,
and local reconstruction. They are not direct source facts:

1. Similar metadata does not imply shared semantics. Every edge needs source
   and target references, a regime, outcomes, and provenance, yet the meaning
   of `Admit`, `ProjectionCorrect`, an invocation result, and a reliance
   decision is fundamentally different.
2. The strongest useful common layer is therefore initially descriptive and
   invariant-enforcing, not a universal semantic executor or wire object.
3. Local capabilities and durable claims solve different problems. A
   capability authorizes a bounded operation in one authority domain; a
   durable result lets a consumer recheck or appraise a claim. Neither is a
   portable substitute for the other.
4. Proposal/check separation is valuable only when the relation checker is
   sound, closed over exact inputs, and materially smaller or more stable than
   the producer. Merely running the producer twice is reproducibility, not an
   independent trust reduction.
5. Pure semantic transitions, effectful occurrences, evidence appraisal, and
   reliance require different composition and replay rules. A framework that
   unifies them as arrows must reintroduce those differences as exceptions.
6. A universal transition artifact would make unresolved Stage 3--6 relation,
   policy, effect, and compatibility choices into one early product promise.
   The present consumer evidence does not justify that cost.
7. Exact closure is the common correctness condition that can be shared
   without centralizing relation semantics: if an undeclared value can change
   a normative result, the contract is incomplete.

### 2.5 Stage 2 recommendations

Sections 3--14 state the recommended synthesis. They are candidates for
convergence, not ratified specifications. The later convergence document must
either accept them after scenario review or record the exact counterevidence
and replacement.

## 3. Strongest candidates and hybrids

### 3.1 Candidate A as a global baseline

Candidate A is the strongest global default because it localizes semantic
authority without preventing shared tooling:

```text
project owns:
  descriptive contract vocabulary
  catalog completeness
  closure, no-backflow, and capability-loss invariants
  cross-domain review and lint rules

domain or bridge owner owns:
  subject meaning and identity
  exact relation and observer contract
  checker, refusal, and diagnostic semantics
  capability lifetime and consumer adequacy
```

Its main weakness is drift: separately owned contracts may use inconsistent
regime, outcome, closure, or identity conventions. The answer is a lintable
contract projection and cross-owner review, not immediate promotion to a
universal runtime object.

### 3.2 Candidate B in its strongest form

The strongest form of Candidate B is an indexed algebra whose subject and
relation kinds remain domain-defined and whose composition requires
registered laws. It can provide uniform graph inspection, orchestration, and
portable replay.

Even in that strongest form, it is not selected for v0:

- most important relation pairs have no demonstrated common composition law;
- operational effects and policy-qualified decisions require a separate
  fragment rather than ordinary pure arrows;
- portable form fixes subject-reference, relation, outcome, checker, witness,
  provenance, and evolution schemas before their owners stabilize;
- in-process form avoids the wire cost but loses much of the claimed portable
  replay benefit; and
- no current independent consumer requires a universal transition DAG rather
  than exact domain results.

Candidate B remains a legitimate future architecture, not a rejected idea in
all circumstances. Section 14 states the evidence that would reopen it.

### 3.3 Candidate C as the lifecycle spine

Candidate C best models authority state across authoring, authentication,
admission, views, projection, supplier binding, deployment, and invocation.
Its advantages are concrete:

- construction control can prevent raw carriers or copied flags from entering
  admitted consumer APIs;
- mutation, FFI, persistence, and process boundaries have an explicit
  authority-loss rule;
- immutable handles can retain the exact checked basis needed for safe local
  use; and
- authority can be narrowed to one source/target pair or one operation.

It is not a complete global model. Capabilities do not by themselves define a
mathematical relation, portable evidence, an operational occurrence, or a
consumer's reliance rule. Unbounded capability proliferation and hidden
retained environments are real failure modes. Candidate C is therefore
selected for local authority, not for all transition semantics.

### 3.4 Candidate D as a selective checking strategy

Candidate D is strongest for edges where production involves search,
optimization, synthesis, target tooling, or a volatile algorithm and a
smaller stable checker can validate the exact result. Its natural target
families are:

- nontrivial canonical normalization with optional source correspondence;
- checked Protocol transformation;
- projection with an exact source map and coverage witness;
- ProverPlan realization;
- property derivation with an explicit plan; and
- target realization when a practical independent checker exists.

It is not a sensible default for every edge. Admission and small schema
checks are better recomputed. Invocation is an effectful occurrence, not a
candidate relation that a witness can replay. A validator that duplicates the
producer does not reduce trust and should not be marketed as independent.

### 3.5 Disciplined hybrid comparison

| Architecture | What it gets right | Remaining failure | Synthesis verdict |
|---|---|---|---|
| A alone | Exact domain ownership and low wire commitment | Weak local authority enforcement; checking and persistence chosen ad hoc | Necessary baseline, insufficient alone |
| B alone | Uniform graph, orchestration, and potential portable replay | Central schema and false common algebra; premature wire promise | Not selected for v0 |
| C alone | Strong local least authority and explicit serialization loss | Does not define durable judgments, mathematical relations, or policy | Selected lifecycle component only |
| D alone | Separates complex producers from edge-specific authority | Validator and certificate proliferation; poor fit for effects and cheap checks | Selected per-edge strategy only |
| A + C | Domain semantics plus strong local authority | Does not choose when independent validation or persistence is justified | Strong but incomplete hybrid |
| A + D | Domain semantics plus scalable untrusted production | Does not prevent capability laundering or model live operation authority | Strong but incomplete hybrid |
| B for pure relations + C elsewhere | Uniformity over a smaller subset | No evidence yet that the pure relations share laws or a consumer; still centralizes unresolved schemas | Deferred research alternative |
| **A + C + selective D + direct checks** | Localized semantics, explicit authority, checker placement by economics and claim structure, low default wire pressure | Requires disciplined catalog/linting and per-edge review | **Recommended Stage 2 target** |

The recommendation is intentionally asymmetric. Candidate A is the global
ownership baseline. Candidate C applies where local authority exists.
Candidate D applies only after its checker test passes. Direct checks and
effect contracts are first-class alternatives, not degenerate failures to fit
the hybrid.

## 4. Shared invariants versus domain-owned semantics

### 4.1 Shared project invariants

Every selected transition contract should satisfy these shared invariants:

1. **Typed subjects.** Every source, target, and auxiliary semantic subject is
   named by family, identity, and semantic regime.
2. **Complete closure.** Every result-affecting semantic, dependency,
   configuration, target, policy, or runtime input is explicit or immutably
   carried by a typed capability.
3. **Single primary postcondition.** One transition may physically combine
   work, but its logical results do not conflate formation, authentication,
   admission, relation checking, operation, appraisal, or reliance.
4. **Named relation.** “Valid,” “verified,” “lowered,” and “checked” are not
   accepted result meanings without a domain-owned relation or judgment.
5. **Explicit identity effect.** The contract states which identities it
   consumes, preserves, mints, and merely cites as provenance.
6. **Explicit authority effect.** The contract states which capability is
   gained, narrowed, shared, consumed, discarded, or reconstructed.
7. **Protected observations.** A preservation, refinement, or intentional
   change names its observer set and direction.
8. **Typed outcomes.** Successful negative judgments, semantic refutations,
   unsupported cases, inconclusive checks, refusals, operational failures, and
   partial effects remain distinguishable.
9. **Scoped replay.** A replay claim names whether it means recomputation,
   validation, certificate verification, re-admission, observational
   reproduction, or attribution.
10. **Lawful composition only.** Procedural adjacency does not imply
    mathematical composition, Protocol composition, or reliance.
11. **Capability loss at representation boundaries.** Bytes, handles copied
    across FFI without an authority protocol, and mutable clones carry data or
    provenance, not local admitted authority.
12. **No authority backflow.** Target validity, an observation, evidence,
    appraisal, or reliance cannot redefine source semantics or mint an
    upstream capability.
13. **Fail-closed extension.** An unknown meaning-bearing subject, relation,
    regime, witness, or effect kind is unsupported, not an opaque checked
    success.
14. **Consumer-justified persistence.** Every durable result names its actual
    independent consumer, retention need, checker, compatibility commitment,
    and cheaper alternative.

These invariants can be represented in documentation metadata, generated
catalog data, lint rules, and review tooling. Their shared representation is a
projection of concrete contracts. It does not own the contracts' semantic
truth.

### 4.2 Domain-owned semantics

The following remain with the concrete subject, bridge, operational, Evidence,
or relying-policy owner:

- subject formation and semantic identity preimages;
- the exact proposition, relation direction, protected observer set, and
  admissible domain;
- theorem assumptions, quantitative losses, solver bounds, and completeness
  limits;
- relation-specific witness and checker semantics;
- what counts as an affirmative, negative, conditional, quantitative,
  inconclusive, or refuted judgment;
- diagnostic and counterexample structure;
- capability lifetime, aliasing, revocation, consumption, and concurrency;
- effect occurrence, completion, compensation, retry, and partial-failure
  behavior;
- durable result schema and compatibility window, when justified; and
- appraisal adequacy and use-specific reliance policy.

The project layer may require these fields to exist and may reject a contract
that leaves them implicit. It cannot fill them generically.

### 4.3 Shared runtime extraction rule

A common runtime mechanism may be extracted only when at least two concrete
transitions share all of the following:

```text
same semantic role
same authority issuer and lifetime pattern
same outcome and refusal meaning
same replay and serialization behavior
same composition law or explicit lack of one
same relying-consumer need
```

Sharing field names, a hash function, an outer diagnostic envelope, or a
source/target shape is insufficient. An extracted mechanism remains
subordinate to the domain contracts and must fail closed on unknown
meaning-bearing extensions.

## 5. Exact conceptual model

### 5.1 Four layers per transition family

The synthesis standardizes a conceptual separation, not one universal value:

```text
Subject
  immutable meaning and domain identity

Attempt or procedure
  construction, search, interpretation, execution, or policy application

Checked result or observation
  exact named proposition, judgment, target, or occurrence outcome

Authority or reliance
  local permission to consume, or policy-qualified permission to act
```

Examples:

- a normalizer produces a candidate; authentication does not trust its search
  history;
- a compiler proposes a successor; validation establishes one exact
  predecessor/successor relation;
- an emitter produces files; a realization checker, if available, establishes
  one named OIR relation;
- an executor produces a verdict or operational failure and an observation;
  evidence recording does not replay the execution;
- an appraiser evaluates evidence under one policy; a relying consumer makes
  a separate intended-use decision.

### 5.2 Reference vocabulary without a universal fact root

The shared layer may define a typed reference vocabulary sufficient to prevent
category mistakes:

```text
SubjectRef<SubjectFamily, SemanticRegime, SubjectId>
OccurrenceRef<OperationFamily, OccurrenceId>
ContractRef<RelationOrProcedureFamily, ContractRegime>
PolicyRef<PolicyFamily, PolicyId>
```

This notation does not require one serialized generic type. A concrete domain
may use exact native types and expose a safe catalog projection. The reference
vocabulary must never become a universal object from which consumers infer
facts that only the source owner can derive.

### 5.3 Attempt, checked edge, and consumer decision

Three identities and records must not be conflated:

```text
TransitionAttempt
  procedure, inputs, configuration, occurrence, diagnostics, partial effects

CheckedEdge
  exact subjects + exact named relation + checking basis + outcome

RelianceDecision
  consumer + intended use + policy + accepted claim + scope + time
```

Most pure local transitions need no durable form of any of these. When one is
persisted, its owner and identity preimage are chosen for the named consumer.

## 6. Closure and semantic-regime rules

### 6.1 Closure partitions

Every transition partitions its inputs into explicit classes:

| Class | Examples | Required treatment |
|---|---|---|
| Semantic subjects | Protocol, Interface, Plan, OIR, relation interface, judgment | Exact typed subject reference and admitted state where required |
| Semantic dependencies | declaration preimages, contract definitions, construction definitions | Exact content-authenticated closure, not a broad mutable registry |
| Interpretation regimes | Protocol, Interface, Plan, relation, OIR, Analysis, checker regimes | Typed references; changes cannot be silent |
| Procedure configuration | normalization choices, transform application, solver bounds, target, toolchain | Explicit when it can change the result or claimed scope |
| Policy | admission policy distinct from semantics, appraisal policy, intended-use policy | Explicit at the policy-owned transition; excluded upstream |
| Operational snapshot | supplier resolution, deployment state, resources, session, clock when relevant | Bound to the effectful occurrence; never hidden in a pure relation |
| Provenance only | producer release, source path, search trace, human label | Kept outside semantic identity unless the domain proves it changes meaning |

A broad resolver, registry, provider catalog, or theorem database may support
lookup. The result must bind the exact subset actually read. If lookup order
or default choice changes the semantic result, that rule is an identified
input rather than ambient behavior.

### 6.2 Extensional closure law

For a deterministic semantic transition `F`:

```text
same admitted source subjects
+ same declared auxiliary subjects
+ same exact dependency closure
+ same semantic and checker regimes
+ same result-affecting configuration
--------------------------------------------------
= same semantic outcome and result
```

Changing undeclared state may affect diagnostics, timing, allocation, or
resource consumption. It may not affect the normative outcome. A counterexample
means either that an input is missing or that the operation was incorrectly
classified as pure.

For an effectful transition, the same inputs need not reproduce the same world
state or occurrence result. Its contract instead closes over the preflight
snapshot, names nondeterminism and external authority, and records the actual
occurrence and partial effects.

### 6.3 Minimal retained basis

An admitted capability retains only the immutable basis required to justify
its advertised operations. It does not retain a broad environment for future
opportunistic reads. A later consumer that needs additional material receives
that material as an explicit typed input and obtains a result scoped to the
new tuple.

This rule prevents two capabilities over equal `ProtocolId` from appearing
substitutable while silently consulting different registries. If two
admissions use different normative regimes or incompatible dependency
preimages, their capabilities are not interchangeable merely because one
content identifier is equal.

### 6.4 Regime factorization

The target should distinguish at least:

```text
SubjectSemanticRegime
RelationOrJudgmentRegime
CheckerContract or CheckerRegime
CarrierOrTransportSchema
LocalAdmissionPolicy
EvidenceAppraisalPolicy
IntendedUsePolicy
```

These are not one global version. Their rules are:

1. A subject regime determines semantic interpretation and participates in
   subject identity.
2. A relation or judgment regime determines the proposition and its
   parameters; it is an exact checked-result input.
3. A checker contract states how that proposition is established and which
   limits or trusted components remain. An implementation release is
   provenance unless it changes this contract.
4. A carrier or transport schema determines decoding. Decode success does not
   establish subject or relation preservation.
5. A local admission policy may decline use without changing semantic
   admission under the named regime.
6. Appraisal and intended-use policies qualify later decisions and cannot
   enter upstream semantic identity.
7. Cross-regime comparison requires an explicit checked migration,
   correspondence, or intentional-change relation. Identical bytes are not a
   migration proof.
8. Supersession creates a new result or policy decision. It does not rewrite a
   historical semantic fact under its exact old regime.

## 7. Mechanism-selection rule

Every edge should be designed in the following order.

### 7.1 Step 1: name the relied-on proposition

Classify the consumer need before choosing machinery:

```text
representation or authentication
whole-subject admission
target-local property
source/target relation
logical or quantitative judgment
effectful operational occurrence
evidence appraisal
use-specific reliance
```

If two consumers rely on different propositions, they need separate results
even when one procedure can compute both.

### 7.2 Step 2: close the proposition

List exact subjects, regimes, dependency preimages, configurations,
assumptions, observer sets, checker limits, policies, and operational snapshots
that can change the proposition or result. Hidden state must be removed or the
contract reclassified.

### 7.3 Step 3: choose the least committed sound mechanism

Apply these branches in order:

1. **Direct recomputation.** Use when the predicate is deterministic, bounded,
   locally available, and cheap enough at the consumption boundary.
2. **Proposal plus per-result validator.** Use when production is search-heavy
   or volatile and a sound checker is materially smaller, more stable, or
   independently implementable. The proposal and witness remain
   unauthoritative.
3. **Explicit trusted procedure.** Use when no practical smaller checker
   exists. Name the trusted implementation and residual assumptions instead of
   calling a duplicate execution independent validation.
4. **Effect contract plus observation.** Use for I/O, deployment, live
   resources, invocation, recording, or other actions with external effects.
   Preflight checks may be pure; execution remains an occurrence.
5. **Policy application.** Use for appraisal and reliance. It consumes exact
   evidence or assessments and yields a policy-qualified result, not semantic
   truth.

### 7.4 Step 4: choose local authority

Mint a narrow process-local capability only when a later in-process consumer
must rely on a completed check or operate a live resource. The capability
names or retains:

- exact subjects and checked basis;
- permitted operations;
- lifetime and aliasing rules;
- narrowing and consumption behavior;
- concurrency and revocation rules where relevant; and
- what serialization, mutation, or FFI does to authority.

Do not assign a semantic identity to a capability merely to make it storable.
Persist the underlying subject or claim and reconstruct local authority.

### 7.5 Step 5: justify persistence separately

A domain-owned durable result is introduced only if all of the following can
be named:

1. an independent producer/consumer, release, process, trust, cache, or
   retention boundary;
2. a proposition stable enough to serialize;
3. exact subject and auxiliary-input closure;
4. a checker or appraisal procedure available to the consumer;
5. a compatibility and supersession policy;
6. authentication and disclosure requirements; and
7. a reason direct rechecking or a local paired capability is inadequate.

Failure of this test means no durable transition artifact. It does not weaken
the in-process checked result.

### 7.6 Step 6: type outcomes, replay, and composition

The owner maps its concrete results into the conceptual outcome, replay, and
composition models below. A generic envelope may transport that mapping; it
does not replace domain variants.

## 8. Recommended mechanism placement

| Transition family | Recommended primary mechanism | Local authority | Durable posture | Key non-claim |
|---|---|---|---|---|
| Author/import | Proposal construction; optional source-correspondence proposal | None | Source/provenance only if a workflow needs it | Parsing or import does not admit a Protocol |
| Resolve | Direct deterministic closure over an immutable resolver snapshot | Immutable resolved snapshot, not Protocol authority | Optional typed cache; no universal environment object | Resolution is not Protocol admission |
| Normalize | Deterministic or search-producing candidate; authentication independently recomputes target | None for candidate | Optional source-correspondence witness only for a named consumer | Normalizer success is not target admission |
| Authenticate | Direct owner recomputation of canonical form, identity, and dependency closure | `AuthenticatedCanonicalProtocol` | No portable authority receipt by default | Identity match is not whole-Protocol admission |
| Admit | Direct whole-Protocol recomputation under exact regime | `AdmittedProtocol` | Persist subject bytes; re-admit in the receiving process | Admission is not a cryptographic property or local suitability decision |
| Consumer view | Direct scoped derivation over exact subjects | `ConsumerView<Q>` | Promote only a named domain result | A view is not a second Protocol model |
| Reopen/link/compose | Proposal or semantic construction followed by ordinary authentication and admission | Source capabilities remain; output begins raw | Provenance only unless separately justified | Child or predecessor authority is not inherited |
| Relation-interface admission | Direct Relations-owned schema and identity checks | Admitted relation-interface capability | No receipt by default | Interface formation is not relation truth |
| Relation correspondence | Relations-owned pair/tuple checker over exact admitted views | Exact correspondence result or paired capability | Candidate certificate only after consumer confirmation | Correspondence is not witness satisfaction or Protocol equality |
| Property analysis | Search outside an Analysis-owned explicit-plan checker; direct decision procedure where complete and cheap | Checked conditional judgment | Derivation witness is justified when independently replayed | Failure to find a proof is not a negative judgment |
| Checked Protocol transform | Producer proposal, target re-admission, per-result relation validator | `CheckedProtocolStep` over exact predecessor/successor | Process-local by default | A new ID or legality success proves no relation by itself |
| Compiler selection | Direct recomputation of exact domain, constraints, objective, and selection while bounded | Decision result scoped to request | None until an external decision consumer exists | Selected means best only over the declared checked domain |
| FS construction | Deterministic construction of a new Protocol candidate | Ordinary target admission | None by default | Construction is not `FSCompile` or property transport |
| `FSCompile` | Dedicated theorem/model checker over exact fresh and FS Protocols | Exact conditional judgment | Defer certificate until a consumer exists | The result is not generic Protocol equality |
| `PropertyTransport` | Analysis-owned rule and derivation checker | Target judgment plus checked derivation | Same witness rule as property analysis | A transform annotation is not transported truth |
| OIR projection | Producer plus source-relative checker; direct checking may be fused | Paired `ProjectedOirCapability` | No projection artifact without a named source-free consumer | Local OIR validity is not source coverage |
| Standalone OIR admission | Direct local OIR authentication and admission | `AdmittedOir` | OIR artifact persists; re-admit | Source origin and coverage remain unknown |
| Supplier binding | Direct exact designation and compatibility closure | Binding config plus separately admitted provider authority | Binding config may persist; live providers do not | Provider selection is not implementation correctness |
| Realization | Effectful production followed by relation checking where practical; otherwise explicit trusted grade | `AdmittedRealization` | Domain artifact and result only for concrete deployment consumers | Emission success is not `RealizesOir` |
| Deployment/invocation | Preflight binding plus effectful occurrence and observation | Narrow live deployment/invocation capabilities | Configurations and observations may persist; live authority does not | Operational success or failure does not redefine Protocol/OIR semantics |
| Evidence/appraisal/reliance | Domain observation, Evidence-owned record/appraisal, consumer-owned policy decision | No upstream semantic capability | Purpose-specific records and assessments only | Provenance, truth, appraisal, and permission remain distinct |

This table is a mechanism recommendation. Exact signatures and domain schemas
remain with the later owners identified by the Stage 2 charter.

## 9. Outcome model

### 9.1 Conceptual factorization

One global `Result<Verified, Error>` is insufficient. Stage 2 should require
every concrete contract to preserve the following conceptual dimensions where
they apply:

```text
ProcedureStatus:
  Completed | Refused | FailedOperationally | PartialEffectFailure

InputDisposition:
  Formed | Malformed | Unresolved | Unsupported
  | Unauthenticated | Inadmissible | NotApplicable

CheckDisposition:
  Established | Refuted | Inconclusive | NotRun

JudgmentContent:
  Affirmative | Negative | Conditional | Quantitative | NotAJudgment

AuthorityEffect:
  None | ImmutableSnapshot | LocalCapability
  | NarrowedCapability | DurableDomainResult
```

This is a review factorization, not a mandate for one product enum. A domain
may make some combinations impossible by construction and should expose a
smaller exact type.

### 9.2 Required distinctions

- A successfully derived negative property result is `Completed` and
  `Established(Negative)`.
- A correspondence checker finding disagreement may be a successful negative
  judgment, not malformed input.
- A sound incomplete validator unable to establish a true relation is
  `Inconclusive`, not `Refuted`.
- A target-specific projection refusal does not make the source inadmissible.
- A verifier reject is a completed semantic endpoint result; missing supplier
  authority and executor failure are different.
- A prover produces bytes or fails. It does not produce a verifier verdict.
- A partial-effect failure must expose residual effects and retry/cleanup
  boundaries.
- An appraisal may be positive, negative, insufficient, stale, or
  indeterminate; reliance denial is a later successful policy decision.

### 9.3 Outcome stability

Stable top-level variants are part of the contract because consumers branch
on them. Diagnostic text, internal trace shape, and resource statistics may
evolve independently unless a named consumer requires a stable diagnostic
schema. A durable result commits only to the outcome and diagnostic facets its
profile promises.

## 10. Replay and composition model

### 10.1 Replay classes

Every claim of replay must choose exactly one or more of these meanings:

| Replay class | What repeats | What it establishes |
|---|---|---|
| Deterministic recomputation | Same pure procedure under exact inputs | Same result under the declared contract |
| Independent validation | Relation checker over exact proposed subjects and witness | Named relation only, under checker scope |
| Certificate verification | Durable witness under exact checker regime | The certificate's claim, not local capability or reliance |
| Re-authentication and re-admission | Decode subject, reconstruct identity/closure, rerun admission | New process-local authority over the same semantic subject |
| Observational reproduction | Execute another occurrence under a named environment | A new observation, not identity with the prior occurrence |
| Non-replayable attribution | Authenticate a record of an occurrence | Who reported what under which procedure, not reproducibility or truth |

Search traces, optimizer seeds, and producer schedules are usually provenance.
They enter semantic replay only when changing them changes the claimed result
or the consumer explicitly relies on the search procedure itself.

### 10.2 Composition classes

The target recognizes five noninterchangeable forms:

1. **Procedural sequencing:** one result type satisfies the next operation's
   precondition.
2. **Mathematical relation composition:** an explicit domain theorem combines
   exact relations, assumptions, observer maps, and quantitative effects.
3. **Certificate chaining:** checkers establish a conjunction or a separately
   proved composed claim; matching intermediate IDs alone is insufficient.
4. **Protocol composition:** child occurrences plus explicit seams construct a
   new `InteractiveCore`, schedule, dependency closure, and identity.
5. **Operational sequencing:** causal occurrences compose under effect,
   retry, compensation, and partial-failure rules.

Evidence aggregation and reliance are policy operations beyond these five;
they do not create semantic composition by accepting a chain.

### 10.3 No generic transitivity

`RepresentationEq` may be transitive within one exact regime. That does not
imply a general law for:

```text
FSCompile ; ProjectionCorrect
TraceRefines ; PropertyTransport
ProjectionCorrect ; RealizesOir
Observation ; Appraisal ; Reliance
```

Each desired end-to-end statement requires a rule owned by the relevant
domains. Where no rule exists, the system may retain a provenance chain or
conjunction of local claims and must stop there.

## 11. Identity model

### 11.1 Identity-effect vocabulary

Every contract declares one of these effects for each subject:

```text
Consume(id)
Preserve(id)
Mint(domain-owned id)
CiteAsProvenance(id)
NoSemanticIdentity
```

Equal identifiers permit substitution only for consumers covered by that
identity's exact semantic regime and explicit auxiliary inputs. Different IDs
do not prove inequality of behavior; equal IDs do not imply equal Interfaces,
Plans, capabilities, environments, observations, or reliance decisions.

### 11.2 No global `TransitionId`

The recommended v0 architecture has no universal `TransitionId`. Such an ID
would need to choose, globally, whether to include:

- failed attempts and diagnostics;
- producer implementation and search history;
- relation/checker regime;
- witness bytes;
- operational effects and occurrence time;
- appraisal policy; and
- relying consumer context.

Those choices differ by transition family. A common ID would either be
unstable and overcommitted or omit meaning-bearing inputs.

### 11.3 Domain result and occurrence identities

- Immutable semantic subjects use domain-owned content identities.
- A checked relation or derivation receives a durable identity only when its
  owner and consumer require persistence. It commits to the exact subject
  tuple, relation, regime, result, and checking basis promised by its profile.
- Effectful production, deployment, invocation, recording, and appraisal use
  occurrence identities because repeating them creates another event.
- Capabilities normally have no semantic identity. They carry or cite subjects
  and a checked basis within one process or authority domain.
- A certificate, envelope, or signature has its own content or issuer identity
  and cannot replace the identity of the claim's subjects.

### 11.4 Producer independence

A target identity is computed from target meaning, not from producer search
history, heuristic seed, compiler plan, or witness. Those fields are
provenance or checked-edge inputs unless they change the target's canonical
semantics. Several producers and several certificates may therefore converge
on one target subject without merging their attempts or evidence.

## 12. Interface and ProverPlan seams

### 12.1 Shared rule

`ProtocolInterface` and `ProverPlan` are separately authenticated dependent
subjects. A transition consumes either only when changing that subject while
holding every advertised input constant could change its normative result.
Carrier labels, compiler state, and realization configuration may not act as
unidentified substitutes.

### 12.2 Interface implications

- Protocol-level Analysis excludes Interface fields and is reusable across
  Interfaces.
- External relation correspondence consumes exact
  `(ProtocolId, ProtocolInterfaceId, relation subject)` because it maps
  canonical semantic ports into an external statement or relation contract.
- Every endpoint projection consumes an admitted Interface and role.
- External malformed-input, decoding, packaging, and callable-entry claims
  cite the Interface; abstract Protocol acceptance does not.
- Compiler objectives or constraints may cite an Interface explicitly, but a
  resulting Protocol relation cannot hide it as ambient context.

### 12.3 ProverPlan implications

- Plan-independent verifier semantics never read a ProverPlan.
- A plan-sensitive completeness question consumes exact
  `(ProtocolId, ProverPlanId)` plus relation, witness, and supplier assumptions.
- `PlanRealizes` is distinct from plan formation, projection, supplier
  binding, and completeness.
- Prover projection uses a tagged basis:

  ```text
  InterfaceOnly
  InterfaceAndPlan(AdmittedProverPlan)
  ```

- If a plan changes canonical prover OIR, `ProverPlanId` is a projection input
  and enters `OirId`.
- If it only chooses algorithms, schedules, buffers, suppliers, or other
  below-OIR realization facts, OIR remains plan-independent and the plan is an
  explicit input to binding or realization.
- A supposed Plan field that changes proof events, distributions, transcript
  actions, checks, proof ABI, or accepted language is misclassified; it
  belongs to a different Protocol.

### 12.4 Required seam ledger

Stage 3 and Stage 4 co-design should maintain one field-level ledger:

```text
field or obligation
semantic owner
dependent subject identity, if any
earliest transition that reads it
later consumers
protected observations it may affect
whether it changes OIR identity
whether it changes only realization or cost
```

Each field has one earliest semantic reader. Duplicating it as ambient state
above and below OIR creates two competing authorities.

## 13. Portable-artifact posture

### 13.1 Default

The v0 default is:

```text
semantic subject bytes may persist
process-local authority does not persist
cheap checks are recomputed
expensive checked claims remain local unless a named consumer needs exchange
effect observations use their own domain records
no universal transition artifact exists
```

Canonical Protocol persistence therefore carries content, transport schema,
claimed semantic references, and integrity data. A receiving process decodes,
authenticates, and admits again.

### 13.2 Plausible purpose-specific durable results

The current synthesis distinguishes likelihood from decision:

| Result | Posture | Reason |
|---|---|---|
| Property derivation | Strong candidate when independently replayed | It is naturally a proof object with an Analysis-owned checker |
| Relation correspondence | Possible after a real consumer appears | Exact pair/tuple claim is portable, but no wire consumer is yet established |
| Projection certificate | Possible for source-free consumers that need source coverage | Without that consumer, a paired local capability is smaller and safer |
| Checked compiler step | Local by default | Rechecking from exact predecessor/successor is preferable while no exchange boundary exists |
| Compiler selection result | No durable form yet | Current selection can be recomputed over a bounded declared domain |
| Admission receipt | No durable form in v0 | Receiving consumers can rerun bounded admission and must reconstruct local authority anyway |
| Supplier binding configuration | Portable configuration, not live capability | Exact designation can persist; provider handles and availability cannot |
| Realization result | Domain-specific and target-dependent | Persist only with a deployment or independent conformance consumer |
| Observation/Evidence record | Purpose-specific durable domain object | Occurrence attribution and later appraisal are its actual function, not semantic authority |
| Appraisal or reliance result | Persist only under an owned policy profile | Scope, time, verifier, consumer, and supersession are meaning-bearing |

### 13.3 Minimum durable claim discipline

Any selected durable checked result should bind at least:

```text
claim type and relation regime
exact source and target subject references
all meaning-bearing auxiliary subject and dependency references
checker contract and semantically relevant configuration
typed outcome and declared limits
relation-specific witness or receipt, when used
authentication envelope, when attribution is required
freshness or supersession data only when the claim needs it
```

The result's identity authenticates that record. It does not prove the record,
preserve a capability, or authorize reliance. Unknown meaning-bearing fields
or checker regimes fail closed.

### 13.4 Compatibility cost

A durable schema creates a release and retention promise. It therefore needs:

- an owning domain and independent consumers;
- exact version and compatibility rules;
- upgrade, downgrade, refusal, and unknown-field behavior;
- checker availability for the promised window;
- test fixtures across supported releases; and
- an explicit statement of historical bugs, revocation, or supersession
  behavior.

A serialization library or deterministic encoding profile does not supply
those product decisions automatically.

## 14. Reversal and falsification conditions

### 14.1 Reopen the universal-algebra decision when

Candidate B should be reconsidered if all or most of the following become
true:

- a named independent consumer requires a uniform transition DAG across
  multiple domains;
- at least two important relation families share real semantics, authority,
  outcomes, replay, and composition laws rather than merely fields;
- per-domain adapters demonstrably recreate the same executable algebra;
- generic orchestration or cross-process validation cannot be expressed
  safely through descriptive projections;
- the subject, relation, effect, and evolution schemas have stabilized enough
  to support a compatibility promise; and
- an unknown relation can fail closed without making the common layer an
  opaque tagged-union router.

The existence of a pipeline visualizer, provenance viewer, or common JSON
envelope alone is not sufficient.

### 14.2 Reopen the capability-first lifecycle when

- capability constructors depend on undeclared mutable state;
- retained environments make equal advertised inputs yield different
  normative answers;
- handle count or pairwise capability proliferation obscures authority rather
  than narrowing it;
- language, FFI, or process boundaries cannot make loss and reconstruction of
  authority explicit; or
- a named consumer cannot economically reconstruct a required authority from
  persisted subjects and claim-scoped evidence.

The response need not be portable capabilities. It may be a narrower
certificate, remote authority protocol, or redesigned consumer boundary.

### 14.3 Reopen per-edge validation when

- the validator duplicates the producer, full backend, or runtime and is not
  a smaller or more stable trust boundary;
- witnesses require hidden producer state, missing private inputs, or an
  unbounded theorem environment;
- incompleteness cannot be represented without consumers treating
  `Inconclusive` as `Refuted`;
- the proposed relation cannot close over a stable observer and regime model;
  or
- validator proliferation duplicates semantics more than domain ownership can
  control.

In those cases, prefer direct recomputation, a verified stable transformation,
or an explicitly trusted procedure with honest residual trust.

### 14.4 Reopen persistence defaults when

- admission or relation checking becomes unavailable or prohibitively
  expensive for a named independent consumer;
- a long-lived artifact or independent release cycle acquires an explicit
  retention window;
- source-free OIR consumers require source-relative coverage rather than local
  validity;
- property derivations or checked transformations must cross a real trust
  boundary; or
- legal, audit, disclosure, or reproducibility requirements demand durable
  attributable results.

Each trigger justifies a claim-scoped artifact. It does not by itself justify
one universal transition artifact.

### 14.5 Universal falsification probes

The recommended hybrid fails if it permits any of the following:

1. an uncited resolver, policy, provider, theorem, or carrier field changes a
   pure semantic result;
2. equal Protocol identity launders a different Interface, Plan, regime, or
   checker basis into an old result;
3. serialized, reopened, or FFI-crossing data preserves a local capability by
   assertion;
4. structural admission is reported as soundness, target support, projection
   coverage, or reliance;
5. adjacent relation results are composed while dropping assumptions,
   observer sets, bounds, or intentional changes;
6. a negative judgment, unsupported input, inconclusive checker, refusal, and
   operational failure share one semantic result;
7. partial external effects are erased by a pure-arrow abstraction;
8. observation, evidence, appraisal, or reliance flows backward into Protocol
   or OIR authority;
9. a durable schema is introduced without a named reader and compatibility
   promise; or
10. a shared diagnostic or metadata layer becomes the authority for a
    domain-owned relation.

## 15. What the synthesis enables

If adopted, this architecture makes several extensions possible without
creating a shadow Protocol model:

- several authoring languages and normalizers can converge on one canonical
  Protocol boundary;
- heuristic compilers, projectors, planners, and emitters can compete while
  exact validators remain the acceptance boundary where feasible;
- one Protocol can support several Interfaces and several ProverPlans without
  hidden label or plan reads;
- Protocol-level Analysis can be reused while interface-, plan-, and
  realization-sensitive judgments remain separately keyed;
- source-free OIR consumers can operate on locally admitted targets while
  reporting source coverage honestly as unknown;
- several suppliers, realizations, and deployments can vary below one fixed
  endpoint contract;
- durable proof-like results can be added exactly where independent consumers
  emerge, without freezing every transition into one wire schema;
- observation, appraisal, and reliance can support different consumers and
  policies without rewriting semantic history; and
- future formal checkers can target small relation-specific contracts instead
  of importing the full compiler or one universal transition runtime.

These are architectural capabilities, not claims that the corresponding
checkers, artifacts, independent consumers, or formal proofs already exist.

## 16. Inputs to convergence and later owners

### 16.1 Stage 2 convergence should decide

The convergence pass should ratify, revise, or reject these recommendations:

1. Candidate A as the global ownership baseline;
2. Candidate C for process-local lifecycle and live authority;
3. Candidate D only under the per-edge checker test;
4. direct recomputation as the first choice for small closed predicates;
5. effect and policy transitions outside a universal pure-arrow algebra;
6. the shared invariants and extensional closure law;
7. the conceptual outcome, replay, composition, and identity vocabularies;
8. no global `TransitionId` or universal transition artifact in v0;
9. explicit Interface and tagged Plan consumption; and
10. consumer-justified, domain-owned persistence.

The scenario package must test these as one integrated architecture, including
cross-regime input, negative judgments, source-free OIR, alternative
Interfaces and Plans, search-heavy checked change, partial effects, and
policy divergence.

### 16.2 Later owners receive bounded seams

- Stage 3 PIR and Relations receive the lifecycle contracts, exact closure
  invariant, Interface ingress/correspondence seams, relation ownership rule,
  and composition-law requirement.
- Stage 4A Analysis and Compiler receive the property-subject selection rule,
  explicit-plan checking architecture, checked-successor contract, compiler
  domain-selection rule, `FSCompile`, and `PropertyTransport` seams.
- Stage 4B OIR and Realization receive Interface/Plan-closed projection,
  `LocalOirValid` versus `ProjectionCorrect`, supplier-binding separation,
  realization checking, and effect/capability rules.
- Stage 6 Evidence receives the observation-to-record-to-appraisal-to-reliance
  separation and the consumer-justified portable-result discipline.
- Foundation and Project may own the descriptive schema, typed reference
  vocabulary, global invariants, and catalog tooling. They do not own
  domain-relation semantics.

### 16.3 Deliberate non-decisions

This synthesis does not select:

- final operation, API, file, or serialized type names;
- exact canonical PIR, Interface, Plan, OIR, Evidence, or policy schemas;
- a global error enum or generic capability implementation;
- exact relation definitions, proof systems, solvers, theorem bases, or
  quantitative bounds;
- which compiler or realization families have a genuinely smaller checker;
- any certificate encoding, signature scheme, compatibility window, or
  retention policy;
- implementation migration sequence; or
- implementation conformance to the target.

Those questions remain downstream. Deferral does not weaken the recommended
authority, closure, identity, outcome, replay, composition, and no-backflow
rules.

## 17. Bounded conclusion

The cases do not support one universal notion of a successful transition.
They support a common discipline for describing several different things:
formation, authentication, admission, mathematical relation, logical
judgment, effectful occurrence, evidence appraisal, and reliance.

The recommended target preserves that discipline with the smallest durable
commitment:

```text
shared invariants, not shared semantic authority
domain relations, not generic validity
local capabilities, not serialized authority
validators where checking is truly smaller, not everywhere
durable claims for named consumers, not speculative universal records
explicit laws for composition, not adjacency
typed effects and policy, not semantic backflow
```

This recommendation is ready for integrated scenario and adversarial review.
It is not yet the Stage 2 ratification record and does not start Stage 3.
