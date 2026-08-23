# Stage 2 semantic bridge families

> **Document kind:** Temporary Stage 2 research dossier
> **Document state:** Current reconstruction and provisional convergence for
> the assigned bridge families
> **Authority:** None. Current specifications remain authoritative; the Stage 1
> architecture is the fixed design input. Source and tests are correspondence
> evidence, not normative definitions.
> **Scope:** Relation-interface ingress, post-seal relation correspondence,
> Protocol property analysis, checked Protocol transformation and compiler
> selection, `FSCompile`, and `PropertyTransport`.
> **Method:** Static inspection of specifications, implementation, and tests;
> comparison with primary literature; clean-sheet design under the fixed Stage
> 1 subject model. No test was executed in this pass.
> **Disposition:** Reconcile with the other Stage 2 dossiers, promote reviewed
> contracts to `relations/`, `analysis/`, `compiler/`, and `pir/`, then delete
> this page.

## 1. Executive result

These bridges must not collapse into one generic `lower`, `check`, or `valid`
transition. They establish different mathematical relations and mint different
kinds of authority:

```text
RelationInterfaceCandidate
  -- relation-owned admission --> AdmittedRelationInterface

AdmittedRelationInterface + optional relation artifact
  -- exact format interpretation --> RelationArtifactObservation

AdmittedProtocol + exact ProtocolInterface
+ AdmittedRelationInterface + optional RelationArtifactObservation
  -- relation-owned correspondence --> RelationCorrespondenceJudgment

Exact admitted property subject + analysis basis
+ explicit derivation plan and assumptions
  -- analysis --> PropertyJudgment + checked derivation

AdmittedProtocol + explicit transform proposal
+ exact transform definition
  -- per-result validation --> AdmittedProtocol successor
                               + CheckedProtocolStep

Fresh-coin Protocol + TranscriptConstruction
  -- FS instantiation --> Fiat--Shamir Protocol

Fresh-coin Protocol + Fiat--Shamir Protocol
+ exact FS theorem/model basis
  -- theorem-backed checking --> FSCompileJudgment

source PropertyJudgment + checked source/target relation
+ exact property-transport rule
  -- analysis --> target PropertyJudgment + checked derivation
```

The central design choice is a two-dimensional separation:

1. **Subject construction and authentication** establish what exact objects
   exist and which semantic identities they have.
2. **Relation and property judgments** establish only named claims between or
   about those exact objects.

Consequently:

- a relation contract never changes a Protocol;
- a correspondence result never proves relation truth or witness satisfaction;
- a property judgment never changes its subject;
- a checked transform may mint a new `ProtocolId` without transporting any
  property;
- a structurally well-formed Fiat--Shamir Protocol may exist even when no
  theorem-backed `FSCompile` judgment is available; and
- a preservation claim is not property transport until an exact analysis rule
  checks it.

The preferred checker architecture is likewise per bridge, not global:

- direct recomputation for small ingress predicates;
- relation-owned checking for relation correspondence;
- plan-driven proof checking for property analysis;
- producer proposal plus per-result validation for nontrivial Protocol
  transforms;
- direct recomputation of a bounded compiler decision while no external
  decision consumer exists;
- a dedicated theorem-backed checker for `FSCompile`; and
- analysis-owned proof checking for `PropertyTransport`.

Portable receipts are justified only for named replaying consumers. The
property derivation already has such a consumer shape; the other bridges should
remain process-local unless Stage 2 confirms a durable consumer.

## 2. Fixed Stage 1 constraints

This dossier treats the following as inputs, not questions to reopen silently:

1. `Protocol = InteractiveCore + ChallengeInterpretation`.
2. A Core owns one total observable schedule and fresh public-coin challenge
   occurrences.
3. `FreshPublicCoins` and `FiatShamir(TranscriptConstructionId)` identify
   different Protocols over the same Core.
4. `ProtocolInterfaceId` depends on one exact `ProtocolId`; interface-sensitive
   bridges consume it explicitly.
5. `ProverPlanId` separately depends on `ProtocolId`; plan-sensitive property
   questions consume it explicitly.
6. Canonical PIR is a small closed MLIR carrier for one Protocol. An admitted
   Protocol is an opaque process-local capability.
7. Semantic identities are qualified by typed semantic regimes.
8. `RepresentationEq`, `ProtocolEq`, `TraceEq`, `TraceRefines`, distributional
   relations, `FSCompile`, `PropertyTransport`, and `IntentionalChange` are
   distinct relations.
9. A purpose-specific consumer view is derived authority, not a second source
   of Protocol truth.
10. Human labels and carrier metadata cannot be hidden normative bridge inputs.

The durable source is the
[Protocol IR Architecture](../../project/protocol-ir-architecture.md),
especially its subject model, identity algebra, lifecycle, relation taxonomy,
and Stage 2 entry contract. The common review requirements come from the
[Stage 2 charter](../stage-2-transition-and-bridge-charter.md).

Role names introduced below, such as `AdmittedRelationInterface` and
`CheckedProtocolStep`, are contract placeholders. They do not select a public
class, MLIR operation, serialized schema, filesystem location, or final Stage 3
or Stage 4 terminology.

## 3. Current authority and correspondence reconstruction

### 3.1 Normative sources

| Current source | Authority supplied | Important limit under the target model |
|---|---|---|
| [Relations specification](../../../docs/spec/relations.md) | `RelationContract` schema, digest, format profiles, current post-seal correspondence, computed/cross-checked/asserted distinction | Current statement wiring reads sealed artifact labels; target wiring must consume `ProtocolInterfaceId` |
| [Soundness Kernel specification](../../../docs/spec/soundness.md) | Exact property subjects, rule/binding/context model, `RULE_WF`, `APPLY`, `DERIVE`, conditional meaning, independently re-checkable derivations | Current subjects are artifact-qualified and current FS logic analyzes one already sealed artifact; neither is yet the Stage 1 `FSCompile` relation |
| [Compiler Core specification](../../../docs/spec/compiler.md) | `DOMAIN -> REALIZE -> VALID -> SCORE -> SELECT -> DECIDE`, exact transform families, candidate lineage, soundness consumption | Current preservation records are claims, not checked transport; current artifact authority is broader than the final typed regime/read-set model |
| Stage 1 Protocol architecture | Fixed subject identities, interface and plan separation, protected observers, named relations | Leaves these transition signatures, result capabilities, and checker placement to Stage 2 |

The current documents already keep structural admission, conditional property
derivation, compiler legality, correspondence, endpoint validity, and evidence
separate. Stage 2 should preserve that asset while replacing artifact- and
label-specific coupling with the selected subject model.

### 3.2 Current implementation paths

#### Relation ingress and correspondence

The current relation path has two physically distinct parts:

```text
RelationContractRegistry::parse/load
  -> closed schema checks
  -> canonical JSON digest

zkc-relation
  -> load RelationContract
  -> load and admit sealed PIR artifact
  -> build SealedSoundnessView
  -> optionally read relation bytes through R1CS header reader
  -> compare anchors, ABI labels, declared facts, and byte-derived facts
  -> emit computed / cross_checked / disagreed / asserted lists
```

The registry implementation in
[`RelationContractRegistry.cpp`](../../../lib/Registry/RelationContractRegistry.cpp)
checks closed fields, admitted formats, anchor partitions, instance encodings,
witness ports, contiguous correspondence slots, and the contract digest. The
correspondence executable in
[`zkc-relation.cpp`](../../../tools/zkc-relation/zkc-relation.cpp) separately
admits the Protocol artifact, resolves the profile pin, optionally reads bytes,
and evaluates the artifact/contract relation.

This separation is semantically useful even though it is not yet represented
by reusable domain APIs. Contract admission asks whether an interface object is
well formed and identified. Correspondence asks whether several already formed
subjects agree at one exact boundary.

The current executable also demonstrates a valuable three-way outcome
discipline:

- exit `0`: the correspondence question was answered affirmatively;
- exit `1`: the subject was examined and the answer was negative, with all
  agreements and disagreements retained; and
- exit `2`: the invocation did not reach a judgment.

That distinction should survive as typed semantic results rather than remain a
tool-only exit-code convention.

#### Property analysis

The PIR adapter
[`buildSealedSoundnessView`](../../../include/zkc/Soundness/PirSoundnessAdapter.h)
accepts only an admitted PIR artifact and produces an owned MLIR-free
`SealedSoundnessView`. The representation-neutral Soundness Kernel then checks
an explicit plan against an immutable context. The compiler reaches the same
kernel through its exact artifact-semantics authority rather than implementing
a second property evaluator.

The current architecture therefore already contains the right authority
shape:

```text
admitted source capability
  -> source-owned authenticated projection
  -> analysis-owned rule interpreter
  -> owned derivation result
```

The future change is in the exact subject vocabulary and projection closure,
not in moving analysis into PIR or Compiler.

#### Checked Protocol transformation

The generic compiler receives an immutable payload plus an exact
`ArtifactSemantics` authority. That authority constructs an
`AuthenticatedCompilerArtifact`; callers cannot populate its observations.
Each `TransformFamily` separates `recognize`, `realize`, and `check`. The PIR
KZG family reopens an admitted artifact as unauthoritative mutable PIR,
constructs a successor, reseals it, snapshots and re-admits it, then checks a
deterministic replay and derives claim correspondences. The generic compiler
authenticates every successor before the next step consumes it.

`checkDecision` reruns compilation and compares the submitted selection rather
than trusting candidate validity, loss, score, or eligibility. This is a
checked-search boundary, but it is not implementation independence: current
realization and checking share semantic implementations and the same configured
environment.

#### Current Fiat--Shamir analysis

The current Soundness Kernel admits a
`StateRestorationToFiatShamirDuplex` rule body. It derives a conditional
Fiat--Shamir property from authenticated duplex and codec facts of one sealed
artifact and prices construction-specific loss. This is strong correspondence
evidence for the inputs a future transport rule needs.

It is not the selected Stage 1 subject relation:

- it does not start from a `FreshPublicCoins` Protocol;
- it does not construct a distinct `FiatShamir(ConstructionId)` Protocol;
- it does not relate two `ProtocolId`s; and
- it cannot by itself be called `FSCompile` under the new architecture.

### 3.3 Test evidence and its limit

| Test | What it demonstrates | What it does not establish |
|---|---|---|
| [`relation-contract.test`](../../../test/Relation/relation-contract.test) | Closed contract admission; post-seal agreement; optional byte-derived facts reduce but do not erase assumptions; foreign contract refusal | Target `ProtocolInterfaceId` closure or relation truth |
| [`relation-disagreements.test`](../../../test/Relation/relation-disagreements.test) | Negative correspondence remains a result and preserves all other agreements | A general negative-judgment schema |
| [`soundness-kernel.mlir`](../../../test/Soundness/soundness-kernel.mlir) | Closed declaration surface, refused invalid mutations, content-digested analysis basis | Truth of cited theorems or future property tracks |
| [`soundness-projection.mlir`](../../../test/Soundness/soundness-projection.mlir) | Exact finite artifact projections and fail-closed missing facts | Adequacy for the redesigned canonical Protocol schema |
| [`fs-duplex-chain.test`](../../../test/Soundness/fs-duplex-chain.test) | End-to-end conditional FS derivation, exact quantitative terms, explicit unsupported construction cases, witness re-derivation | A two-Protocol `FSCompile` judgment |
| [`fs-counted-squeeze.test`](../../../test/Soundness/fs-counted-squeeze.test) | Challenge count is a semantic quantitative input; uncovered events block an artifact-wide claim | Completeness of all transcript-construction effects |
| [`soundness-kzg-preservation.mlir`](../../../test/Soundness/soundness-kzg-preservation.mlir) | Exact preservation-rule application and negative point/order cases | Generic property preservation by all compiler transforms |
| [`compiler-core.mlir`](../../../test/Compiler/compiler-core.mlir) | Domain, shared `DERIVE`, lineage, deterministic selection, decision recomputation, and refusal composition | Independent validation implementation or persisted compiler certificate |
| [`pir-compiler-provider.mlir`](../../../test/Compiler/pir-compiler-provider.mlir) | Full current environment binding, sequential successor re-admission, exact provider identities | The ideal per-subject regime/read-set split |
| [`compiler-config-parity.test`](../../../test/Compiler/compiler-config-parity.test) | A second implementation agrees on current compiler-configuration digests | Semantic correctness of the transform or compiler |

These tests were inspected, not run, in this research pass.

## 4. Bridge family A: relation-interface ingress

### 4.1 Required split

Relation-interface ingress should have two named transitions because optional
relation bytes and a semantic interface declaration have different authority:

```text
ADMIT_RELATION_INTERFACE(
  candidate,
  RelationSemanticRegime,
  exact declaration dependencies)
    -> AdmittedRelationInterface | refuse | unsupported

INTERPRET_RELATION_ARTIFACT(
  AdmittedRelationInterface,
  immutable relation artifact bytes,
  exact format adapter)
    -> RelationArtifactObservation
       { affirmative | negative, computed facts, residual obligations }
       | refuse-before-subject | unsupported
```

`RelationInterfaceCandidate`, its final identity name, and its complete schema
belong to Stage 3 Relations work. Stage 2 needs only the role boundary:

- it is an independently identified relation-domain subject;
- its identity includes the exact relation-interface regime and semantic
  declaration content;
- it can cite a relation artifact identity without proving what the artifact
  means;
- admission does not consume or change a Protocol; and
- a format adapter may add authenticated observations without becoming the
  authority for relation truth.

### 4.2 Contract skeleton

| Field | Provisional contract |
|---|---|
| Source | Immutable relation-interface candidate; optional referenced declaration preimages |
| Target | Process-local immutable admitted-interface capability |
| Source owner | `relations/` |
| Checker owner | `relations/`, with each format reader an exact subordinate profile |
| Authority inputs | Relation semantic regime; closed schema; exact profile/format definitions actually cited |
| Forbidden ambient inputs | Protocol environment, PIR carrier labels, compiler configuration, target backend, relying policy |
| Relation | Formation, canonical identity authentication, and domain admission; not relation satisfaction |
| Identity | Mint relation-interface identity; preserve separately supplied relation-artifact digest as a cited transport/content identity |
| Success | One admitted interface whose every semantic read is determined by its identity and declared dependencies |
| Negative result | Supplied artifact does not match the admitted interface or reader interpretation, after both subjects were reached |
| Refusal | Malformed candidate, identity mismatch, missing cited preimage, or ill-typed declaration |
| Unsupported | Unknown regime, interface construct, or format adapter |
| Capability | In-process read authority only; serialization retains content and IDs, not admission |

An I/O failure while obtaining bytes is operational failure before artifact
interpretation. A byte sequence that is available but does not satisfy the
declared format is a negative interpretation result, not “no answer.” This
preserves the current correspondence tool's useful distinction without making
all parser failures semantic disagreement.

### 4.3 Checker placement candidates

| Candidate | Assessment |
|---|---|
| Direct relation-owned recomputation | **Preferred.** The closed schema and digest predicate are small, deterministic, and locally available. |
| Portable admission receipt | Deferred until a consumer cannot cheaply re-admit the candidate. A self-reporting digest is not a receipt. |
| Trusted loader returning an unchecked object | Rejected as semantic ingress; it collapses parsing and admission. |
| Protocol seal validates relation interfaces | Rejected. It moves post-seal external interpretation into Protocol identity and creates circular authority. |
| Format tool attestation only | Admitted only as an explicit asserted fact; never upgraded to computed truth. |

## 5. Bridge family B: post-seal relation correspondence

### 5.1 Exact target shape

The target bridge is closed over separately authenticated subjects:

```text
RELATION_CORRESPONDENCE(
  AdmittedProtocol[ProtocolId],
  AuthenticatedProtocolInterface[ProtocolInterfaceId -> ProtocolId],
  AdmittedRelationInterface[RelationInterfaceId],
  optional RelationArtifactObservation,
  CorrespondenceSemanticRegime)
    -> RelationCorrespondenceJudgment
       | unsupported
       | refuse-before-judgment
```

The result is about an exact tuple, at least:

```text
(ProtocolId,
 ProtocolInterfaceId,
 RelationInterfaceId,
 optional relation-artifact content identity,
 correspondence regime)
```

It is not a property of bare `ProtocolId`. Canonical semantic ports and events
come from Protocol; external statement positions, names, and packaging come
from `ProtocolInterface`. The bridge may consume only a narrow authenticated
view exported by each owner. It must not reuse the current broad
`SealedSoundnessView` merely because that view happens to contain convenient
fields.

### 5.2 Claimed relation

The relation is provisionally named `RelationCorrespondsAtInterface`. Its
affirmative result establishes only the exact agreements stated by the bridge,
for example:

- the relation interface is scoped to the cited external relation identity;
- its public-instance positions map to exact canonical Protocol semantic ports
  through the cited Protocol interface;
- relation and instance anchors agree with the exact Protocol claim boundary;
- optional byte-derived facts agree with interface-declared facts; and
- every remaining asserted fact is retained as a named obligation.

It does not establish:

- relation truth;
- witness satisfaction, existence, generation, secrecy, or completeness;
- intent or provenance;
- a cryptographic property of the Protocol;
- endpoint projection correctness; or
- equality of Protocol and relation subjects.

### 5.3 Identity and outcomes

The bridge changes none of its source identities. If the judgment becomes a
durable content-addressed object, its preimage must include the exact subject
tuple, bridge regime, verdicts, and obligations. The digest of the result is
not a new relation or Protocol identity.

Outcomes are deliberately three-way:

```text
JudgedAffirmative(agreements, obligations)
JudgedNegative(agreements, disagreements, obligations)
RefusedOrUnsupported(reason)
```

A negative correspondence is a successful bridge evaluation. Missing
authority, a malformed subject, or a question outside the admitted bridge
domain is not a negative correspondence.

### 5.4 Checker placement candidates

| Candidate | Assessment |
|---|---|
| Relations-owned checker over authenticated narrow views | **Preferred.** It owns the relation without redefining either endpoint. |
| Seal-time checker | Rejected; correspondence is post-seal and must not alter Protocol identity. |
| Analysis-owned checker | Rejected; analysis may consume an admitted correspondence fact but does not own relation-interface semantics. |
| OIR projection checker | Rejected; an endpoint consumer cannot retroactively define relation correspondence. |
| Producer assertion | Insufficient; asserted remainders may be inputs but cannot decide computed agreement. |

A portable correspondence certificate is plausible because the current
specification anticipates digest citation. Stage 2 should confirm an actual
replaying consumer before fixing its wire schema. Until then, the semantic
judgment and an in-process paired capability are sufficient.

## 6. Bridge family C: property analysis

### 6.1 Exact subject discipline

Property analysis does not always have the same subject tuple. The property
question selects it explicitly:

- a verifier-semantic property may depend only on `ProtocolId` and an exact
  claim or occurrence;
- an externally callable acceptance property also depends on
  `ProtocolInterfaceId`;
- a plan-sensitive completeness property depends on `ProtocolId` and
  `ProverPlanId`, plus exact relation, witness, and supplier assumptions; and
- a correspondence-conditioned property consumes the exact correspondence
  judgment as a premise, not an ambient relation registry.

If changing an omitted Interface or Plan can change an analysis answer, the
question is mis-typed. It may not be repaired by reading carrier metadata.

### 6.2 Contract skeleton

```text
ANALYZE(
  exact admitted property subject,
  exact PropertyQuestion,
  AnalysisSemanticRegime,
  immutable AnalysisBasis,
  explicit DerivationPlan,
  explicit external judgments and hypotheses,
  source-owned authenticated fact views)
    -> CheckedPropertyDerivation
       { PropertyJudgment }
       | unsupported
       | refuse
```

| Field | Provisional contract |
|---|---|
| Source | Exact admitted subject tuple selected by the property question |
| Target | Conditional typed property judgment plus its checked derivation |
| Source owner | Protocol, Interface, Plan, or Relations owner for each cited subject/fact |
| Bridge/checker owner | `analysis/` |
| Authority inputs | Analysis regime; immutable rule and binding basis; exact plan; explicit external premises; finite source projection vocabulary |
| Relation | Logical derivability under the stated rule interpretation, hypotheses, and exact quantities |
| Identity effect | No source identity changes; conclusion identity and derivation identity, if materialized, remain distinct because several derivations may yield one conclusion |
| Capability | Authority to consume this exact conditional judgment; no general `verified` bit |
| Serialization | A portable witness must rebind the exact subject, basis, regimes, external inputs, and conclusion and be rechecked |

The source-owned projection must satisfy an adequacy condition for the selected
analysis basis: it is the whole channel by which that basis reads the source.
Adding an ambient source read is a specification change, not a harmless
implementation shortcut.

### 6.3 Negative, unknown, and refusal

The target analysis design must distinguish:

- an affirmative conditional judgment;
- a negative judgment derived by a rule or total decision procedure;
- an explicitly qualified unknown or no-conclusion result;
- unsupported property/index/rule forms;
- an invalid submitted derivation plan; and
- malformed or unauthenticated source input.

Failure to find a derivation is not proof of a negative property unless the
search space and a completeness theorem make it so. A derived upper bound is
also not naturally a Boolean “yes.” Stage 4A must choose result variants per
property track rather than force every analysis into one polarity enum.

### 6.4 Checker placement candidates

| Candidate | Assessment |
|---|---|
| Analysis-owned plan checker over an authenticated source view | **Preferred semantic core.** Search stays outside; rule application is deterministic and exact. |
| Portable derivation witness rechecked from subject and basis | **Justified optional artifact.** Property derivations have a clear independent replay consumer and are proof objects, not logs. |
| Compiler-local property evaluator | Rejected. Compiler must call the shared analysis authority. |
| Producer-authored property annotation | Rejected as a judgment; it may only become an explicit assumption. |
| One artifact-global property cache | Rejected unless keyed by exact subject, question, basis, regime, and external inputs and proven complete for its advertised scope. |

## 7. Bridge family D: checked Protocol transformation and compiler

### 7.1 Separate proposal, authentication, relation checking, and selection

The target lifecycle for one nonidentity step is:

```text
AdmittedProtocol P
  + explicit transform application
  + exact transform definition
  -> untrusted or deterministic CanonicalProtocolCandidate Q
  -> authenticate and admit Q under its Protocol regime
  -> check named relation R(P, Q, application)
  -> CheckedProtocolStep(P, Q, R)
```

A compiler composes checked steps, property derivations, constraints,
objectives, and a declared comparison domain. It does not make an unchecked
candidate authoritative by selecting it.

The order `admit target -> check source/target relation` is intentional. Whole-
Protocol admission proves that the target is a well-formed subject; the family
checker proves the separate relation to its predecessor. A checker may inspect
an unauthoritative candidate for diagnostics, but a successful checked step
contains an admitted successor.

### 7.2 Relation and identity taxonomy

| Step class | Required relation | Identity effect |
|---|---|---|
| Carrier-only rewrite | `RepresentationEq` | Same semantic identity; normally outside canonical-to-canonical compilation |
| Empty/identity plan | `ProtocolEq` | Same `ProtocolId` and same canonical graph modulo admitted carrier trivia |
| Observer-preserving semantic rewrite | Exact `TraceEq[observers]`, `TraceRefines[observers]`, or other named relation | Normally a new `ProtocolId`; behavioral relation is not identity |
| Distribution-changing rewrite | Exact equality/closeness relation with parameters | New `ProtocolId` |
| Deliberate protocol change | `IntentionalChange` with explicit semantic delta and lineage | New `ProtocolId`; no implicit preservation |
| Fiat--Shamir transformation | Specialized construction plus `FSCompile` judgment | New `ProtocolId` over the same `CoreId` |

Because canonical PIR has one legal graph per Protocol, a nontrivial change
between two canonical Protocols cannot preserve `ProtocolId` merely because a
validator considers them behaviorally equivalent.

### 7.3 Contract skeleton

| Field | Provisional contract |
|---|---|
| Source | `AdmittedProtocol[P]`; exact application and source coordinates |
| Target | `AdmittedProtocol[Q]` plus checked step relating `P` and `Q` |
| Source/target owner | `pir/` Protocol semantics and admission |
| Transform relation owner | Exact transform family beneath `compiler/`; it cites, rather than redefines, Protocol observers |
| Compiler owner | Domain, plan composition, constraints, objectives, and selection |
| Additional authority | Transform definition/ref; exact Protocol regimes; relation-specific parameters; explicit analysis results used by constraints |
| Forbidden ambient authority | Mutable registry fallback, carrier labels, backend feasibility, unbound Interface or Plan, producer scores |
| Side effects | None outside construction of new immutable subjects and process-local capabilities |
| Serialization | Loses paired capability; a durable checked-step certificate needs an actual replay consumer |

Every checked step must state:

- its exact source and target IDs;
- the relation and protected observer set;
- a total occurrence/claim map for every fact later transported;
- assumptions and deliberately unpreserved observations;
- the exact checker and semantic regimes; and
- whether its target was constructed by recomputation or supplied as a
  proposal.

Structural claim lineage is not itself an application-level semantic relation,
and neither one implies property transport.

### 7.4 Compiler decision contract

The compiler-level envelope is distinct from every family relation checker:

```text
COMPILE_PROTOCOL(
  AdmittedProtocol[P],
  exact CompilerRequest,
  authenticated CompilerConfiguration,
  complete declared candidate-domain provider,
  exact transform-family validators,
  exact Analysis judgments or Analysis authority required by constraints)
    -> CompilerDecision {
         selected AdmittedProtocol[Q],
         checked path P -> Q,
         comparison record
       }
       | NoSelection { complete checked comparison domain }
       | unsupported
       | refuse

CHECK_COMPILER_DECISION(
  the same exact inputs,
  submitted CompilerDecision or NoSelection)
    -> accepted | judged_negative | unsupported | refuse
```

The declared domain, constraints, objectives, tie breakers, transform
definitions, and every semantic regime they read qualify the decision. They do
not enter `Q`'s `ProtocolId` unless their semantic content is already embodied
in `Q`. Selection creates no Protocol: it chooses a target that was already
constructed, authenticated, admitted, and connected to the source by checked
steps.

The decision can remain process-local while its only consumer shares the
compiler authority and cheap full recomputation is available. If materialized,
its identity must commit to the source, request, complete comparison scope,
checked candidate results, objective values, and selected or no-selection
outcome. A target ID and score alone cannot authenticate optimality.

### 7.5 Compiler-level outcomes

The compiler must preserve these distinctions:

- candidate builder failure;
- target admission refusal;
- a successfully evaluated but negative/illegal transform relation;
- unsupported transform or checker regime;
- a valid candidate that violates a request constraint;
- a declared domain with no eligible candidate, yielding successful
  `no_selection`; and
- decision-check refusal because a submitted result differs from recomputation.

`no_selection` is not a malformed request and an illegal candidate is not an
invalid source Protocol.

### 7.6 Checker placement candidates

| Candidate | Assessment |
|---|---|
| Verified transform implementation for all inputs | Strong long-term option, but high proof and extension cost; not required to state v0 semantics. |
| Producer proposal plus per-result translation validation | **Preferred general architecture.** Search and construction may evolve while an exact checker validates each admitted pair. |
| Deterministic recomputation of the target | **Preferred for small closed families.** It is one validation strategy, not a universal relation definition. |
| Proof-generating transform plus portable certificate | Useful when an independent or cross-process consumer exists; otherwise premature schema and version surface. |
| Direct trusted transform | Last resort only with the trusted component and relation limitation explicit. |

The current compiler's deterministic replay is valid correspondence evidence
for the recomputation candidate. Sharing the builder, validator, and semantic
libraries means it is not an independent checker and must not be described as
one.

At selection level, full recomputation of a bounded declared domain remains
reasonable for v0. If domain construction becomes too expensive or externally
produced, the replacement must prove both candidate validity and comparison-
scope completeness; validating only the winner would not justify an optimum.

## 8. Bridge family E: Fiat--Shamir instantiation and `FSCompile`

### 8.1 Three boundaries, not one lowering

The clean target separates:

```text
FIAT_SHAMIR_INSTANTIATE(
  AdmittedProtocol[P_fresh = (Core, FreshPublicCoins)],
  admitted TranscriptConstruction K scoped to Core)
    -> AdmittedProtocol[P_fs = (Core, FiatShamir(K))]

CHECK_FS_COMPILE(
  P_fresh,
  P_fs,
  K,
  exact FS model/theorem basis,
  exact source-to-target occurrence map)
    -> FSCompileJudgment | judged_negative | unsupported | refuse

PROPERTY_TRANSPORT(
  source PropertyJudgment,
  FSCompileJudgment,
  exact FS transport rule,
  explicit resources and assumptions)
    -> target PropertyJudgment + checked derivation
```

Instantiation is a Protocol constructor. It checks that:

- both Protocols cite the same `CoreId` and total schedule;
- every fresh challenge occurrence maps exactly once to construction behavior;
- transcript initialization, domain separation, typed framing, absorb/squeeze
  behavior, codecs, sampling, counts, and failure classes are explicit; and
- the target `ProtocolId` is recomputed from the Core and exact construction.

These conditions establish a well-formed target, not a security theorem.

### 8.2 Meaning of `FSCompile`

`FSCompile` is a theorem-backed correspondence between two exact Protocols. Its
result states that the target is the precise Fiat--Shamir interpretation of the
source interaction under one admitted mathematical model and construction. It
must expose, rather than hide:

- the exact interactive and noninteractive subjects;
- the event and transcript-prefix correspondence;
- the random-oracle, duplex-sponge, or other construction model;
- sampling and distribution relations;
- query/resource variables;
- abort, framing, and codec behavior;
- exact theorem and model assumptions; and
- the property families for which a later transport rule is available.

An `FSCompileJudgment` does not mean “all properties are preserved.” The
multi-round Fiat--Shamir literature has property- and protocol-class-specific
losses, including qualitatively different bounds for general and structured
protocol classes. A single unchecked `compiled = true` bit would erase the
main content of the theorem.

### 8.3 Ownership

| Role | Provisional owner |
|---|---|
| Fresh and FS Protocol definitions, Core equality, construction identity | `pir/` |
| Candidate construction and optional search/selection | `compiler/` when compilation invokes it |
| `FSCompile` theorem/model basis and checking | `analysis/`, jointly specified against exact Protocol exports |
| Property-specific transport | `analysis/` |
| Interface mapping between fresh and noninteractive external contracts | A separate Interface/correspondence bridge; never inferred from shared Core |

This placement prevents the compiler from authoring a cryptographic theorem and
prevents analysis from redefining Protocol construction.

### 8.4 Identity and outcomes

`P_fresh` and `P_fs` share `CoreId` and have distinct `ProtocolId`s.
`TranscriptConstructionId` is an exact input and already participates in the FS
Protocol identity. The `FSCompile` result, if persisted, additionally identifies
its theorem/model basis and correspondence; it does not replace either Protocol
identity.

A well-formed FS Protocol may exist when:

- no theorem basis is installed;
- a theorem does not cover this Core class;
- the requested property has no transport rule; or
- quantitative parameters make the result unusable for one policy.

Those conditions do not retroactively make the Protocol malformed. They yield
unsupported analysis, refusal of a claimed relation, or a valid conditional
judgment that a later policy declines to rely on.

### 8.5 Checker placement candidates

| Candidate | Assessment |
|---|---|
| Treat FS as ordinary deterministic lowering | Rejected; it can construct the target but cannot establish theorem applicability or property loss. |
| Fuse target construction and every property proof | Rejected; the same target may have several property arguments or none, and subject existence must not depend on one analysis catalog. |
| Structural instantiation plus separate theorem-backed `FSCompile` | **Preferred.** It isolates Protocol construction from exact cryptographic correspondence. |
| Producer-supplied FS marker | Rejected; it provides no model, occurrence map, assumptions, or quantitative relation. |
| Portable FS certificate | Deferred until an independent consumer needs to replay the relation without running the analysis stack. |

## 9. Bridge family F: `PropertyTransport`

### 9.1 Exact rule shape

Property transport is an analysis derivation over a checked relation, not a
flag carried by the transform family:

```text
PROPERTY_TRANSPORT(
  source_judgment: PropertyJudgment[S, property_s],
  checked_relation: R(S, T, relation_parameters),
  subject_map: exact map from source property sites to target sites,
  transport_rule: exact rule for (property_s, R) -> property_t,
  explicit assumptions and resource substitutions)
    -> CheckedPropertyDerivation {
         PropertyJudgment[T, property_t]
       }
       | unsupported
       | refuse
```

Acceptance requires at least:

1. the source judgment's subject equals the checked relation's source;
2. the target subject is constructed from the relation and subject map, not
   supplied independently by the caller;
3. the rule explicitly admits the source and target property notions,
   quantification, and result schemas;
4. the checked relation covers every observer and effect the rule requires;
5. the subject/claim occurrence map is total on every property-relevant site;
6. inherited hypotheses and obligations are preserved monotonically unless an
   exact discharge rule proves otherwise;
7. resource substitution and quantitative loss are total, typed, and exact;
8. any distributional approximation or intentional change appears in the
   resulting bound or hypotheses; and
9. rule, relation, and subject regimes are explicitly compatible.

No generic theorem says that `TraceEq`, `TraceRefines`, `IntentionalChange`, or
even `FSCompile` transports every property. Each rule states the property and
the relation it understands.

### 9.2 Identity and authority

Transport changes neither source nor target identity. It creates a new target
judgment and derivation. If separately identified, the conclusion identity
commits to its exact target and conditional content; the derivation identity
also commits to source judgment, checked relation, transport rule, mappings,
and explicit premises.

The transform family may publish a `property_ref` as a discoverable proposal or
attribution. That is not an input sufficient for transport. The current
`PreservationClaim` carrier slot is therefore useful provenance, but its
semantics must remain “an argument is claimed to exist” until Analysis checks
the argument.

### 9.3 Checker placement candidates

| Candidate | Assessment |
|---|---|
| Transform-family checker establishes all property preservation | Rejected; it makes Compiler own property semantics and cannot scale across notions. |
| Compiler checks a property-specific constraint by invoking Analysis | **Preferred compiler integration.** The compiler consumes, but does not reinterpret, the result. |
| Analysis-owned transport rule and proof checker | **Preferred semantic authority.** It composes exact judgments, relations, maps, assumptions, and bounds. |
| Unchecked preservation annotation | Permitted only as provenance or an explicit assumption, never as a derived target judgment. |
| Portable derivation witness | Appropriate when the target judgment crosses a process or trust boundary; use the same exact replay discipline as ordinary property analysis. |

## 10. Cross-bridge closure and identity matrix

| Bridge | Required semantic subjects | Additional identified authority | Hidden carrier context allowed? | Subject identity effect | Result category |
|---|---|---|---|---|---|
| Relation-interface admission | Relation interface candidate | Relation regime and cited schema/profile definitions | No | Mint relation-interface identity | Capability |
| Relation-artifact interpretation | Admitted relation interface + bytes | Exact adapter and adapter regime | No | Preserve interface ID; cite byte digest | Observation/judgment |
| Post-seal correspondence | Protocol + ProtocolInterface + relation interface | Correspondence regime; optional exact artifact observation | No | Preserve all source IDs | Correspondence judgment |
| Property analysis | Exact property subject tuple | Analysis basis, plan, external premises, analysis regime | No | Preserve subject IDs | Property judgment + derivation |
| Checked transform step | Source and target Protocols | Transform definition, relation, parameters, regimes | No | Preserve on identity only; otherwise mint target Protocol ID | Checked relation capability |
| Compiler selection | Source Protocol, checked candidates, exact property results | Domain provider/configuration, constraints, objectives | No | Does not define target IDs; selects one already checked candidate | Decision |
| FS instantiation | Fresh Protocol + transcript construction | Protocol regime | No | Same Core ID; new Protocol ID | Subject/capability |
| `FSCompile` | Exact fresh and FS Protocols | Theorem/model basis, occurrence map, analysis regime | No | Preserve both IDs | Correspondence judgment |
| `PropertyTransport` | Source judgment + checked source/target relation | Exact transport rule, maps, assumptions, analysis regime | No | Preserve subject IDs; mint target judgment/derivation if identified | Property judgment + derivation |

Changing uncited entries in a broad registry must not change any row. If the
complete environment can change a result, its exact content is an input until a
narrower dependency closure is designed. A configuration digest qualifies a
compiler decision; it does not enter a successor `ProtocolId` unless its
semantic content is already part of that Protocol.

## 11. Checker-placement convergence

| Bridge | Preferred v0 placement | Durable witness posture | Primary reason |
|---|---|---|---|
| Relation-interface admission | Direct relation-owned recomputation | None by default | Small closed predicate; bytes and dependencies locally available |
| Relation-artifact interpretation | Exact relation-format adapter, results checked by Relations | Persist only for a named consumer | Adapter authority is narrower than relation truth |
| Post-seal correspondence | Relations-owned checker over authenticated views | Candidate certificate after consumer confirmation | Both endpoints retain independent authority |
| Property analysis | Analysis-owned explicit-plan checker | Yes when independently replayed | Derivation is naturally a proof object and search is separable |
| Transform step | Untrusted proposal or deterministic builder plus exact per-result validator | Process-local paired capability by default | Search need not be trusted; relation is family-specific |
| Compiler selection | Recompute bounded domain, validity, score, and selection | No persisted result schema yet | No external consumer currently justifies one |
| FS instantiation | Protocol constructor, optionally orchestrated by Compiler | None | Subject construction is deterministic and not itself a theorem |
| `FSCompile` | Analysis-owned theorem/model checker over exact Protocol exports | Defer portable certificate pending consumer | Cryptographic relation is not a compiler implementation fact |
| `PropertyTransport` | Analysis-owned rule checker | Same witness discipline as property analysis | Property semantics and hypothesis propagation remain centralized |

The literature supplies useful alternatives, not a vote. Translation
validation motivates checking each produced source/target pair without proving
the optimizer implementation. Proof-generating compilation motivates a
portable proof only when a separate checker is a real consumer. Verified
compilation demonstrates that pass relations compose only after their
observable semantics and theorem are exact. None of these sources defines the
zkc relation taxonomy or proves a zkc implementation correct.

## 12. Conflicts and target changes relative to the current system

### 12.1 Relation boundary

1. Current `statement_correspondence` maps relation slots to labels stored in a
   sealed artifact. Stage 1 makes ABI labels and external bindings part of
   `ProtocolInterfaceId`, not `ProtocolId`. Target correspondence must consume
   the exact Interface subject.
2. Current `zkc-relation` uses `SealedSoundnessView`, a view owned for property
   analysis. Target Relations needs a narrow source-owned correspondence view;
   sharing an implementation helper cannot make Analysis the semantic owner.
3. Current contract loading and optional byte interpretation are separated in
   code but not named as independent semantic transitions. The target makes
   their authority and outcomes explicit.
4. The current spec calls the contract evidence-only relative to Protocol and
   gives it its own digest. That separation remains sound; Stage 3 must decide
   whether `RelationContract` remains the final subject name and identity form.

### 12.2 Analysis boundary

1. Current property subjects cite `artifact_id`. Target subjects must cite the
   exact semantic subject identity and add `ProtocolInterfaceId` or
   `ProverPlanId` only for questions that depend on them.
2. Current PIR projection is a good capability firewall, but its fields and
   adequacy claim must be rebuilt against canonical PIR and the new Core,
   Interface, and Plan boundaries.
3. The current Soundness Kernel has a mature positive conditional-derivation
   model. Stage 4A must add negative/unknown result forms only where the
   property semantics justify them, not by retrofitting every bound into a
   Boolean.
4. Current external theorem receipts and citations do not prove theorem truth
   or artifact applicability. This non-claim remains.

### 12.3 Compiler boundary

1. Current `ArtifactSemantics` correctly prevents producer-populated fact
   mirrors, but the configured PIR adapter binds the complete current
   `ProtocolEnvironment`. Target contracts require exact regime and dependency
   closures per transition.
2. Current deterministic replay authenticates a concrete KZG successor and is
   a useful validator strategy. It is not an independent validator because it
   shares implementation and configured authorities with realization.
3. Current `ClaimCorrespondence` is structural lineage. It does not establish
   an application-level trace relation or property preservation.
4. Current `PreservationClaim` is deliberately unchecked. Target
   `PropertyTransport` turns an actual preservation argument into an
   analysis-owned derivation; the claim remains provenance only.
5. Current `CompilerResult` is an in-memory selected ordinal and
   `checkDecision` recomputes it. That is sufficient while no persistent
   decision consumer exists.

### 12.4 Fiat--Shamir boundary

1. Current sealed artifacts combine interactive round structure with a chosen
   construction profile. Stage 1 now identifies Fresh and FS Protocols
   separately over one Core.
2. Current `StateRestorationToFiatShamirDuplex` is a property rule within one
   artifact. Its authenticated codec, squeeze, coverage, and quantitative facts
   inform the target transport rule, but its current subject relation cannot be
   retained unchanged.
3. The new model requires an explicit fresh-to-FS occurrence map and two exact
   Protocol IDs before property transport is meaningful.

These are design deltas, not defect or vulnerability findings and not
implementation-change requests.

## 13. Scenario results and falsifiers

The provisional contracts must survive the following scenarios.

### 13.1 Interface relabel and repackaging

Two Interfaces over one Protocol bind different external names or packaging.
Protocol-only property analysis must return the same result. Relation
correspondence may differ and must cite the respective `ProtocolInterfaceId`.

**Falsifier:** a correspondence checker can change its result after only
carrier labels change while receiving the same advertised inputs.

### 13.2 Relation artifact supplied later

Admit a relation interface without bytes, then supply bytes to an exact adapter.
The later observation may convert declared facts into computed or cross-checked
facts while preserving unresolved semantic obligations.

**Falsifier:** supplying bytes changes `ProtocolId`, or an agreeing header is
reported as proof of relation meaning or witness correctness.

### 13.3 Negative correspondence

A well-formed relation interface and readable artifact disagree on one field.
The result retains other agreements and returns a negative correspondence.

**Falsifier:** the bridge reports malformed/unsupported, discards already
computed facts, or emits an affirmative result with a warning.

### 13.4 Successful negative property result

Ask a closed decidable property question for which the analysis basis derives a
negative result.

**Falsifier:** negative is encoded as checker failure, or failure to find a
derivation is automatically encoded as negative without a completeness theorem.

### 13.5 Identity and content-changing compiler plans

Run an empty plan and a semantics-changing plan. The empty plan reproduces the
same canonical Protocol and ID. The nonidentity plan produces a newly admitted
Protocol and a named checked relation.

**Falsifier:** a noncanonical alternate graph reuses `ProtocolId`, or a new ID
is treated as evidence of either equivalence or intentional difference without
the checked relation.

### 13.6 Structural relation without property transport

Validate a transform's exact claim lineage and selected trace relation, but
provide no transport rule for completeness or zero knowledge.

**Falsifier:** Compiler or a consumer infers those properties from legality or
from an unchecked preservation name.

### 13.7 Fresh-to-FS construction without theorem basis

Construct and admit `P_fs` from `P_fresh` and an exact transcript construction,
then remove the FS theorem/model basis.

**Required result:** `P_fs` remains a valid Protocol subject; `FSCompile` and
property transport are unavailable or refused at their own boundary.

**Falsifier:** absence of an analysis theorem invalidates the target Protocol,
or target admission is reported as an FS security result.

### 13.8 FS theorem and property specificity

Hold the Core and construction fixed while requesting two property tracks with
different theorem prerequisites or losses.

**Falsifier:** one global `FS-valid` bit discharges both, or a bound/hypothesis
from one track silently enters the other.

### 13.9 Serialization and replay

Serialize a Protocol, a correspondence result, and a property derivation into
a new process.

**Required result:** Protocol and relation subjects are re-admitted; a durable
correspondence or property witness is rechecked under exact regimes and bases;
no process-local capability survives by assertion.

**Falsifier:** a serialized `admitted`, `checked`, or `preserved` marker alone
restores authority.

### 13.10 Compiler optimum and incomplete domain

Validate a winning candidate but omit another member of the declared
comparison domain.

**Falsifier:** the result is accepted as the optimum without recomputing the
domain or checking a complete-domain witness.

## 14. Open questions routed to later work

### Stage 2 convergence questions

1. What exact term names the relation-domain interface subject, and what
   minimum identity preimage closes all current and selected consumers?
2. Does optional relation-artifact interpretation mint an identified fact
   object, or remain a process-local observation consumed immediately by
   correspondence?
3. Which concrete consumer justifies a portable relation-correspondence
   certificate in v0?
4. What is the exact admission transition for `ProtocolInterface`, and which
   narrow view does it export to Relations?
5. Which transform relations have reusable checkers in v0, and which remain
   family-specific intentional changes?
6. Does compiler comparison-domain completeness remain cheap enough to
   recompute, or is a checked domain witness eventually required?
7. Which exact owner names and versions the `FSCompile` theorem/model basis
   while keeping Protocol construction under `pir/`?

### Stage 3 Protocol and Relations questions

1. Complete `ProtocolInterface` and relation-interface schemas and their
   canonical identity encodings.
2. Define canonical semantic port and claim occurrence references used by
   correspondence.
3. Define the exact fresh-to-FS occurrence and transcript-prefix map supplied
   by Protocol semantics.
4. Decide whether relation artifact identity, relation semantic identity, and
   interface identity are one factorization or several dependent identities.

### Stage 4A Analysis and Compiler questions

1. Define property-subject variants, polarity/unknown forms, analysis-basis
   identity, and derivation identity.
2. Rebuild the authenticated Protocol fact projection and prove or test its
   adequacy for each analysis basis.
3. Define the exact `FSCompile` result schema and property-specific transport
   rules for soundness, knowledge, completeness, and any later zero-knowledge
   track separately.
4. Define the checked Protocol-step schema, relation composition, and
   property-relevant occurrence/claim maps.
5. Decide which current preservation claims gain admitted transport rules and
   which remain only attributed proposals.

## 15. Research comparison

Three external lessons materially constrain the candidates:

1. [CompCert's semantic-preservation contract](https://compcert.org/man/manual.pdf)
   is stated over observable behavior, permits compile-time refusal, and
   composes pass-specific preservation proofs. The transfer is the need for an
   exact relation per Protocol transform and explicit observer sets. It does
   not imply that zkc should adopt CompCert's languages, proof assistant, or one
   universal preservation theorem.
2. [Translation validation](https://doi.org/10.1007/BFb0054170) checks each
   concrete translation rather than trusting the optimizer implementation. The
   transfer is the producer/validator split for checked Protocol steps. A
   validator establishes only its formal relation and is not automatically an
   independent implementation.
3. [Proof-generating compilation](https://doi.org/10.1016/j.entcs.2005.03.023)
   demonstrates a source/target translation predicate plus an independently
   checkable proof. The transfer is conditional: add a portable witness when a
   replaying consumer justifies it, not as a universal transition envelope.
4. [Multi-round Fiat--Shamir analysis](https://eprint.iacr.org/2021/1377.pdf)
   shows that the transformed security statement and loss depend on the round
   structure and protocol class. The transfer is the strict split between FS
   subject construction, `FSCompile`, and property-specific transport.
5. [Duplex-sponge Fiat--Shamir analysis](https://eprint.iacr.org/2025/536.pdf)
   makes the stateful construction, trace transformation, codecs, aborts, and
   several property analyses explicit. The transfer is the requirement to bind
   construction and model facts exactly; it is not evidence that the current
   zkc construction or bounds conform to that paper.

## 16. Non-claims

- This dossier is not normative and does not start Stage 3 or Stage 4 domain
  schema design.
- It does not select final C++, Rust, MLIR, JSON, or filesystem types.
- It does not prove relation truth, witness satisfaction, a cryptographic
  property, compiler correctness, Fiat--Shamir security, or property
  preservation for any zkc transform.
- Static source and test inspection is implementation-correspondence evidence;
  the tests were not executed here.
- Current deterministic replay, parity tests, and witness re-derivation do not
  imply independent implementations or formal verification.
- A checked structural transform is not backend realization and says nothing
  about emitted prover equivalence.
- A relation or property result does not authorize consumer reliance; reliance
  remains a later policy decision.
- No implementation change, identity migration, portable wire schema, or new
  long-lived compatibility promise is authorized by this page.
- The external literature informs relation and checker design only; it does not
  establish zkc conformance.

## 17. Provisional convergence statement

The semantic-bridge family converges on this architecture:

```text
small subject admission predicates
  -> direct owner recomputation

cross-domain correspondence
  -> exact independently owned subjects
  -> bridge-owned affirmative/negative judgment

property analysis
  -> source-owned authenticated view
  -> analysis-owned explicit-plan checker
  -> conditional judgment and replayable derivation

Protocol compilation
  -> untrusted search or deterministic construction
  -> target re-admission
  -> per-result named relation validation
  -> analysis-owned constraints and property transport
  -> checked selection over an exact declared domain

Fiat--Shamir
  -> deterministic new Protocol construction over the same Core
  -> distinct theorem-backed FSCompile judgment
  -> separate property-specific transport
```

This is the smallest model that keeps semantic subject creation, cross-domain
correspondence, logical derivation, checked semantic change, cryptographic
compilation, and consumer choice from laundering authority into one another.
