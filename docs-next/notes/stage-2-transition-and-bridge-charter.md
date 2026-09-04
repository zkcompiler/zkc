# Stage 2 transition and bridge charter

> **Document kind:** Temporary work-package charter
> **Document state:** Complete; retained as the historical Stage 2 charter
> **Provisional owner:** `project`
> **Authority:** None. This charter scopes research and convergence; it does
> not define a transition, admit an artifact, select a checker, or authorize
> implementation work.
> **Disposition:** Reviewed contracts are absorbed into their durable
> architecture and domain boundaries. Retain this historical charter with the
> completed package until the temporary workspace deletion gate is met.

> **Completion notice — 2026-08-22:** Stage 1 completed and published the
> selected non-normative
> [Protocol IR Architecture](../project/protocol-ir-architecture.md), including
> the fixed Stage 2 entry contract. Stage 2 then completed its reconstruction,
> external research, candidate comparison, scenario falsification, convergence,
> durable promotion, and bounded Stage 3 handoff. The selected result is the
> [Transition and Bridge Architecture](../project/transition-and-bridge-architecture.md).
> Stage 3 subsequently consumed that bounded handoff and completed on
> 2026-08-22. Earlier material below is retained as the historical scope and
> gate, not as a second decision owner.

## 1. Scope and central question

Stage 2 turns the provisional Stage 1 subject vocabulary into a typed catalog
of authority-bearing transitions and cross-domain bridges.

The central question is:

> Which exact transitions connect the semantic subjects, and what equality,
> interpretation, admission, derivability, preservation, refinement,
> correspondence, coverage, observation, appraisal, reliance, or explicit
> non-preservation relation does each successful transition establish?

The package covers every currently admitted boundary and every boundary already
selected by target architecture. It specifies downstream subjects only deeply
enough to make their ingress, authority, identity, and refusal contracts
unambiguous. Full Protocol-and-Relations, Analysis, Compiler, OIR, Realization,
and Evidence schemas remain later owning packages.

This is not a directory migration, a normative rewrite, an implementation
change, or a proposal for one universal transition IR.

## 2. Selected Stage 1 entry and historical baseline

The active Stage 1 inputs are:

```text
typed SemanticRegime per subject family
InteractiveCore[CoreId] with one total observable schedule
ChallengeInterpretation = FreshPublicCoins | FiatShamir(ConstructionId)
Protocol[ProtocolId] = Core + ChallengeInterpretation
ProtocolInterface[ProtocolInterfaceId depends on ProtocolId]
ProverPlan[ProverPlanId depends on ProtocolId]
closed canonical PIR candidate in MLIR
AuthenticatedCanonicalProtocol
AdmittedProtocol immutable capability
purpose-specific ConsumerView or checked certificate
OIR derived from ProtocolInterfaceId and endpoint role
```

Canonical PIR is a distinct small closed MLIR level downstream of a rich
authoring/import/synthesis workbench. Semantic identity is independent of MLIR
transport, regime-qualified, and compositionally factored. The exact
transition schemas and validation bases remain Stage 2 work.

### 2.1 Historical first entry contract

Before the reopening, Stage 2 provisionally inherited the subject model in the
[Candidate Protocol Subject and Lifecycle](../pir/protocol-lifecycle.md):

```text
ProtocolDraft
ResolvedSealCandidate
ProtocolRoot
SealAuthorityGraph(root)
ReferencedSubjectGraph(root)
SealedProtocol[ProtocolId] under SemanticRegime
PersistedPirArtifact[ProtocolId]
DecodedPirCarrier[ProtocolId]
SemanticRegime
ProtocolInterface or canonical positional interface
AdmittedProtocol[ProtocolId, AdmissionBasis, SemanticRegime]
AdmittedPirCarrier[
  ProtocolId,
  AdmissionBasis,
  SemanticRegime,
  CarrierContext,
  RetainedResolverEnvironment
]
ProtocolSubjectRef
ConsumerView
DerivedArtifactOrJudgment
```

`CarrierContext` is the Stage 1 placeholder for authenticated read-only PIR
representation and carrier-qualified fields excluded from `ProtocolRoot`. It
has no selected independent identity; Stage 2 must enumerate every field a
consumer actually reads and either type it as an explicit transition input or
remove the dependency. `RetainedResolverEnvironment` is the broader immutable
provider retained by the current admitted artifact beyond the minimal cited
admission basis. It is a separate authority axis: any uncited lookup must be
declared by the consuming transition.

The following constraints were inputs to the earlier Stage 2 attempt, not new
Stage 2 conclusions. They are preserved as historical comparison and are
superseded wherever the selected architecture differs:

1. There is one Protocol semantic subject and one content identity.
2. PIR/MLIR remains the sole supported v0 authoring and persistence carrier.
3. `CanonicalProtocolForm` is an internal identity projection, not a second
   ingress schema or wire contract.
4. `SealAuthorityGraph(root)` contains declarations that seal is authorized to
   interpret; `ReferencedSubjectGraph(root)` contains opaque subjects that seal
   may shape-check or cite without acquiring interpretation authority.
5. Protocol identity, admission basis, retained resolver environment, compiler
   configuration, interface input, and runtime supplier closure are separate
   axes unless a later decision deliberately joins them.
6. Serialization ends process-local capability continuity.
7. A consumer cannot use carrier data erased from Protocol identity unless the
   data becomes an explicit authenticated transition input or is replaced by a
   canonical root-derived value.
8. Ephemeral views do not acquire independent semantic authority. Durable OIR,
   relation, derivation, judgment, realization, and evidence results remain
   owned and identified by their producing domains.

Stage 2 may reopen the selected factorization only under the reversal
conditions in the owning
[Protocol IR Architecture](../project/protocol-ir-architecture.md).
`ProtocolInterfaceId`, typed semantic regimes, total Core schedule, separate
`ProverPlanId`, and the closed canonical PIR level are fixed entry inputs, not
unresolved Stage 2 choices.

## 3. Current baseline and reason for review

The current corpus already has strong, non-uniform boundaries:

```text
author or edit -> seal
link -> new Open PIR -> seal
seal -> persist -> decode -> admit
admit -> derive analysis view -> conditional judgment
admit -> checked transform -> resealed and re-admitted successor
admit -> project -> paired source/OIR capability and OIR artifact
OIR + suppliers -> emitted endpoint -> invocation result
sealed Protocol + relation contract -> correspondence result
observation -> evidence record -> appraisal -> reliance
```

They cannot be specified as one generic lowering operation:

- seal checks structural closure and mints Protocol identity;
- persist and decode represent and authenticate the same identity;
- admit re-establishes authority under a resolver and semantic regime;
- analysis can successfully derive a negative judgment;
- compiler transformation may deliberately produce a different Protocol;
- projection creates an endpoint subject and a source-relative coverage claim;
- realization binds abstract behavior to concrete suppliers;
- execution produces one operational observation; and
- appraisal and reliance are policy-qualified decisions, not semantic facts.

The review is necessary because exact source and target types, ambient read
sets, identity effects, capability lifetimes, checker authority, and refusal
classes are distributed across several current owners. Stage 1 also produced a
concrete counterexample: current projection and relation wiring can consult
author labels erased from `ProtocolId`. A transition that relies on such hidden
carrier context is not closed over its advertised inputs.

## 4. Transition ontology

The following families organize research. They are not one runtime sum type.

### 4.1 Lifecycle and authentication

```text
author or import
resolve for seal
seal
persist
decode
admit
derive consumer view
reopen and discard authority
```

### 4.2 Protocol construction and checked change

```text
static link
checked Protocol transform
reseal and authenticate successor
```

### 4.3 Cross-domain semantic bridges

```text
relation-interface ingress
post-seal relation correspondence
property analysis
OIR projection
supplier binding
endpoint realization
```

### 4.4 Operational, evidential, and reliance transitions

```text
deploy
invoke
record or attribute observation
appraise evidence
make use-specific reliance decision
```

Every entry must be classified as one or more of:

```text
proposal or state change
representation or interpretation
authentication or admission
checked semantic transformation
derivation or judgment
correspondence or coverage
operational effect or observation
evidence appraisal
consumer decision
```

A negative judgment can be the successful output of derivation. An unsupported
projection can be a typed refusal without making its source invalid. An
operational failure does not retroactively invalidate Protocol or OIR meaning.

## 5. Required transition contract

For every transition, the package must record the following fields in prose or
tables. This is a review schema, not authorization for a serialized
`TransitionRecord`.

### 5.1 Ownership and classification

```text
stable descriptive name
current research state
current normative owner
provisional target owner
source-definition owner
target-definition owner
bridge or checker owner
relying consumer or policy owner
implementation correspondence and evidence scope
transition family, direction, cardinality, determinism, and side effects
```

### 5.2 Exact inputs and read set

```text
source subjects and required authority state
identified semantic inputs
resolver and declaration material
carrier-only context
ProtocolInterface or ABI input
analysis, compiler, or projection configuration
supplier and runtime bindings
relying policy
semantic regime and version
checker or procedure authority
binding time, snapshot, lifetime, and concurrency assumptions
```

Each contract must name which closures it reads:

```text
Protocol byte-identity closure
SealAuthorityGraph(root)
ReferencedSubjectGraph(root)
complete resolver or compiler environment
ProtocolInterface or canonical interface
execution and supplier closure
external theorem, relation, or relying-policy authority
```

If uncited or unlisted material may change a result, it is an input and must be
named. Ambient lookup is not a substitute for a declared authority boundary.

### 5.3 Result and claimed relation

```text
result category: subject, artifact, view, capability, judgment, observation,
                 assessment, or reliance decision
successful postcondition
claimed relation and its exact source and target
coverage or source map, where applicable
facts deliberately not established
residual trust and trusted-computing-base dependencies
```

The relation must be selected and defined rather than summarized as `valid` or
`lowered`. Candidate relation families include:

```text
content equality or identity preservation
carrier interpretation and representation fidelity
structural formation or seal admission
logical derivability
semantic preservation
behavioral refinement or equivalence
source/target correspondence
obligation coverage
operational observation
policy-qualified evidence appraisal
use-specific reliance
explicit non-preservation with authenticated successor semantics
```

### 5.4 Identity effects

```text
identities consumed
identities preserved
identities minted
identities cited only as provenance
configuration, interface, transition, witness, or checker identity
facts explicitly excluded from identity
cache and comparison key, if any
migration effect of changing the contract
```

“Same ID” must not be used as shorthand for retained admission authority,
semantic equivalence across regimes, identical interface, or identical runtime
behavior.

### 5.5 Outcomes and refusal

The catalog must distinguish, where applicable:

```text
malformed carrier
unsupported version or construct
stored/computed identity mismatch
missing or invalid declaration preimage
seal inadmissibility
consumer unsupportedness
successful negative judgment
illegal compiler candidate
endpoint or target refusal
supplier incompatibility
operational failure
partial-effect failure
appraisal rejection
reliance denial
```

One shared envelope is acceptable only if the domain-specific variants and
meanings remain visible.

### 5.6 Capability, replay, and evolution

```text
capability gained, narrowed, preserved, or discarded
authorized consumers and operations
copy, alias, concurrency, and lifetime behavior
serialization degradation
replay or independent-checking behavior
supersession and invalidation
semantic-regime compatibility
scenario vectors and counterexamples
reversal trigger
```

## 6. Bridge ownership rule

A cross-domain bridge has four independently named authorities:

| Role | Responsibility | Must not do |
|---|---|---|
| Source owner | Defines the exact input subject and exported facts | Define target semantics through a convenient encoding |
| Bridge or checker owner | Defines and checks the named relation between exact inputs and outputs | Redefine either endpoint or claim more than the checked relation |
| Target owner | Defines the result subject, behavior, and identity | Reinterpret missing source facts as defaults |
| Relying consumer | Decides whether the result is adequate for one use | Turn reliance policy into semantic truth |

The bridge contract cites source and target definitions rather than copying
them. A shared field layout does not justify moving bridges into `foundation/`.
Extraction requires at least two transitions with the same semantics,
lifecycle, authority, and refusal behavior.

## 7. Priority boundary A: Protocol interface closure

### 7.1 Counterexample

The current canonical PIR identity normalizes away author labels. Current OIR
identity includes statement and witness labels, while relation correspondence
can use those labels as wiring. Existing relabel fixtures therefore admit the
following shape:

```text
same ProtocolId
different carrier labels
different OIR identity or relation-wiring input
```

Projection is consequently not yet a function of only
`(ProtocolId, endpoint_kind)`. The package must not hide the additional input
inside `AdmittedPirCarrier` metadata.

### 7.2 Stage 1 resolution and remaining Stage 2 work

Stage 1 selected a dependent, separately identified `ProtocolInterface` whose
identity commits to `ProtocolId`. Canonical semantic ports and proof-event
occurrences remain Protocol content; external names, containers, and codecs
may remain Interface content only when they decode before and do not alter the
fixed Protocol meaning. Carrier-qualified hidden metadata is rejected as a
target input.

Stage 2 does not reconsider whether this subject exists. It must make every
transition that consumes it functionally closed by specifying:

```text
exact admitted Interface input and authority state
the Protocol-owned canonical references it binds
the Interface read set and semantic regime
identity and cache effects
substitution and adapter-correctness requirements
malformed-input and interface-refusal outcomes
serialization and independent replay behavior
the Relations, OIR, and later realization owners that refine its fields
```

The historical four-way candidate portfolio remains evidence for the selected
factorization. A contradiction must reopen the owning Stage 1 decision rather
than silently choosing another interface model inside a bridge contract.

## 8. Priority decision B: closure and semantic regime

Build a read-set matrix for at least seal, admit, link, analysis, checked
transform, relation correspondence, projection, supplier binding, realization,
and invocation.

The matrix must test:

1. two resolver environments that differ only by uncited entries;
2. a missing, changed, or mistyped cited declaration preimage;
3. an opaque anchor present in `ReferencedSubjectGraph(root)` but deliberately
   uninterpreted by seal;
4. the same Protocol bytes and authority graph under different intrinsic
   `SemanticRegime` interpretations;
5. the same predecessor under different complete compiler configurations;
6. the same Protocol under different relation or interface bindings;
7. the same OIR under different supplier bindings; and
8. the same realized endpoint under different deployment and invocation
   environments.

For each difference, state whether it may affect:

```text
ProtocolId
Protocol admission
capability comparability
analysis question or judgment
compiler configuration identity or successor ProtocolId
relation result or InterfaceId
OIR identity or paired projection admission
realized artifact or deployment identity
invocation result only
```

The package must decide which transitions can use process-local implicit regime
authority and which require an explicit stable regime reference for caching,
serialization, independent checking, or cross-version comparison.

## 9. Priority boundary C: ProverPlan closure

Stage 1 selected `ProverPlanId` as a dependent subject over `ProtocolId` that
realizes Protocol-owned abstract prover obligations without changing
verifier-visible behavior. Stage 2 must determine which transitions consume a
plan, what authority state they require, and whether the plan affects OIR
projection or remains solely a realization input.

The package must maintain an obligation/plan ownership ledger covering:

```text
Protocol-owned abstract obligation
canonical obligation occurrence identity
plan-owned construction or witness dependency
plan admission and structural coverage
optional projection dependency
supplier requirement and later binding
facts required for completeness but not established by plan admission
```

No plan field may arrive as ambient compiler or realization state. If a plan
changes proof events, their required distributions, transcript behavior,
external proof ABI, checks, or accepted language, the proposed plan instead
denotes a different Protocol.

## 10. Checker and witness alternatives

Select a model per transition rather than declaring one global architecture:

| Model | Suitable pressure | Required caution |
|---|---|---|
| Direct consumer recomputation | Small deterministic admission predicate and locally available closure | Recompute under the exact regime and declared inputs |
| Process-local checked transition plus paired capability | Strong in-process source/target relation with no external consumer | Serialization loses the paired authority |
| Producer proposal plus translation validation | Complex search or transform with a smaller source/target checker | Validator establishes only its named relation and domain |
| Portable witness or certificate | Independent replay, exchange, caching, or a smaller relying checker justifies a durable object | Must identify claim, checker regime, declaration dependencies, replay, and failure |
| Direct trusted transformation | No practical validator and an explicitly accepted trusted boundary | State the trusted component and non-portability; do not imply independent checking |
| No transition artifact | Rechecking is cheap and no durable consumer exists | Preserve this as a first-class design choice |

Compare independence, read-set size, diagnostic quality, replay and
serialization, semantic-regime stability, implementation cost, migration, and
whether a durable identity has a real consumer.

The package must not infer that current recomputation is proof-carrying code or
that a portable certificate is beneficial for every boundary.

## 11. Research sequence

1. Run a bounded Stage 1 intake review, freeze the selected invariants, and
   reconcile this charter with the active entry contract.
2. Reconstruct the complete current transition catalog and section-level owner
   map from normative sources.
3. Trace implementation and tests as correspondence evidence for inputs,
   ambient reads, identity effects, capability construction, and refusal.
4. Study external transition and checking models, their installed-cost pain
   points, and their exact transfer limits; generate an equal-resolution
   candidate portfolio rather than inheriting the charter's first hypothesis.
5. Close the `ProtocolInterface` and `ProverPlan` transition inputs under the
   selected Stage 1 factorization.
6. Build closure, read-set, identity-effect, observer/effect, and
   semantic-regime matrices.
7. Specify the lifecycle spine: author/import, resolve, normalize, canonical
   candidate production, authentication and admission, persistence, decode and
   re-admission, consumer-view derivation, reopen, and link.
8. Specify checked-change and cross-domain bridge skeletons with both endpoint
   owners: relation ingress/correspondence, analysis, compiler transform,
   projection, supplier binding, and realization.
9. Specify deployment, invocation, evidence, appraisal, and reliance only
   deeply enough to preserve category and authority boundaries.
10. Compare checker and witness candidates per transition, including the option
   of no durable transition object.
11. Run the scenario portfolio, capability prompts, and adversarial
    counterexamples.
12. Converge across domain owners, promote durable conclusions, record open
    decisions and reversal triggers, and prepare the Stage 3 entry contract.

Research follows the evidence order in the
[Design Research Method](../project/design-research-method.md). Primary
literature and official specifications may expose alternatives or justify a
constraint, but cannot establish zkc implementation conformance. In
particular, MLIR interfaces and bytecode versioning inform carrier boundaries;
data-abstraction work informs representation independence; translation
validation and proof-carrying-code work inform checker placement; and
object-capability work informs narrow in-process authority. None is imported as
a complete zkc design by analogy.

## 12. Scenario and falsification portfolio

### 12.1 Minimal lifecycle

Author one closed Protocol, resolve, seal, persist, decode, admit, and derive a
consumer view. Verify which steps preserve identity, which reconstruct
authority, and where serialization discards capability continuity.

### 12.2 Relation-bound subject

Carry an opaque anchor in Protocol identity while a separately authenticated
relation contract interprets it post-seal. Test pre-seal interface ingress as a
different role and prevent relation truth from entering seal by implication.

### 12.3 Checked compiler transformation

Consume one admitted predecessor plus a complete compiler configuration,
construct candidates, reopen only as an internal unauthoritative mechanism,
and produce a resealed and re-admitted successor with a recomputed Protocol
identity. The empty identity plan must preserve the predecessor artifact and
ID; a content-changing plan may produce a different ID.

### 12.4 OIR relabel counterexample

Use two accepted PIR carriers with equal `ProtocolId` and distinct author
labels. Trace current OIR IDs and relation wiring, then test every
`ProtocolInterface` candidate against both artifacts.

### 12.5 Independent replay

Begin with raw persisted bytes in a new process. Require explicit ingress,
expected identity when supplied, reachable declaration preimages, semantic
regime, and the consumer question. Confirm that no serialized capability flag
substitutes for rechecking.

### 12.6 Successful negative analysis

Derive a well-formed negative property judgment and distinguish it from
malformed input, unavailable rules, unsupported analysis, and checker refusal.

### 12.7 Realization and invocation

Bind one OIR to two supplier or deployment configurations. Determine which
identities and correspondence claims change, and ensure a successful or failed
run cannot flow backward into Protocol or OIR meaning.

### 12.8 Falsification requirements

At least one scenario must attempt each of:

- an undeclared ambient read;
- identity laundering across different interfaces or regimes;
- capability laundering through serialization or raw carrier copying;
- circular authority from evidence or reliance back into semantics;
- a bridge that silently redefines its source or target;
- a negative judgment mislabeled as refusal;
- a partial operational effect without a stated effect boundary; and
- a universal transition abstraction whose similar fields conceal different
  mathematical relations.

## 13. Required outputs

The package must produce:

1. a current typed transition catalog with section-level normative ownership;
2. a provisional target transition catalog covering every current admitted and
   selected target boundary;
3. completed transition contracts using the fields in Section 5;
4. a bridge-owner matrix;
5. closure/read-set and semantic-regime matrices;
6. an identity-effect matrix;
7. a qualified outcome and refusal taxonomy;
8. a `ProtocolInterface` boundary contract and field-ownership ledger;
9. a `ProverPlan` obligation/realization boundary ledger;
10. a per-transition checker and witness candidate matrix;
11. scenario, opportunity, and counterexample results;
12. a current-to-target implementation correspondence and gap inventory;
13. durable decisions, deliberately deferred questions, exact owners, and
    reversal triggers; and
14. an explicit Stage 3 Protocol-semantics-and-Relations entry contract.

Detailed reconstruction evidence, exact code traces, test vectors, and
unpromoted alternatives belong in the temporary
[`stage-2-transitions/`](stage-2-transitions/README.md) package. Durable pages
receive reviewed conclusions and neutral rationale, not raw review logs.

## 14. Risks and non-claims

- A common review checklist is not a universal transition language.
- Similar source/target fields do not imply the same correctness relation.
- A transition need not be a deterministic function; nondeterminism,
  selection, and effects must be modeled explicitly where present.
- A stable subject ID does not preserve a process-local capability or make two
  semantic regimes equivalent.
- A digest reference does not supply, type-check, interpret, or prove its
  preimage.
- A bridge checker cannot redefine source or target semantics or authorize its
  own use.
- A paired capability is not automatically a portable proof or certificate.
- A successful analysis with a negative conclusion is not a failed transition.
- Operational success, evidence appraisal, and consumer reliance do not flow
  backward into Protocol or endpoint meaning.
- Deployment and invocation may have partial effects; their later owner must
  state effect, retry, and rollback boundaries rather than reuse pure-transform
  language.
- Adding universal transition IDs or witnesses can create an accidental wire
  and version surface; every durable object requires an actual consumer.
- This package does not change current artifact identity, create a second
  Protocol carrier, migrate normative authority, or modify implementation code.

## 15. Intended durable destinations

| Result | Destination |
|---|---|
| Cross-system transition taxonomy and ownership map | `project/` architecture and information architecture |
| Protocol lifecycle transitions and capability rules | `pir/` with extracted common mechanisms in `foundation/` only when justified |
| Relation ingress and correspondence bridges | `relations/` with exact references to Protocol and later realization owners |
| Analysis transition and judgment boundary | `analysis/` |
| Checked Protocol transformation | `compiler/` |
| Projection, endpoint coverage, and interface consumption | `oir/` |
| Supplier binding, emission, deployment, invocation, and effects | `realization/` |
| Observation, appraisal, and reliance separation | `evidence/` and the relying consumer |
| Non-obvious accepted cross-domain choices | Future decision records beside their owning architecture |
| Deferred product work | The single future public roadmap, only after design convergence |

No durable destination may depend on this charter after absorption.

## 16. Exit, reopening, and deletion gates

### 16.1 Exit condition

Stage 2 exits only when:

- every current admitted and selected target boundary has an unambiguous source
  and result category;
- every contract names its authorities, read set, semantic regime, binding time,
  claimed relation, identity effect, success, refusal, capability behavior,
  replay or serialization behavior, owner, residual trust, and non-claims;
- no boundary is described only as `valid`, `lowered`, or `checked`;
- negative judgments, typed refusals, and operational failures cannot be
  confused;
- label/interface and ambient-environment dependencies are explicit;
- every Interface- or ProverPlan-sensitive transition consumes its exact
  identified input without carrier, compiler, or realization ambient state;
- at least one meaningful checker alternative has been compared per major
  transition family;
- a clean-room reviewer can begin Stage 3 without consulting current C++ type
  names to infer semantic contracts; and
- no universal record, certificate, or ID has been introduced merely because
  several transitions share table columns.

This condition is satisfied. The
[Convergence Record](stage-2-transitions/convergence.md) audits the selected
candidate and non-selections, the
[Absorption Record](stage-2-transitions/absorption-record.md) accounts for all
durable destinations and deferrals, and the
[Stage 3 Entry Contract](stage-2-transitions/stage-3-entry-contract.md) gives a
clean-room next gate without activating it.

### 16.2 Reopen conditions

Reopen a provisional contract when:

- a hidden input makes the transition non-functional over its declared source;
- a new consumer requires a different subject or authority state;
- an identity contradiction or cross-regime comparison appears;
- a supposedly pure transition has observable side effects;
- a portable checker requires declaration material or regime identity that the
  contract omits;
- implementation feasibility invalidates an assumed checker or witness; or
- a credible alternative materially improves independence, composition,
  migration, or option value.

### 16.3 Deletion trigger

Delete this charter only after:

1. reviewed conclusions and durable rationale are present in their exact
   owners;
2. every rejected or deferred alternative has an owner and durable trigger;
3. the Stage 3 package has a bounded entry contract;
4. the temporary workspace inventory is updated;
5. no durable page depends on this file; and
6. documentation validation reports no orphaned route or manifest entry.
