# Information architecture

> **Document kind:** Architecture map
> **Document state:** Active
> **Target decision status:** Selected non-normative boundaries
> **Provisional owner:** `project`
> **Authority:** Non-normative. This page records the target conceptual
> partition and routes later specifications; it does not move authority from
> the current specifications.

This map applies the selected
[Transition and Bridge Architecture](transition-and-bridge-architecture.md)
and the completed Stage 3
[Protocol and Relations Architecture](protocol-and-relations-architecture.md).
Domains own semantic subjects and results. A shared descriptive contract shape
does not create one universal transition type, artifact, capability, checker,
or composition law.

## 1. Partitioning method

The documentation should resemble the semantic architecture, not the source
tree. A durable domain normally has:

- a coherent subject and vocabulary;
- a clear authority boundary;
- inputs and outputs that can be stated independently;
- a lifecycle or change cadence distinct from neighboring subjects;
- a recognizable set of upstream dependencies and downstream consumers; and
- enough internal material to benefit from one navigation entrypoint.

Page length alone is not a reason to split. A short page with a different
authority may need separation; a long, cohesive formal contract may remain one
document.

A bridge is placed with the domain that defines the newly minted semantic
subject, checked result, observation record, assessment, or reliance decision.
That owner must still cite every source authority and may not redefine either
endpoint. Procedural adjacency alone is not a bridge-composition theorem.

## 2. Selected domains

| Domain | Provisional subject | Primary boundary guardrail |
|---|---|---|
| `foundation/` | Constitutional encoding and typed identity, same-regime semantic modules, domain-indexed values, bounded portable functions, typed completed failures, and deterministic evaluation control | Accept only genuinely shared semantics; never become a universal domain algebra, transition runtime, judgment, authority, capability, or resource policy |
| `relations/` | External relation identities and interfaces, artifact interpretation, statement and witness ports, adapters, and correspondence | Keep relation admission, artifact interpretation, correspondence, satisfaction, and source compilation distinct |
| `pir/` | Canonical Protocol semantics and lifecycle, formation, authentication, admission, composition, carrier, obligations, independently identified Protocol Interface and Prover Plan subjects, and admitted source/target subjects | Do not mirror MLIR; fold Interface or Plan identity into Protocol identity; or absorb property analysis, compiler search, endpoint behavior, or realization merely by convenience |
| `analysis/` | Qualified property judgments, exact theorem applicability, and property-specific transport over exact admitted subjects | Do not collect every domain-local predicate, collapse applicability into theorem truth or transport, or turn search failure into a negative judgment |
| `compiler/` | Proposal/search orchestration, constraints, objectives, and selection among already admitted relation-checked candidates | Do not authenticate/admit a target or make a source/target relation true by selecting it |
| `oir/` | Protocol/Interface/role/basis projection, `ProjectionCorrect`, standalone `LocalOirValid`, canonical OIR, endpoint semantics, and abstract execution | Do not infer source coverage from source-free OIR or absorb concrete suppliers and runtime |
| `realization/` | Exact supplier binding, production, `RealizesOir`, deployment preparation/activation, invocation binding/execution, and operational observations | Do not change endpoint semantics; keep portable configuration, live authority, content identity, occurrence identity, and partial effects distinct |
| `evidence/` | Attributable Evidence records, provenance, claim-scoped appraisal, reproduction, and qualified assessment | Record and appraisal do not define upstream meaning or own a consumer's reliance decision |

`project/` governs the whole map. `guides/` provides reader journeys. Neither is
a semantic domain.

`ProtocolInterface` and `ProverPlan` are independently admitted subjects
dependent on one exact Protocol. Stage 3 placed their semantic definitions
under `pir/` because they are typed directly over Protocol-owned ports,
events, objects, and obligations. They are not part of `ProtocolId`, and their
identity or authority cannot be folded into Protocol, OIR, compiler state, or
realization merely to avoid a domain boundary.

### Names intentionally not promoted

- `boundaries/` would collect bridges with different output authorities. Keep
  one project bridge map, but place every exact contract with its result owner.
- `transitions/` would encourage a universal algebra despite different
  subjects, relations, outcomes, capabilities, replay, and effects. Shared
  contract metadata remains descriptive and capability-neutral.
- `carrier/` would separate a representation from the semantic subject it
  carries. Keep PIR carrier rules under PIR, OIR carrier rules under OIR, and
  only identical shared mechanisms under foundation.
- `vocabularies/` would reproduce the current cross-domain catch-all. Place
  concrete entries with the domain that gives them meaning and keep only common
  admission discipline under foundation.
- `composition/` is a project view over several owned operations: Protocol
  construction, checked relation composition, property transport, projection,
  realization, and operational sequencing. It is not one relation.
- `registry/` and `artifacts/` remain candidate foundation subdomains until
  they demonstrate independent subjects and lifecycles.

## 3. Dependency and authority model

`foundation/` supplies common mechanisms but not domain meaning. Authoring and
import form proposals; resolution closes their actual dependency read set;
normalization forms a canonical Protocol candidate; authentication establishes
canonical content and identity; and PIR admission alone mints local Protocol
authority. Persistence, decoding, and reopening lose that capability and
require reauthentication or re-admission before authoritative reuse.

Relation ingress and optional artifact interpretation establish only their own
subjects. Post-admission correspondence then consumes exact Protocol,
Interface, and relation subjects. Analysis produces qualified judgments over
exact subject tuples. A checked Protocol change follows this order:

```text
producer proposes successor
  -> PIR authenticates successor
  -> PIR admits successor
  -> relation owner checks predecessor/successor edge
  -> compiler may select among already admitted checked candidates
```

Selection does not create validity, and an admitted successor may exist even
when one proposed predecessor relation is refuted. Exact theorem applicability
and property-specific transport remain separate Analysis results from the
PIR-owned construction and admission of an FS Protocol; applicability excludes
theorem truth and source-property authority.

OIR projection consumes affirmative PIR-owned purpose-specific source views
over an admitted Protocol and Interface and, for a plan-specialized prover, an
admitted Plan plus affirmative `CheckedPlanRealizes`. The semantic proposition
binds the complete source-view ID; whole source IDs and live handles bind its
validation request and capability but do not enter target identity. Standalone OIR admission
establishes only `LocalOirValid`, not source-relative `ProjectionCorrect`.
Realization consumes admitted OIR and then separates
supplier designation, live provider authority, production, preservation
checking, deployment preparation, activation, invocation binding, and
execution.

Evidence dependencies are one-way:

```text
producer-owned observation
  -> Evidence-owned attributable record
  -> Evidence-policy-qualified assessment
  -> consumer-owned intended-use reliance decision
```

Adding or removing a record, assessment, or reliance decision cannot change a
semantic subject's identity or admission.

These arrows describe semantic production and consumption, not code-package
imports. One implementation may fuse adjacent procedures for usability only
if its types and records preserve every distinct postcondition, authority
effect, refusal, negative result, operational failure, and partial-effect
frontier.

## 4. Bridge ownership

Cross-domain material is not gathered into a generic `boundaries/` directory.
The table deliberately keeps lifecycle, checked change, endpoint operation,
Evidence appraisal, and reliance at their actual authority cuts.

| Transition or bridge | Result owner | Boundary constraint |
|---|---|---|
| Author/import to `AuthoringUnit` | PIR workbench or named frontend owner | Authoring produces a proposal, not Protocol authority |
| Resolve imports/dependencies to `ResolvedAuthoringUnit` | PIR workbench | Bind the immutable snapshot and complete actual read closure; do not retain ambient resolver meaning |
| Normalize to `CanonicalProtocolCandidate` | `pir/` | Form one canonical physical subject; any Interface or Plan candidate remains separately identified |
| Authenticate canonical Protocol candidate | `pir/` | Recompute canonical form, identity, regime, and dependency closure; authentication is not whole-Protocol admission |
| Admit authenticated Protocol | `pir/` | Establish the complete normative predicate and mint only process-local immutable authority |
| Persist admitted Protocol | `pir/` using its carrier contract and Foundation canonical-content rules | Official persistence is admission-gated; Foundation does not define a transport contract, and persisted bytes or references never carry local capability |
| Decode Protocol carrier | `pir/` using its carrier contract | Parsing establishes only bounded carrier structure; Foundation canonical decoding may establish canonical structural form for embedded values, but neither that nor carrier parsing performs typed owner admission or admits Protocol meaning |
| Re-authenticate and re-admit decoded Protocol | `pir/` | Recompute identities and the whole-Protocol predicate under exact regimes and closure; never trust a stored admission marker |
| Reopen admitted Protocol | `pir/` | Produce an independent mutable authoring branch with no output authority; the immutable source remains admitted |
| Form `ProtocolInterface` or `ProverPlan` candidate | `pir/` | Candidate identity is an unauthoritative expectation over the exact Protocol reference |
| Authenticate dependent subject | `pir/` | Independently recompute dependent identity and closure; authentication is not admission or cross-subject coverage |
| Admit dependent subject | `pir/` | Establish its own well-formedness and mint narrow local authority; every consuming edge names the exact admitted ID |
| Check `PlanRealizes` | `pir/` | Relate an admitted Plan to the exact admitted Protocol's abstract obligations; Plan admission alone proves no coverage or completeness |
| Relation-interface ingress | `relations/` | Reader/registry authority and successful parsing do not establish relation truth |
| Optional relation-artifact interpretation | `relations/` | Bind exact bytes and interpretation regime separately from Protocol admission and relation satisfaction |
| Protocol/Interface/relation subjects to `RelationCorrespondsAtInterface` | `relations/` | Protocol remains unchanged; correspondence is not witness satisfaction, Protocol equality, or a property theorem |
| Admitted Protocol to a property-analysis subject and qualified judgment | `analysis/` | PIR owns authenticated facts; unsupported or incomplete analysis is not a negative theorem |
| Produce a successor candidate | Named transform or producer family | Production, structural legality, and target identity do not establish a predecessor/successor relation |
| Authenticate and admit successor | `pir/` | Target admission remains independent of the claimed source relation |
| Check exact predecessor/successor relation | Owner of the named relation | Consume exact admitted subjects, regimes, maps, assumptions, observers, and losses; a negative judgment need not invalidate either subject |
| Select among admitted, checked candidates | `compiler/` | Selection names the candidate domain and objective; winner validity does not establish global optimality |
| Construct and admit an FS Protocol | `pir/` | Three phases keep candidate construction, independent target authentication/admission, and exact A/N construction checking distinct; none establishes theorem applicability or property transport |
| Compose admitted Core views into a target Protocol | `pir/` | Admit the exact composition specification, independently form and admit the target, then recompute the A/N composition result; only A carries resolved maps or context authority, and no structural result implies a property theorem |
| Fresh/FS Protocol pair to theorem applicability | `analysis/` | Bind one exact theorem profile, transcript construction, occurrence/prefix map, regime, and structural premises; exclude theorem truth and source-property authority |
| Source property plus applicability to property-specific transport | `analysis/` | Apply one exact rule under theorem truth, hypotheses, maps, and losses; adjacency or an annotation is insufficient |
| Affirmative checked `EndpointSourceView` plus independently admitted OIR to projected OIR | `oir/` | Plan-sensitive extraction separately requires admitted Plan plus checked `PlanRealizes`; OIR owns distinct `LocalOirValid` and `ProjectionCorrect` results, exact graph coverage, target identity, and refusal |
| Standalone OIR carrier to locally admitted OIR | `oir/` | `LocalOirValid` cannot mint omitted source coverage or restore a serialized projection capability |
| Verifier endpoint to outer relation material (`descend`) | `relations/` | Endpoint identity and verifier semantics remain under `oir/` |
| OIR abstract requirements + target + proposal to exact supplier binding | `realization/` | The selected base path rereads no Plan; portable designation carries no live authority and proves no provider correctness or availability |
| Exact supplier binding + resolver snapshot + provider policy/regime to live provider authority | `realization/` | Resolution mints narrow process-local authority with explicit lifetime, revocation, unavailability, and refusal; serialization erases it |
| OIR + exact binding + admitted live provider authority to realization candidate | `realization/` | Production is effectful and creates content plus an occurrence observation, not a preservation judgment |
| Candidate + exact source/checker basis to `RealizesOir` | `realization/` | `DoesNotRealize`, checker refusal, producer refusal, and operational failure are distinct |
| Admitted realization + resources and policy to deployment binding | `realization/` | Portable configuration cannot change semantics or serve as live deployment authority |
| Admitted deployment binding + operator authority to activation | `realization/` | Activation creates a distinct live occurrence and capability and reports residual partial effects |
| Live deployment + Interface + request/input authority + invocation policy/regime to bound invocation | `realization/` | Bind and attenuate exact authority before execution; malformed input and refusal remain distinct |
| Bound invocation + executor to endpoint result and raw observation | `realization/` | Verifier rejection is a completed semantic result; execution reports run occurrence, protected-event/completion frontier, operational failure, and partial effects separately |
| Raw observation/receipt/comparison to Evidence record | `evidence/` | The producer owns raw meaning; recording establishes attribution and bounded scope, not claim truth |
| Evidence set + policy to `ClaimAssessment` | `evidence/` | Supported, contradicted, insufficient, stale, and indeterminate are policy-qualified outcomes, not reliance |
| Assessment + intended-use policy to `RelianceDecision` | Relying consumer | A decision is consumer-, use-, context-, and time-specific and cannot redefine Evidence or semantic truth |

Owning a bridge does not authorize redefining either endpoint. Every bridge
specification lists its complete inputs and read closure, source authorities,
new postcondition, identity and capability effects, outcome taxonomy, replay
class, composition rules, and non-claims.

The portable-algorithm and supported module-effect boundary remains
three-part:

- PIR owns each identity-bearing semantic citation and its Protocol-facing
  ABI, observation, decision, influence, replay, and terminal laws;
- bounded K3-D OIR owns the corresponding static endpoint graph and derived
  semantic requirements, while Stage 4B owns dynamic endpoint behavior; and
- realization owns concrete supplier designation, live authority, binding,
  and execution.

The selected base Plan has no opaque hole. No domain may silently acquire a
complete contract by convenience.

## 5. Physical layout rules

### Domain first, kind second

The primary path answers “which semantic owner?” A secondary directory may
answer “what kind of page?” when that distinction aids navigation. Possible
local kinds include `spec/`, `architecture/`, `decisions/`, and `guides/`.

Do not create all kinds under every domain. Create a kind directory only with
durable content and a real navigation need. A single page can remain directly
under its domain and declare its kind in the page contract.

### Promote semantic subdomains carefully

Create a nested semantic directory when the topic has an independent subject,
authority, lifecycle, and more than one durable page. The new directory must
include a README and at least one substantive page in the same change.

Likely OIR subdomains are projection, endpoint programs, and abstract
execution. Likely realization subdomains are supplier binding, production,
deployment, and invocation. They are candidates, not directories to pre-create
now.

### Keep public planning bounded

The public tree carries one project roadmap and durable reader-facing design.
Domain work queues, migration scratchpads, review notes, and session plans stay
private. A domain-specific public plan is justified only when it describes a
stable, externally meaningful sequence that cannot be represented in the
global roadmap.

## 6. Split and merge tests

Split a document or domain when one or more of these remain true after editing:

- different sections answer to different authority classes;
- sections change independently and serve different consumers;
- one title hides more than one semantic subject or identity lifecycle;
- a bridge and both endpoint definitions compete inside the same page; or
- current, target, and evidence claims cannot be made unambiguous locally.

Merge or avoid a boundary when:

- the proposed child only mirrors a code namespace;
- it has no independent definitions or consumers;
- it would contain only an index pointing back to its parent;
- separating it would duplicate one normative invariant; or
- its name describes a mechanism used everywhere rather than a bounded
  subject.

## 7. Selected decomposition consequences

The selected authority cuts imply these later document moves:

- split common encoding and admission mechanisms from PIR- and OIR-specific
  carrier semantics;
- distribute vocabulary entries to their semantic owners instead of moving
  the current vocabulary document wholesale into `foundation/`;
- keep Protocol structural judgments such as formation, closure, admission,
  and composition in `pir/`;
- separate property calculus, soundness, knowledge, completeness, assumptions,
  derivations, theorem applicability, and property-specific transport within
  `analysis/`;
- separate transform proposal, target admission, relation checking, and
  compiler selection rather than treating them as one pass result;
- keep endpoint projection and local OIR admission separate from supplier
  binding, production, preservation checking, deployment, invocation, and
  concrete execution;
- keep producer observations distinct from Evidence records and assessments;
  and
- keep global status concise by linking bounded records and qualified
  assessments rather than duplicating their claims.

## 8. Remaining structural candidates

`realization/` remains a single domain because every included subject serves
the implementation lifecycle of a fixed endpoint, while its internal
transitions and authorities are now explicit. `analysis/` names the
property-analysis service without claiming all domain-local judgments. `oir/`
names the canonical semantic subject projection creates, while endpoint is a
role within that domain.

The candidates to reevaluate as exact schemas mature are:

- `pir/` to `protocol/` with PIR as a nested canonical representation, if the
  Protocol semantic subject becomes demonstrably carrier-independent in the
  durable specification;
- the selected `pir/` ownership of `ProtocolInterface` and `ProverPlan`, but
  only if later schemas demonstrate that either subject has a genuinely
  independent domain boundary rather than merely an independent identity and
  lifecycle within the Protocol family;
- an internal split of `realization/`, if bindings, artifacts, deployments,
  invocations, suppliers, and sessions acquire several independent normative
  identities and multiple durable pages;
- `artifacts/` or `representation/`, if common carrier semantics outgrow the
  strict admission rule for `foundation/`; and
- `evidence/` to `assurance/`, if the current name repeatedly attracts
  out-of-scope material or conflicts with Evidence as a local record kind.

Promotion follows demonstrated subject and authority boundaries, not code
layout or anticipated page count.
