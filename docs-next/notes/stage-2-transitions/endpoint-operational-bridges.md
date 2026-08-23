# Endpoint, operational, and evidence bridges

> **Document kind:** Temporary Stage 2 research note
> **Document state:** Completed Stage 2 research input; selected refinements
> are reflected in the target catalog and convergence record
> **Authority:** None. This page reconstructs current contracts and proposes
> transition boundaries for convergence. It does not define OIR semantics,
> admit a realization, establish conformance, select an evidence policy, or
> authorize implementation work.
> **Scope:** `ProtocolInterface` and optional `ProverPlan` consumption, OIR
> projection and coverage, supplier binding, realization, deployment,
> invocation, observation, evidence recording, appraisal, and reliance.
> **Later owners:** Stage 4B completes OIR and Realization; Stage 6 completes
> Evidence. This page deliberately stops at their ingress and authority
> boundaries.
> **Method:** Static inspection of current specifications, implementation, and
> tests; target modeling under Stage 1; bounded comparison with primary
> provenance and appraisal specifications. No test was executed in this pass.
> **Disposition:** Reviewed conclusions have been reconciled and absorbed into
> `oir/`, `realization/`, `evidence/`, and the relying owners. Retain this
> research detail until the temporary-package deletion gate.

## 1. Result in one view

The endpoint-to-reliance path should not be one lowering pipeline. It contains
different relations and different kinds of authority:

```text
AdmittedProtocol + AdmittedProtocolInterface + EndpointRole
                 + explicit ProjectionBasis
        |
        | ProjectEndpoint / CheckProjection
        | establishes ProjectionCorrect
        v
canonical OIR subject + source-relative ProjectedOir capability
        |
        | FormSupplierBinding
        | establishes exact immutable requirement closure
        v
SupplierBinding subject
        |
        | ResolveSupplierAuthority
        | establishes current provider availability and authority
        v
process-local admitted provider capability
        |
        | ProduceRealization                   effectful
        v
realization candidate + artifact content + emission observation
        |
        | CheckRealization
        | establishes a named OIR-preservation relation
        v
AdmittedRealization capability
        |
        | PrepareDeployment / ActivateDeployment       effectful at activation
        v
DeploymentBinding + live DeploymentCapability + observation
        |
        | BindInvocation / InvokeEndpoint              effectful at invocation
        v
typed endpoint result + raw operational observation
        |
        | RecordEvidence
        v
EvidenceRecord
        |
        | AppraiseEvidence under EvidencePolicy
        v
ClaimAssessment
        |
        | DecideReliance under IntendedUsePolicy
        v
use-specific RelianceDecision
```

The proposed skeleton has seven central rules:

1. Projection is closed over an admitted Protocol, an admitted dependent
   Interface, a role, and a tagged plan basis. Labels or plans may not arrive
   through retained carrier or compiler state.
2. `LocalOirValid(O)` and
   `ProjectionCorrect(P, I, role, basis, O)` are different judgments. A
   source-free OIR can establish only the former without source-bound evidence.
3. A `ProverPlan` is optional only by an explicit tagged choice. It affects OIR
   identity exactly when projection reads it; otherwise any later plan use is
   an explicit Realization input.
4. A supplier binding is an exact closed designation, not capability matching
   or negotiation. It establishes that every requirement has one compatible
   provider, not that provider code is correct.
5. Producing bytes, deploying resources, and running an endpoint are effectful
   activities. Their observations do not themselves establish semantic
   preservation or evidence adequacy.
6. A verifier rejection is a successfully produced semantic result. It is not
   malformed input, supplier refusal, operational failure, or policy denial. A
   prover produces bytes or fails; it never produces a verifier verdict.
7. Evidence recording, evidence appraisal, and reliance are three separate
   transitions. Neither evidence nor reliance can flow backward and redefine
   Protocol, Interface, OIR, realization, or run meaning.

This favors domain-owned typed contracts over a universal transition record.
Some transitions may later share mechanisms, but their relations, outcomes,
capabilities, and policy owners remain distinct.

## 2. Scope discipline and fixed Stage 1 constraints

This note consumes the selected
[Protocol IR Architecture](../../project/protocol-ir-architecture.md) without
reopening it. In particular:

- `Protocol = InteractiveCore + ChallengeInterpretation` fixes complete
  verifier-visible behavior before endpoint realization;
- `ProtocolInterfaceId` is a dependent identity over `ProtocolId` and owns only
  an external callable contract that decodes to the already-fixed semantics;
- `ProverPlanId` is a separate dependent identity over `ProtocolId` and may not
  change proof events, challenge behavior, checks, proof ABI, or accepted
  language;
- OIR is a new endpoint subject derived from an exact Interface and role;
- `TRANSCRIPT`, `WIRE`, `PUBLIC`, `CHECK`, `ARTIFACT`, `CLAIM`, and `TERMINAL`
  observations are protected;
- semantic regimes are typed and explicit;
- an admitted capability is process-local authority, not a serialized flag;
  and
- source-free OIR cannot recover omitted source obligations and therefore
  cannot establish source-relative projection coverage by itself.

The required durable endpoint reference begins as:

```text
EndpointContractRef = (ProtocolId, ProtocolInterfaceId, EndpointRole)
```

This page adds only transition-level types around that reference. It does not
select the complete Interface schema, ProverPlan schema, OIR grammar, target
ABI vocabulary, provider API, deployment topology, evidence record encoding,
or policy language. Capitalized type names introduced below are provisional
roles, not selected public classes, operations, or serialized schemas.

### 2.1 Categories that must remain separate

The following terms are used consistently throughout the page:

| Category | Meaning |
|---|---|
| Subject | Immutable semantic or configuration content with a stable identity under a typed regime |
| Artifact | A concrete carrier or generated object; content authentication does not automatically admit its semantics |
| Capability | Process-local authority to perform a bounded operation over an already checked object or live resource |
| Judgment | A checked proposition with exact subjects, assumptions, and a named relation |
| Result | The typed semantic output of one endpoint execution, such as verifier accept or a named reject class |
| Observation | What one attributed activity reported or exposed; not yet evidence for a claim merely by existing |
| Evidence record | A bounded, attributable record binding observations or receipts to a claim and procedure |
| Assessment | An evidence-policy-qualified conclusion, which may be positive, negative, insufficient, or indeterminate |
| Reliance decision | A consumer-owned decision for one intended use, context, scope, and time |
| Refusal | A transition did not attempt or could not establish its contract for a well-formed request |
| Operational failure | An effectful attempt failed; partial effects may remain and must be reported |

## 3. Current architecture reconstruction

The current system already contains several of the necessary distinctions,
but its implemented and architecture-only portions must be reported
separately.

### 3.1 Current documentation contracts

The current normative [Endpoints](../../../docs/spec/endpoints.md) and
[Boundaries](../../../docs/spec/boundaries.md) specifications establish this
contract surface:

- `project` consumes an opaque admitted sealed-PIR capability and an endpoint
  kind and produces one `OIRArtifact`;
- projection compares emitted `src` positions with the source obligation set
  and establishes current `COV_realized` while both source and target are in
  scope;
- OIR has its own canonical identity, endpoint ABI, linear sponge/stream/handle
  resources, protected events, verifier and prover frames, and local validity;
- standalone OIR validation cannot establish projector origin or exhaustive
  source coverage;
- an execution profile supplies exact codec, sponge, sampling, check, and hole
  implementations, with missing or mismatched supply classified as profile
  incompatibility rather than verifier rejection;
- verifier execution yields accept or a named reject class, while prover
  execution yields proof bytes without an accept verdict; and
- a prover run record is required in the specification to bind the sealed PIR,
  prover OIR, execution profile, supplier digests, and opaque-input digests,
  although the general record type is not yet a public implemented boundary.

The current [Target Architecture](../../../docs/architecture.md) then sketches
supplier binding, emitted artifacts, deployment bindings, invocation bindings,
run records, evidence, and consumer admission as different roles. Its
[Current Status](../../../docs/status.md) reports verifier/prover OIR,
reference execution, and Rust emission as partial, while generalized evidence
admission and wider targets/deployment remain future work.

### 3.2 Current implementation and test correspondence

The implementation trace gives the following bounded evidence:

- [`Projection.h`](../../../include/zkc/Dialect/Pir/Transforms/Projection.h)
  exposes `projectArtifact(AdmittedPirArtifact, EndpointKind)` and returns a
  copyable `ProjectedOirArtifact`. Its private shared storage retains the
  reopened source backing beside the projected OIR, which is a concrete
  process-local paired-capability pattern.
- [`PirProject.cpp`](../../../lib/Dialect/Pir/Transforms/PirProject.cpp) clones
  the admitted source internally, reads the retained Protocol environment,
  projects one role, checks exact source-position coverage, and computes OIR
  identity. Its separate `admitOirArtifact` path reauthenticates standalone OIR
  and re-resolves locally cited check and hole contracts, but has no source
  obligation set from which to recover coverage.
- [`ExecutionProfile.h`](../../../include/zkc/Interpreter/ExecutionProfile.h)
  models a closed in-process supplier set and explicitly treats the selected
  profile as a run fact rather than OIR artifact identity.
- [`Interpreter.h`](../../../include/zkc/Interpreter/Interpreter.h) and
  [`Interpreter.cpp`](../../../lib/Interpreter/Interpreter.cpp) keep verifier
  verdicts, prover outputs, missing suppliers, fill defects, and wrong endpoint
  roles on separate result or error paths.
- [`zkc-emit`](../../../emit/zkc-emit/src/main.rs) is a source-free OIR
  consumer. It recomputes OIR identity, resolves an explicit binding, gates
  supplier requirements, and emits a standalone Rust crate. The emitted crate
  carries OIR and source identities, binding provenance, emitter version, and
  optional conformance vectors. Double-emission tests establish byte
  determinism for the exercised inputs.

Representative tests preserve the current boundary distinctions:

| Evidence | What it exercises | What it does not establish |
|---|---|---|
| [`Artifact/project.test`](../../../test/Artifact/project.test) | Persisted PIR admission, projection of both roles, and one reference round trip | A target Interface/Plan schema or generalized realization |
| [`pir-project.mlir`](../../../test/Transforms/pir-project.mlir) and related projection tests | Embedded source positions, source-relative exact coverage, identity refusal, unsupported projection | Source-free coverage or a portable projection proof |
| [`standalone-admission.test`](../../../test/Oir/standalone-admission.test) | Local OIR identity and cited check/hole contract re-admission | Origin or exhaustive Protocol obligation coverage |
| [`profile-refusals.test`](../../../test/Oir/profile-refusals.test) | Missing/mismatched supplier refusal distinct from a verdict | Supplier implementation correctness |
| [`prover-round-trip.test`](../../../test/Oir/prover-round-trip.test) | Prover output, verifier result, challenge parity, and typed refusal/defect distinctions | General completeness or universal conformance |
| [`emit-schnorr.test`](../../../test/Emit/emit-schnorr.test), [`emit-schnorr-prover.test`](../../../test/Emit/emit-schnorr-prover.test), and [`emit-document-gates.test`](../../../test/Emit/emit-document-gates.test) | Source-free document checks, explicit binding gates, generated behavior for fixtures, and deterministic output | A separately checked general `RealizesOir` judgment, deployment, or reliance |
| [`plonky3-replay.test`](../../../test/Evidence/plonky3-replay.test) and neighboring evaluation assets | Exact pinned replay and mutation observations | A generalized `EvidenceRecord`, appraisal policy, or release decision |

No generalized `EvidenceRecord`, `ClaimAssessment`, `RelianceDecision`,
`DeploymentBinding`, or invocation-capability transition was found in the
surveyed implementation. That is a scope statement, not a defect finding: the
status and roadmap already classify those surfaces as future work.

### 3.3 Current-to-Stage-1 seam

The current projection engine obtains statement and witness labels from the
PIR carrier, while current OIR identity treats them as ABI-significant. Stage
1 deliberately removes this hidden input from the target contract:

```text
current correspondence:
  AdmittedPirArtifact(with retained carrier labels and environment) + role
    -> ProjectedOirArtifact

Stage 1 target closure:
  AdmittedProtocol + AdmittedProtocolInterface + role + ProjectionBasis
    -> ProjectedOir
```

The target does not discard current behavior. It reclassifies ABI labels,
containers, and external encodings into the separately identified Interface,
and requires any plan-sensitive prover construction to be explicit. Current
`ProjectedOirArtifact` already demonstrates the useful capability rule: keep
the source and target paired in process when the source-relative judgment is
needed, and do not pretend serialized OIR bytes retain that authority.

## 4. Target transition graph and dataflow rules

The target graph uses relation-specific transitions. The signatures below are
type skeletons, not final APIs or wire formats.

```text
AdmittedProtocol[P]
AdmittedProtocolInterface[I -> P]
EndpointRole
ProjectionBasis =
  InterfaceOnly
  | InterfaceAndPlan(
      AdmittedProverPlan[L -> P],
      CheckedPlanRealizes[L -> P])
OirSemanticRegime
        |
        v
ProjectEndpoint / CheckProjection
        |
        +--> ProjectionProductionRefusal or ProjectionCheckRefusal
        +--> ProjectionIncorrect                  checker only
        `--> ProjectedOirCapability[P, I, role, basis, O]
               exposes canonical OirArtifact[O]
               carries ProjectionCorrect(P, I, role, basis, O)

OirArtifact[O] + local dependency preimages + OirSemanticRegime
        |
        `--> AdmitOirLocal
               -> AdmittedOir[O, LocalAdmissionBasis]
               -> LocalOirValid(O), never source coverage by implication

AdmittedOir[O] + explicit realization-plan basis + TargetContract
BindingProposal + SupplierBindingRegime
        |
        `--> FormSupplierBinding
               -> SupplierBinding[B -> O]

AdmittedOir[O] + SupplierBinding[B] + exact SupplierResolver snapshot
ProviderAdmissionPolicy + ProviderRegime
        |
        `--> ResolveSupplierAuthority
               -> AdmittedSupplierAuthority[B -> O]

AdmittedOir[O] + SupplierBinding[B] + AdmittedSupplierAuthority[B]
RealizationRequest + exact toolchain closure
        |
        `--> ProduceRealization
               -> RealizationCandidate[R, ArtifactContent[A]]
                  + EmissionObservation
                    |
                    `--> CheckRealization
                           +--> DoesNotRealize
                           +--> RealizationCheckRefusal
                           `--> AdmittedRealization[R]

AdmittedRealization[R] + DeploymentSpecification + resources + policy
        |
        `--> PrepareDeployment
               -> DeploymentBinding[D -> R]
                  + AdmittedDeploymentBinding[D -> R]
                 |
                 `--> ActivateDeployment
                        -> live DeploymentCapability[J] + observation

DeploymentCapability[J] + AdmittedProtocolInterface[I -> P]
InvocationRequest + input capabilities
        |
        `--> BindInvocation -> BoundInvocationCapability[U]
                 |
                 `--> InvokeEndpoint
                        -> typed result + RawOperationalObservation

RawObservation or external Receipt + ClaimRef + recorder/issuer + procedure
        |
        `--> RecordEvidence -> EvidenceRecord[E]
                 |
                 `--> AppraiseEvidence(EvidencePolicy)
                        -> ClaimAssessment[C]
                              |
                              `--> DecideReliance(IntendedUsePolicy)
                                     -> RelianceDecision[Q]
```

Three closure rules apply to every arrow:

1. If changing an unlisted value can change the result, that value is an input.
2. A broad resolver or catalog may be used for lookup, but the admitted result
   records the exact cited/resolved closure; unrelated entries cannot affect a
   recheck.
3. A result may cite its production policy or procedure as provenance without
   making that policy part of semantic identity when the result is completely
   self-describing. If the policy continues to affect interpretation, it is an
   identified dependency instead.

### 4.1 Required read closures

| Transition | Complete result-affecting read closure | Material explicitly outside that closure |
|---|---|---|
| `ProjectEndpoint` | Admitted Protocol semantic closure; admitted Interface closure; role; tagged plan and plan-coverage basis when selected; OIR regime; exact cited endpoint contracts | Author labels not owned by Interface, compiler search state, unrelated registry entries, suppliers, deployment |
| `AdmitOirLocal` | Exact OIR carrier/content; expected ID if supplied; OIR regime; every cited preimage needed for local interpretation | Source obligations, projector state, unrelated resolver entries, source-relative coverage |
| `FormSupplierBinding` | Admitted OIR requirement closure; explicit below-OIR plan basis if selected; target contract; exact proposal and provider designations; binding regime | Unselected providers, ambient ranking, current provider availability, compiler state, deployment resources |
| `ResolveSupplierAuthority` | Admitted OIR; exact SupplierBinding; immutable resolver snapshot; provider policy/regime; exact provider descriptions and current capabilities | Unselected providers, ambient ranking, compiler state, deployment resources |
| `ProduceRealization` | OIR; exact binding; admitted provider authority; realization request; exact provider artifacts/capabilities; target and toolchain closure; declared output context | Broad provider catalogs, undeclared build inputs, deployment/invocation state |
| `CheckRealization` | OIR; binding; exact candidate content and manifest; checker/regime; every target dependency the selected relation reads | Producer success flag, unrelated tests/evidence, later deployment outcomes |
| `PrepareDeployment` | Admitted realization; topology/resource specification; exact resource snapshot or authorized late-binding set; deployment policy/regime | New semantic choices, unrelated resources, future invocation values |
| `ActivateDeployment` | Admitted deployment binding; operator authority; activation request; current external resource state declared by the contract | Unlisted services/resources and future caller policy |
| `BindInvocation` | Live deployment capability; admitted Interface; exact request; input/provider capabilities; invocation policy/regime; current late-bound resource versions | Ambient providers, unauthorized setup, evidence or prior run success |
| `InvokeEndpoint` | Bound invocation; executor capability; declared live runtime state | New Interface, supplier, or semantic choices after binding |
| `RecordEvidence` | Exact observation/receipt; claim/subjects; issuer/recorder; procedure; environment/pins; Evidence regime; disclosure scope | Unrecorded observations and inferred broader claims |
| `AppraiseEvidence` | Exact records; claim; Evidence policy/version; reference values; trust anchors; context and freshness basis | Consumer intended-use policy and omitted evidence |
| `DecideReliance` | Exact assessments; consumer/use policy; consumer context, current state, trust anchors, time | Authority to rewrite assessments, records, observations, or semantic subjects |

Each typed regime is read only by the transition whose interpretation it
governs. A Protocol regime does not substitute for Interface, OIR,
Realization, Deployment, Invocation, or Evidence regimes. A result that must be
compared or independently replayed across processes cites the stable regime
reference rather than relying on process-global defaults.

## 5. Interface- and plan-closed OIR projection

### 5.1 Source, target, owner, and relation

The proposed primary transition is:

```text
ProjectEndpoint(
  source: AdmittedProtocol[P],
  interface: AdmittedProtocolInterface[I -> P],
  role: EndpointRole,
  basis: ProjectionBasis,
  oir_regime: OirSemanticRegime,
  cited_dependency_closure
) -> ProjectedOirCapability[P, I, role, basis, O]
  | ProjectionProductionRefusal
```

An alternative producer may propose a candidate and invoke the same
relation-specific checker:

```text
CheckProjection(P, I, role, basis, candidate_O) ->
    ProjectionCorrect(ProjectedOirCapability[P, I, role, basis, O])
  | ProjectionIncorrect(typed mismatch or counterexample)
  | ProjectionCheckRefusal
```

`ProjectionIncorrect` is a successful negative correspondence judgment about
the candidate. `ProjectionCheckRefusal` means the checker could not apply. A
combined direct projector may expose a simpler accepted-result/refusal API,
but its internal candidate failure must not be misreported as an invalid
source Protocol.

The Protocol/PIR owner defines the source Protocol and abstract endpoint
obligations. The Interface owner defines the external mapping. The optional
plan owner defines the admitted ProverPlan and its Protocol dependency. OIR
owns the bridge, exact coverage, target program, target identity, and
projection refusal. Realization is a relying consumer and cannot redefine the
relation.

Successful projection establishes the named judgment:

```text
ProjectionCorrect(P, I, role, basis, O)
```

At Stage 2 resolution, that judgment contains at least these facets:

- the Interface depends on exactly `P`, and every external field consumed by
  projection comes from `I` rather than carrier-only labels;
- every role-relevant Protocol obligation is represented by the target
  endpoint according to a total source map;
- every target protected effect is justified by a Protocol obligation,
  Interface boundary action, or explicitly permitted target-local action;
- protected order, causal dependencies, value classes, counts, framing,
  challenge behavior, checks, claim flow, failure classes, and terminal
  behavior are preserved under the exact OIR relation selected later;
- the external statement/proof/witness ABI realizes the Interface mapping
  without changing Protocol semantics;
- source coverage has no omission, duplication, unauthorized reordering, or
  target event masquerading as a source obligation; and
- when the basis is plan-specialized, the plan depends on exactly `P`, covers
  the relevant abstract prover obligations, and changes no verifier-visible
  behavior.

This judgment does **not** establish relation truth, soundness, completeness,
zero knowledge, supplier correctness, concrete execution, target
preservation, deployment suitability, or consumer reliance.

### 5.2 Explicit plan basis

An untyped optional `ProverPlanId` is too easy to omit from cache keys or read
ambiently. The target uses a tagged basis:

```text
ProjectionBasis =
    InterfaceOnly
  | InterfaceAndPlan(
      AdmittedProverPlan[L -> P],
      CheckedPlanRealizes[L -> P])
```

`CheckedPlanRealizes` is a local capability over the separately checked
`PlanRealizes` structural judgment that the plan covers the exact Protocol
obligations used here. A plan's authenticated content, admission, and dependent
`ProverPlanId` do not prove that judgment by themselves.
An implementation may recompute coverage inside projection instead of passing
a separate capability, but successful projection must retain the exact
coverage basis it used.

The role rules are:

| Role and shape | Permitted basis | Consequence |
|---|---|---|
| Verifier | `InterfaceOnly` | A ProverPlan cannot affect verifier OIR. Supplying one is a superfluous-input refusal, not a hidden variation. |
| Generic prover obligation skeleton | `InterfaceOnly` | OIR exposes Protocol-owned abstract holes and requirements; the plan may be consumed explicitly below OIR if realization needs it. |
| Plan-specialized prover program | `InterfaceAndPlan` | `ProverPlanId` enters the projection dependency and OIR identity because projection reads plan content. |

There are therefore two valid placements for plan information, to be selected
per field during Stage 4B co-design:

```text
plan changes canonical prover OIR
  -> consume it in projection and commit ProverPlanId in OirId

plan only chooses scheduling, buffering, algorithms, or suppliers below OIR
  -> keep OIR plan-independent and pass the admitted plan explicitly to
     supplier binding or realization
```

The same plan fact must not appear first as ambient state at both boundaries.
The obligation/plan ledger should assign each field to the earliest transition
that reads it. If a supposed plan field changes a proof message, distribution,
transcript action, external proof ABI, check, or accepted language, the input
is outside ProverPlan authority and denotes a different Protocol.

### 5.3 Source-relative coverage versus local OIR validity

The target names two independent relations:

```text
LocalOirValid(O, OirSemanticRegime, local_dependency_closure)

ProjectionCorrect(P, I, role, basis, O)
```

`LocalOirValid` may check canonical target identity, target grammar, role frame,
entry ABI, linear resources, local references, contract schemas, and local
protected-effect well-formedness. It has no quantifier over the source
Protocol obligation set.

`ProjectionCorrect` has both source and target and can establish exact
coverage. Embedded source positions or an authenticated source digest are
useful witness data, but neither can reveal an omitted obligation. Therefore:

```text
AdmitOirLocal(serialized_OIR)  !=  re-establish ProjectionCorrect
```

A source-free consumer must report source coverage as `unknown` unless it
receives one of:

- the admitted source Protocol and Interface and rechecks projection;
- a process-local paired projection capability whose source remains live; or
- a later durable source-bound projection record/certificate sufficient for an
  identified independent checker.

The default target remains direct checked projection plus a paired process
capability. A portable `ProjectionRecord` is not introduced merely because it
is conceivable. It becomes justified only when a named cross-process consumer
cannot cheaply or acceptably obtain and admit the source. Such a record would
need to bind the full source obligation commitment, Interface, role, optional
plan and its coverage basis, target OIR, checker regime, dependency closure,
and claimed coverage relation; an OIR's own ID and source map are not a
certificate.

### 5.4 OIR identity dependency

Stage 1 already requires OIR to commit to the endpoint reference and canonical
OIR content. The minimum target dependency shape is:

```text
OirId = H(
  "zkc/oir",
  OirSemanticRegimeId,
  EndpointContractRef(P, I, role),
  ProjectionBasisTag,
  ProverPlanId if ProjectionBasisTag == InterfaceAndPlan,
  CanonicalEncode(OirSubject))
```

This is an identity dependency sketch, not the Stage 4B byte grammar. The
explicit basis tag prevents a generic prover skeleton and an accidentally
plan-omitted specialized skeleton from sharing an interpretation. If the OIR
subject already carries a field, the eventual encoder may avoid literal
duplication while retaining the same dependency.

Changes to carrier transport bytes, source locations, projector release, or
diagnostic presentation do not change `OirId` when they decode to the same OIR
subject under the same regime. A different Interface, role, plan-specialized
basis, semantic regime, or canonical endpoint behavior does. Comparisons that
want to relate distinct OIR identities use a named relation such as `TraceEq`
or `TraceRefines`; they do not erase dependencies from identity to force
equality.

### 5.5 Projection capability and replay

`ProjectedOirCapability` is the authority-bearing success result. It should:

- retain immutable access to the exact admitted source, Interface, optional
  plan, and target OIR or to a checker-owned equivalent closure;
- authorize only projection-relative queries and extraction of portable OIR
  bytes;
- preserve the exact semantic regimes and admission bases used for the check;
- define copy/alias/concurrency behavior explicitly; and
- degrade on serialization to an unauthoritative OIR artifact plus ordinary
  references, unless a separate durable record is emitted.

Current copyable `ProjectedOirArtifact` is a useful implementation precedent,
not a requirement that every later capability be copyable. A projection
capability refers only to immutable subjects, so shared read-only aliases are
plausible. Deployment and invocation capabilities have different lifetime and
effect semantics and should not inherit that choice.

### 5.6 Projection outcomes

Projection needs a typed refusal vocabulary at least as precise as:

| Outcome | Meaning | Source status |
|---|---|---|
| malformed or unauthenticated input | A required carrier, subject, dependency, or stored identity could not be interpreted/admitted | No conclusion about a different valid source |
| dependency mismatch | Interface or plan cites another Protocol, or regimes/dependencies do not agree | Inputs remain independently meaningful; this join is invalid |
| unsupported endpoint role or source obligation | OIR cannot express the requested endpoint under this regime | Protocol remains admitted |
| Interface incompatibility | The proposed external mapping changes or fails to cover fixed Protocol semantics | Protocol remains admitted; Interface or join refuses |
| plan incompatibility | The plan is not admitted, does not cover its obligations, or crosses the verifier-visible boundary | Protocol remains admitted; no completeness conclusion |
| coverage mismatch | Source and target protected obligations do not correspond exactly | Candidate OIR is not admitted as this projection |
| checker unavailable or policy refusal | The requested checker/regime is unavailable or disallowed | `ProjectionCorrect` is not established |

An unsupported or refused projection is never a negative soundness judgment,
an invalid Protocol, a verifier rejection, or an operational failure.

## 6. Standalone OIR admission

Portable OIR needs a local admission transition even when source-relative
authority is unavailable:

```text
AdmitOirLocal(
  carrier: OirArtifactCarrier,
  oir_regime: OirSemanticRegime,
  expected_oir_id?,
  local_dependency_resolver
) -> AdmittedOir[O, LocalAdmissionBasis]
  | OirAdmissionRefusal
```

The transition authenticates the carrier, reconstructs the canonical OIR
subject, validates `OirId`, resolves every dependency needed to interpret its
own local operations and ABI, and establishes `LocalOirValid`. It may retain a
minimal immutable resolved closure for later consumers. Uncited resolver
entries cannot affect the result.

If local OIR is self-contained except for identified dependency references,
the admitted result can validate their reference shape without claiming the
source Interface mapping. If local semantics require a cited Interface or
contract preimage, that exact preimage is part of the local admission basis.
Neither case recovers Protocol obligation coverage.

Serialization discards the capability. A new process re-runs carrier
authentication, dependency resolution, and local admission under an explicit
OIR regime. It must not deserialize an `admitted: true` bit or infer
`ProjectionCorrect` from an embedded source ID.

## 7. Supplier binding

### 7.1 Boundary purpose

OIR owns abstract endpoint requirements; supplier binding chooses exact
implementations for them. The target boundary is deliberately narrower than a
general capability matcher:

```text
FormSupplierBinding(
  endpoint: AdmittedOir[O],
  plan_basis: RealizationPlanBasis,
  target: TargetContract,
  proposal: SupplierBindingProposal,
  binding_regime: SupplierBindingRegime
) -> SupplierBinding[B -> O]
  | SupplierBindingRefusal

ResolveSupplierAuthority(
  endpoint: AdmittedOir[O],
  binding: SupplierBinding[B -> O],
  resolver: SupplierResolverSnapshot,
  policy: ProviderAdmissionPolicy,
  provider_regime: ProviderRegime
) -> AdmittedSupplierAuthority[B -> O]
  | SupplierAuthorityRefusal

RealizationPlanBasis =
    OirComplete
  | OirAndPlan(
      AdmittedProverPlan[L -> ProtocolOf(O)],
      CheckedPlanRealizes[L -> ProtocolOf(O)])
```

The first success produces portable immutable `SupplierBinding[B]`
configuration. The second independently resolves it into the process-local
`AdmittedSupplierAuthority[B -> O]`. An implementation may fuse the traversals,
but their postconditions and refusal surfaces remain distinct.

`OirAndPlan` is permitted only when the plan remains below OIR and the binding
or realizer actually reads it. A plan already specialized into OIR may be cited
for provenance, but may not be silently reinterpreted through a second ambient
copy. The plan ledger must make this choice explicit.

The OIR/plan owners define the requirement set. Realization owns the binding
subject, its checker, and its admission capability. The proposal names exactly
one implementation for every required codec, transcript construction,
sampling operation, algebra or kernel contract, check adapter, hole fill,
runtime service, or other Stage 4B requirement. The proposal is designation,
not search: ranking and optimization belong to an earlier explicit planner or
Compiler judgment if ever needed.

### 7.2 Successful postcondition and non-claims

Successful binding establishes:

```text
RequirementClosureExact(O, plan_basis, target, B)
ProviderAbiCompatible(B)
```

Successful provider-authority resolution separately establishes
`ProviderReferencesResolved(B, SupplierResolverSnapshot)` and the exact local
authority admitted under the provider policy and regime.

At minimum:

- every requirement has exactly one binding entry;
- no binding entry is superfluous to the closed requirement set;
- the entry identifies the exact required contract and concrete provider
  implementation, ABI, limits, target properties, and any content or release
  reference required for resolution;
- every cited provider preimage resolves under the explicit snapshot;
- provider and target capabilities agree with the declared boundary; and
- the normalized binding is independent of unrelated resolver entries.

The closed binding object should reject superfluous entries, while the broader
supplier catalog may contain any number of irrelevant providers. This avoids
making catalog growth change an exact binding and keeps the binding's claim
surface honest.

Binding does not establish provider algorithm correctness, protected-trace
preservation, generated-artifact correctness, availability at deployment,
performance, relation satisfaction, or endpoint acceptance. A provider's
self-declared contract is an input to checking, not proof of its
implementation.

### 7.3 Binding identity and capability

The minimum identity dependency is:

```text
SupplierBindingId = H(
  "zkc/supplier-binding",
  SupplierBindingRegimeId,
  OirId,
  RealizationPlanBasisTag,
  ProverPlanId if RealizationPlanBasisTag == OirAndPlan,
  TargetContractId,
  CanonicalEncode(exact binding entries and resolved provider identities))
```

The complete catalog snapshot need not enter identity when the explicit
binding result is self-contained and unrelated catalog entries cannot affect
admission. The exact snapshot and admission procedure remain in the admission
basis or provenance. If lookup rules themselves affect interpretation after
admission, their identified form becomes a semantic dependency instead.

The portable `SupplierBinding` is configuration. It does not grant access to
libraries, devices, services, keys, or processes. The process-local
`AdmittedSupplierAuthority` additionally retains resolved immutable provider
descriptions or narrow provider capabilities and authorizes only realization
of the exact OIR/plan/target tuple. Serialization returns to configuration
bytes and references; a new process must re-resolve and re-admit them.

### 7.4 Refusal surface

Binding refusals include:

- malformed or unauthenticated OIR, plan, target, proposal, or provider
  description;
- Protocol or plan dependency mismatch;
- missing, duplicate, or superfluous binding entries;
- contract, ABI, type, count, limit, construction digest, target, or semantic
  parameter mismatch;
- unresolved or changed provider preimage;
- a well-formed OIR feature unsupported by the requested target;
- a provider capability unavailable at the required binding time; and
- explicit selection or local policy refusal.

None is a verifier verdict, proof rejection, Protocol invalidation, provider
defect observed during execution, or evidence appraisal.

## 8. Realization and emission

### 8.1 Separate production from preservation checking

Emission is a production activity. It may produce deterministic bytes and
still not prove those bytes realize OIR. The clean target therefore separates
two logical transitions even if one command initially performs both:

```text
ProduceRealization(
  endpoint: AdmittedOir[O],
  binding: SupplierBinding[B -> O],
  providers: AdmittedSupplierAuthority[B -> O],
  request: RealizationRequest,
  provider_closure: ExactProviderClosure,
  toolchain_closure: ExactToolchainClosure
) -> RealizationCandidate[R, ArtifactContent[A]] + EmissionObservation
  | RealizationProductionRefusal
  | OperationalFailure
  | PartialEffectFailure

CheckRealization(
  endpoint: AdmittedOir[O],
  binding: SupplierBinding[B -> O],
  candidate: RealizationCandidate[R, ArtifactContent[A]],
  checker: RealizationChecker,
  realization_regime: RealizationRegime
) -> RealizationCheckResult =
    Realizes(AdmittedRealization[R, RealizesOir(O, B, R)])
  | DoesNotRealize(typed mismatch or counterexample)
  | RealizationCheckRefusal
```

The exact `RealizesOir` relation is Stage 4B work. Stage 2 requires it to name
at least:

- the exact source OIR, role, Interface, supplier binding, target contract,
  and artifact/package;
- the protected observation classes covered;
- endpoint ABI and result-taxonomy preservation;
- transcript, proof-stream, public-binding, check, artifact, claim, and
  terminal correspondence at the selected grade;
- any permitted refinement of non-observable scheduling, layout, batching, or
  performance behavior;
- unsupported modes and open obligations; and
- the trusted producer, checker, toolchain, provider, runtime, or proof
  assumptions that remain.

A generated manifest, matching ID, successful build, vector corpus, or
producer assertion can be input to checking or later evidence. None proves its
own correspondence by being packaged with the artifact.

`DoesNotRealize` is a successful negative judgment about one candidate under
the named checker relation. It does not invalidate OIR, the supplier binding,
or other candidates. `RealizationCheckRefusal` means the checker could not
interpret or decide the requested relation. Production refusal, checker
refusal, negative correspondence, and effectful production failure remain four
different outcomes.

### 8.2 Checker alternatives kept open

Stage 4B should select among these per target rather than impose one universal
mechanism:

| Model | Appropriate when | Stage 2 boundary rule |
|---|---|---|
| Direct trusted emitter | The producer is intentionally in the trusted semantic boundary and no smaller checker is practical | State the trusted component and exact relation; do not call producer success independent validation |
| Producer plus translation validator | Candidate generation is complex but source/target correspondence is locally checkable | Validator consumes exact OIR, binding, candidate, regime, and dependency closure |
| Portable certificate or witness | A named independent consumer justifies exchange or caching | Identify source, target, claim, checker regime, dependencies, replay, and invalidation |
| Differential or conformance evidence | Exact behavior can be exercised but exhaustive preservation is not established | Keep it as bounded Evidence; do not silently upgrade it to `RealizesOir` |
| Direct interpreter realization | OIR is executed without emitting a standalone package | Model the admitted interpreter/profile pair as a concrete realization capability, not as OIR semantics itself |

Current `zkc-emit` is strong implementation evidence for exact binding gates,
source-free local validation, deterministic production, and tested behavioral
correspondence on fixtures. This Stage 2 model does not retroactively assign it
a general preservation grade.

### 8.3 Realized artifact identity

The target needs to keep five notions apart:

```text
OirId                       endpoint semantic subject
SupplierBindingId           exact implementation designation
ArtifactContentId            exact produced bytes/package content
RealizationId                OIR/binding/target-qualified realized endpoint
EmissionOccurrenceId        one production activity
```

The minimum dependency shape is:

```text
ArtifactContentId = ContentHash(exact artifact/package bytes)

RealizationId depends on:
  RealizationRegimeId
  OirId
  SupplierBindingId
  TargetContractId and external ABI
  ArtifactContentId
  any build-definition field whose omission would change interpretation
```

This permits two byte-identical packages to share a raw content ID while still
carrying distinct realized-endpoint identities when their admitted OIR,
binding, target interpretation, or preservation basis differs. Conversely, a
new package layout or embedded manifest changes `ArtifactContentId` without
silently changing OIR.

The emitter/toolchain versions, resolved dependencies, invocation ID, times,
logs, and byproducts belong in production provenance unless the artifact's
meaning depends on them. If a supposedly provenance-only field can change the
meaning of identical target bytes, the artifact model is not closed and the
field must move into identity or the target contract.

An emission occurrence is not content-addressed deduplication. Two executions
may produce byte-identical artifacts and still have distinct observations,
operators, times, environments, and residual trust.

### 8.4 Effects and failure boundary

`ProduceRealization` may read provider packages, compilers, runtimes, caches,
and services and may write directories, objects, manifests, logs, or remote
artifacts. Its contract must report:

- which effects may begin before all semantic and supplier gates complete;
- whether publication is atomic at an identified boundary;
- which outputs or byproducts exist after failure;
- whether a retry is idempotent, content-addressed, or a new occurrence;
- cleanup and supersession behavior; and
- the exact observation emitted for complete, refused, failed, and partial
  runs.

Stage 2 does not prescribe staging directories or transaction mechanics. It
requires the later contract not to describe an effectful producer as a pure
function or treat partial production as endpoint rejection.

`RealizationProductionRefusal` occurs before production effects when the
well-formed request names an unsupported target/mode, lacks an admitted binding
or provider capability, or is disallowed by explicit policy. Malformed inputs
remain authentication/admission failures. Toolchain, filesystem, provider, or
service breakdown after production begins is an operational failure, with the
partial variant used whenever declared effects remain.

## 9. Deployment

### 9.1 Configuration and activation are different transitions

Deployment resolves a fixed admitted realization to physical resources. It
cannot authorize a semantic change. The target distinguishes a portable
binding from live operational authority:

```text
PrepareDeployment(
  realization: AdmittedRealization[R],
  specification: DeploymentSpecification,
  resources: ResourceResolutionSnapshot,
  policy: DeploymentPolicy,
  deployment_regime: DeploymentRegime
) -> DeploymentBinding[D -> R] + AdmittedDeploymentBinding[D -> R]
  | DeploymentRefusal

ActivateDeployment(
  binding: AdmittedDeploymentBinding[D -> R],
  operator_authority: OperatorAuthority,
  activation_request: ActivationRequest
) -> DeploymentCapability[J -> D] + DeploymentObservation
  | OperationalFailure
  | PartialEffectFailure
```

`PrepareDeployment` checks that every resource, service, key, setup object,
module, device, process, topology edge, and trust-zone constraint resolves only
roles the realized endpoint already authorizes. It establishes physical
resolution and policy compatibility, not implementation conformance or
endpoint acceptance.

A setup or verification-key choice that changes the accepted proof language
is not free deployment configuration. Deployment may resolve only a value or
member already authorized by the Protocol/OIR contract; otherwise the change
must return to the semantic owner.

`ActivateDeployment` may allocate, upload, provision, register, start, or
connect resources. It creates a live, scoped, expiring or revocable capability
to one deployment instance. A serialized deployment document is never the
live capability.

### 9.2 Deployment identity and mutable state

The identities are intentionally split:

```text
DeploymentBindingId   content identity of exact realization-to-resource plan
DeploymentInstanceId  occurrence identity of one activation
DeploymentCapability  process/session authority over that live instance
```

`DeploymentBindingId` should commit to the realized artifact, topology,
resource roles, exact immutable resource versions or references, and any
continuing runtime constraints. The policy and resolution procedure may remain
in provenance when the resulting binding is complete; a policy whose rules
continue to constrain invocation is an identified dependency.

A mutable resource must be handled in one of two explicit ways:

1. bind a content/version/epoch snapshot into `DeploymentBindingId`; or
2. declare it late-bound, restrict the allowed set in the deployment binding,
   and bind the selected instance/version in each invocation.

An unversioned mutable lookup cannot be treated as immutable deployment
identity. Changing a resource cannot change Protocol or OIR meaning; it may
create a new deployment binding/instance, a refused join, an operational
failure, or evidence of nonconformance.

### 9.3 Deployment outcomes and capability rules

Deployment refusal includes incompatible target/resource roles, unavailable
required declarations, unauthorized substitution, unmet deployment policy,
and unsupported topology. Activation failure includes allocation, upload,
startup, registration, or connectivity failures. A partially started service
or allocated device is a partial-effect failure and must identify remaining
resources and cleanup status.

A `DeploymentCapability` must state:

- authorized endpoint role and entry points;
- resource and setup scope;
- instance identity, epoch, and lifetime;
- invocation limits and concurrency model;
- revocation, shutdown, and supersession behavior;
- delegation or attenuation rules; and
- whether copying creates an alias, is prohibited, or consumes authority.

No default copy rule should be inherited from immutable projection
capabilities.

## 10. Invocation

### 10.1 Bind before executing

Invocation is an exact runtime join. Separating binding from execution makes
malformed external input, missing authority, semantic result, and operational
failure observable as different categories:

```text
BindInvocation(
  deployment: DeploymentCapability[J],
  interface: AdmittedProtocolInterface[I -> P],
  request: InvocationRequest,
  input_capabilities: InvocationInputCapabilities,
  policy: InvocationPolicy,
  invocation_regime: InvocationRegime
) -> BoundInvocationCapability[U]
  | InterfaceMalformed
  | InvocationRefusal

InvokeEndpoint(
  invocation: BoundInvocationCapability[U],
  executor: ExecutorCapability
) -> CompletedEndpointRun + RawOperationalObservation
  | OperationalFailure
  | PartialEffectFailure
```

The binder reauthenticates the join among Protocol, Interface, OIR,
realization, deployment instance, role, statement, proof or witness ports,
setup/resources, and authorized prover-local inputs. Interface decoding occurs
before fixed Protocol semantics and therefore owns malformed external
statement/proof packaging behavior. A decoder that changes the semantic value
or accepted language is outside Interface authority.

Private witness material, stateful sessions, external services, setup
resources, and local entropy arrive as scoped capabilities or exact values,
not as reusable Protocol/OIR identity. The binder may attenuate a broad
provider capability to the exact port, statement, operation set, lifetime, and
use count required by one invocation.

### 10.2 Completed result taxonomy

The completed result remains role-specific:

```text
VerifierRunResult =
    Accept
  | Reject(ProtocolRejectClass)

ProverRunResult =
    ProducedProof(proof_bytes, declared public observables)
```

The surrounding invocation outcome separately carries:

```text
InterfaceMalformed
InvocationRefusal
OperationalFailure
PartialEffectFailure
```

Verifier `Reject` is a successful endpoint execution that answered the
Protocol question negatively. It is not an exception or refusal. Conversely,
missing supplier/runtime authority, an unavailable resource, or an executor
defect is not proof rejection. Prover success means only that this invocation
produced these bytes and declared observables; it does not establish verifier
acceptance, witness satisfaction, completeness, soundness, or zero knowledge.

Stage 4B may refine result and reject classes, but it may not collapse these
outer categories.

### 10.3 Invocation identity, capability, and replay

An invocation is an occurrence, not a semantic content subject:

```text
InvocationId / RunId binds at least:
  DeploymentInstanceId and current resource snapshot
  OirId, ProtocolInterfaceId, role, and optional ProverPlanId dependency
  exact public statement and proof input, or their canonical identities
  private-input references/digests or commitments suitable for the record
  setup/resource selections
  executor/runtime identity
  invocation nonce, sequence, epoch, or time when needed
```

Exact private-record handling belongs to Stage 4B and Stage 6. The structural
rule is that a public observation can bind opaque or confidential inputs by an
appropriate reference without claiming to reveal or validate their contents.

`BoundInvocationCapability` is normally narrow and invocation-local. It should
declare whether it is single-use, whether failure consumes it, which child
capabilities it owns or borrows, and whether retries mint a new `InvocationId`.
Serializing the request does not serialize live deployment or provider
authority. A replay is a new invocation occurrence even if all content inputs
are equal; deterministic output equality, when expected, is a separately
checked relation between runs.

Invocation may emit proof bytes, logs, metrics, resource changes, service
requests, or externally visible actions before completion. The observation
must distinguish a completed result from the last protected event reached and
from remaining partial effects. A run result cannot flow backward to authorize
a missing Protocol event, Interface mapping, supplier, realization, or
deployment resource.

## 11. Observation, evidence record, appraisal, and reliance

### 11.1 Raw observations remain producer-owned

Each producing domain defines what its raw result means:

- OIR projection may produce a projection trace or checker receipt;
- realization may produce an emission/build observation;
- deployment may produce provisioning and activation observations;
- invocation may produce endpoint event logs, proof or verdict results,
  resource observations, and partial-effect reports;
- formal or external tools may produce theorem, replay, comparison, or
  benchmark receipts; and
- source reading may produce an attributed reconstruction record.

The producing domain owns event ordering, result taxonomy, sensitivity, and
the statement that the observation actually makes. Evidence does not rename a
partial log as a complete execution or reinterpret a verifier reject as an
operational failure.

A `RawObservation` may be ephemeral, streamed, incomplete, or too sensitive to
publish. It needs an occurrence/producer reference sufficient for attribution,
but it need not become a universal persisted object. Redaction or aggregation
creates a derived observation or evidence record with explicit omissions; it
does not preserve an unqualified identity.

### 11.2 Evidence recording

The Evidence-owned ingress is:

```text
RecordEvidence(
  material: RawObservation | ExternalReceipt | ComparisonResult,
  claim: ClaimRef,
  subject_refs,
  recorder_or_issuer,
  procedure: ProcedureRef,
  environment_and_pins,
  evidence_regime: EvidenceRegime,
  disclosure_and_redaction_scope
) -> EvidenceRecord[E]
  | EvidenceRecordRefusal
```

The minimum record contract binds:

```text
claim or evidence facet
exact semantic, artifact, transition, or occurrence subjects
issuer/recorder and attribution mechanism
input identities and relevant values
environment, dependencies, providers, toolchain, and external pins
procedure/checker and its version or identity
observed result and outcome category
covered and uncovered observations
conditions, exclusions, residual trust, and non-claims
time, epoch, nonce, or other freshness material when relevant
reproduction or independent-check path
derivation/redaction lineage when the record is not raw
```

Successful recording establishes that one well-formed evidence record
explicitly attributes the stated material, scope, and procedure under its
recording regime, including whatever authentication that regime actually
requires. It does **not** establish that the claim is true, the
procedure is adequate, the issuer is trusted for an intended use, the result
is current, or a consumer should rely on it.

`RecordEvidence` names the logical record-construction/admission boundary.
Acquiring external material, signing, storing, and publishing the record may
be separate effectful activities. If an implementation combines them, it must
distinguish a record refusal from operational or partial-publication failure;
successful publication still does not appraise the claim.

A tentative identity dependency, to be completed only in Stage 6, is:

```text
EvidenceRecordId depends on:
  EvidenceRegimeId
  exact material/observation or receipt identity
  exact claim/facet and subject references
  issuer/recorder identity
  procedure and environment/pin identities
  stated scope, exclusions, freshness material, and record content
```

Two records containing equal observed values may have different identities
because they came from different activities, issuers, procedures, environments,
or scopes. A signature authenticates an issuer and bytes under its scheme; it
does not by itself widen the claim.

### 11.3 Evidence appraisal

Appraisal asks whether one or more records support a claim under an explicit
policy:

```text
AppraiseEvidence(
  records: EvidenceSet,
  claim: ClaimRef,
  policy: EvidencePolicy,
  reference_values,
  trust_anchors,
  appraisal_context_and_time
) -> ClaimAssessment[C]
  | AppraisalRefusal
```

A successful assessment may report outcomes such as supported,
contradicted, insufficient, stale, or indeterminate. The exact vocabulary is
Stage 6 work. A negative or insufficient assessment is still a successful
application of policy; `AppraisalRefusal` is reserved for a malformed or
unauthenticated record, unavailable policy/dependency, unsupported evidence
kind, or checker inability to apply the requested policy.

`ClaimAssessment` must bind the exact evidence set, claim, policy and version,
reference values, trust anchors or trust domain, appraisal context, time or
freshness basis, conclusion, residuals, and validity scope. If it is durable,
its identity depends on those fields. A later policy, reference-value, or
freshness change may produce another assessment without changing any Evidence
record or semantic subject.

Evidence appraisal is not Protocol admission, OIR admission, realization
checking, verifier execution, or release authorization. It reports a
policy-qualified conclusion about supplied records.

### 11.4 Use-specific reliance

The relying consumer owns the final transition:

```text
DecideReliance(
  assessments: ClaimAssessmentSet,
  intended_use: IntendedUse,
  policy: IntendedUsePolicy,
  consumer_context,
  current_state,
  consumer_trust_anchors
) -> RelianceDecision[Q]
  | RelianceDecisionRefusal
```

The decision may permit, deny, condition, limit, or defer one use. Exact
outcome vocabulary belongs to the relying consumer. A decision binds its
consumer, intended action, subjects, assessments, policy/version, current
state, validity interval or expiry, revocation/supersession rule, and residual
conditions.

Two consumers may make different valid decisions from the same assessment.
The same consumer may decide differently for deployment, publication,
benchmark reporting, or release. Reliance does not mutate an EvidenceRecord or
make its claim semantically true. A later expired or revoked decision does not
change the historical observation or endpoint result.

### 11.5 Why appraisal and reliance remain separate

[RFC 9334](https://datatracker.ietf.org/doc/html/rfc9334) provides a useful
architectural analogue: a Verifier applies an appraisal policy to Evidence and
produces Attestation Results, while a Relying Party applies its own policy to
those results for an application-specific decision. It also places freshness
under the relevant appraisal policy. zkc should preserve that two-policy
separation without importing RATS roles or attestation formats wholesale.

[SLSA build provenance v1.2](https://slsa.dev/spec/v1.2/build-provenance)
separates output subjects, build definition, external/internal parameters,
resolved dependencies, builder identity, one invocation's metadata, and
byproducts. This is a useful checklist for emission provenance and its trust
boundary, not a substitute for `RealizesOir` or zkc Evidence appraisal.

[W3C PROV-DM](https://www.w3.org/TR/prov-dm/) distinguishes entities,
activities, and agents/responsibility and permits separately identified uses
and generations. That separation supports occurrence-specific observation and
attribution. PROV is a provenance vocabulary; it does not choose zkc's claim
taxonomy, preservation relation, or reliance policy.

## 12. Cross-transition identity rules

The identity algebra should preserve the following separations. Exact hashes
and encodings remain with later normative owners.

| Transition/result | Identity consumed | Identity preserved or minted | Explicitly not implied |
|---|---|---|---|
| Project endpoint | `ProtocolId`, `ProtocolInterfaceId`, role, OIR regime, tagged optional `ProverPlanId` | Mints `OirId`; source IDs remain cited dependencies | Same Protocol does not imply same OIR across Interfaces or plan-specialized bases |
| Admit standalone OIR | Stored/computed `OirId`, OIR regime, local dependency identities | Preserves `OirId`; creates no new semantic identity | Local admission does not mint projection coverage |
| Form supplier binding | `OirId`, target, binding regime, explicit below-OIR `ProverPlanId` if read, exact provider designations | Mints `SupplierBindingId`; no live authority | Binding does not change `OirId` or establish provider correctness or availability |
| Resolve supplier authority | `OirId`, `SupplierBindingId`, resolver snapshot, provider policy and regime | Mints only process-local authority; no semantic identity | Parsed configuration does not grant provider access and authority does not survive serialization |
| Produce realization | `OirId`, `SupplierBindingId`, target/build inputs | Mints `ArtifactContentId`, candidate `RealizationId`, and distinct occurrence identity | Production success does not establish preservation |
| Admit realization | `ArtifactContentId`, candidate `RealizationId`, `OirId`, binding, checker/regime | Preserves content and realization IDs; creates a process capability and possibly a separately identified judgment/certificate | Admission does not change OIR or artifact bytes |
| Prepare deployment | `RealizationId`, topology/resource snapshots, deployment regime | Mints `DeploymentBindingId` | Physical resolution cannot change semantic identity |
| Activate deployment | `DeploymentBindingId`, operator/request | Mints `DeploymentInstanceId`; returns live capability | Equal configuration does not mean the same live instance |
| Bind/invoke | Deployment instance, Interface, exact input/resource references, executor | Mints `InvocationId`/`RunId` for an occurrence | Equal inputs do not collapse two executions into one occurrence |
| Record evidence | Observation/receipt, claim, subject, issuer, procedure, environment, Evidence regime | Mints `EvidenceRecordId` if durable | Record identity does not make the claim true |
| Appraise | Evidence set, policy/version, references, trust context, time | Mints `ClaimAssessmentId` if durable | Assessment does not alter evidence or semantic subjects |
| Decide reliance | Assessment set, consumer/use policy, context/time | Mints a scoped decision identity if the consumer persists it | Reliance is not reusable semantic or evidence authority |

Four general identity rules follow:

1. Content identity and occurrence identity are different. Builds,
   activations, invocations, and appraisals can repeat over equal content.
2. Production provenance and semantic identity are different. A producer or
   policy is included in semantic identity only if interpretation remains
   dependent on it.
3. A dependent ID is not authority to resolve or use its preimage. Consumers
   require admitted subjects or explicit capabilities.
4. Evidence about an existing subject attaches to it and never remints or
   mutates the subject.

If Stage 6 persists them, `ClaimAssessmentId` and a reliance-decision content
identity remain separate from `AppraisalOccurrenceId` and a decision
occurrence. Repeating the same policy calculation can preserve equal content
while producing a distinct attributed activity.

## 13. Effect and outcome rules

### 13.1 Effect ledger

| Transition | Semantic/operational effect class | Required effect statement |
|---|---|---|
| `ProjectEndpoint` | Pure checked derivation over admitted immutable inputs, unless an implementation explicitly exposes caches/logs as non-semantic effects | Determinism, read set, and no ambient Interface/plan state |
| `AdmitOirLocal` | Authentication/admission over bytes and declared resolvers | Exact resolver snapshot and retained closure |
| `FormSupplierBinding` | Pure checked configuration derivation | Exact requirement closure and provider designations; no live capability acquisition |
| `ResolveSupplierAuthority` | Process-local authority resolution | Exact lookup snapshot, provider policy/regime, lifetime, revocation, and refusal surface |
| `ProduceRealization` | Effectful production | Publication boundary, files/objects/services touched, byproducts, retry, and partial failure |
| `CheckRealization` | Checked correspondence; may invoke tools or sandboxes operationally | Separate checker observations from the semantic judgment established |
| `PrepareDeployment` | Configuration and policy check; resource resolution may observe external state | Snapshot/time and whether any reservation occurs |
| `ActivateDeployment` | Effectful provisioning and lifecycle creation | Allocation/start/registration effects, rollback, revocation, partial state |
| `BindInvocation` | Authority attenuation and external Interface decode; may reserve capacity | Capability consumption/reservation and malformed/refusal boundary |
| `InvokeEndpoint` | Effectful endpoint execution | Protected event frontier, emitted outputs, service/resource effects, retry semantics |
| `RecordEvidence` | Logical record construction/admission; acquisition, signing, storage, or publication may add effects | Source material, redaction, issuer, and any storage/publication failure or partial-record rules |
| `AppraiseEvidence` | Policy evaluation; normally no semantic side effect | External reference/freshness reads and audit-log effects if any |
| `DecideReliance` | Consumer decision, potentially authorizing an external action | Decision scope, action boundary, expiry, revocation, and audit effects |

An implementation may combine adjacent steps, but its result type and record
must preserve the conceptual boundaries. For example, one command may bind,
emit, build, test, and publish; a failure still needs to say which gates were
passed and which effects occurred.

### 13.2 Outcome taxonomy

| Outcome family | Successful transition? | Example | Must not be reported as |
|---|:---:|---|---|
| Positive semantic judgment | Yes | `ProjectionCorrect`, `RealizesOir` | Operational success alone |
| Successful negative semantic result or correspondence judgment | Yes | Verifier `Reject(check_failure)`; candidate `ProjectionIncorrect`; `DoesNotRealize` | Refusal, malformed input, or executor failure |
| Positive operational result | Yes | Prover produced bytes; deployment activated | Completeness, conformance, or reliance |
| Malformed/unauthenticated input | No | Carrier cannot decode; stored ID mismatches | Unsupported valid feature |
| Typed refusal | No | Target unsupported; supplier missing; policy declines the request | Protocol invalidity or proof rejection |
| Operational failure | No completed effectful result | Compiler/service/device failed after attempt | Semantic negative judgment |
| Partial-effect failure | No completed result; residual state exists | Some package files published or resources activated | Pure refusal with no effects |
| Evidence assessment outcome | Yes | supported, contradicted, insufficient, stale, indeterminate | Reliance decision |
| Reliance denial | Yes, when policy was successfully applied | Consumer denies one intended use | Evidence invalidity or semantic falsehood |
| Policy/checker refusal | No assessment/decision | Required policy or checker unavailable | Negative assessment or denial |

This taxonomy is more important than sharing one outer error class. A common
transport envelope is acceptable only if these domain meanings remain typed
and recoverable.

## 14. Capability, serialization, replay, and evolution rules

| Object or capability | Authority gained or informational role | Copy/lifetime default | Serialization behavior |
|---|---|---|---|
| `AdmittedOir` | Consume one locally valid OIR under exact regime/dependencies | Immutable read-only sharing is plausible | Degrades to OIR carrier and references; re-admit |
| `ProjectedOirCapability` | Assert/rely on source-relative projection within its checker scope | Immutable sharing is plausible while retained source remains live | Degrades to OIR artifact plus ordinary source refs unless a portable projection record exists |
| `AdmittedSupplierAuthority` | Realize the exact OIR/plan/target through resolved providers | Bound to resolver/provider lifetime; provider handles may restrict copying | Portable binding config survives; live provider authority does not |
| `AdmittedRealization` | Deploy or invoke one `RealizationId` under one checked preservation basis | Immutable artifact access may share; executable resources may not | Content, realization, and judgment references survive; reauthenticate/re-admit in a new process |
| `AdmittedDeploymentBinding` | Activate only the authorized realization/resource plan | Immutable configuration, subject to resource snapshot validity | Binding survives; live resources do not |
| `DeploymentCapability` | Operate one live instance within role/resource/lifetime limits | Explicitly scoped, revocable, and concurrency-aware | Never serialized as live authority |
| `BoundInvocationCapability` | Perform one or a bounded number of exact invocations | Normally narrow, consuming or explicitly replayable | Request description may serialize; deployment/provider authority does not |
| `EvidenceRecord` | No operational or semantic capability; provides attributable material to an appraiser | Immutable record, freely copyable subject to disclosure rules | Portable only under its explicit schema and authentication |
| `ClaimAssessment` | No endpoint authority; supports a later consumer decision within scope | Immutable, time/policy qualified | Portable only if Stage 6 defines verifier identity and validation |
| `RelianceDecision` | Authorizes only the consumer's named use when the consumer defines it that way | Expiring/revocable and consumer-local by default | No transferable authority unless the consumer explicitly defines delegation |

Cross-cutting rules:

1. Bytes and IDs authenticate content; they do not carry process authority.
2. Serialization always loses live resolver, provider, deployment, session,
   and invocation authority unless a separate protocol reconstructs it.
3. Copy, alias, concurrency, consumption-on-failure, and revocation are
   specified per capability, never inherited from one generic handle type.
4. Replay of a checked pure transition may reproduce the same subject ID.
   Replay of an effectful transition creates another occurrence and may observe
   different state.
5. Supersession does not rewrite history. A new regime, provider, deployment,
   assessment, or policy creates a new admitted basis, occurrence, or decision.
6. Evidence and reliance never grant permission to bypass source admission,
   projection, supplier binding, realization checking, or invocation binding.

## 15. Bridge ownership map

| Bridge | Source-definition owner | Bridge/checker and target owner | Relying consumer/policy owner | Authority boundary |
|---|---|---|---|---|
| Protocol + Interface + optional plan to OIR | PIR/Protocol owns obligations; Interface and plan owners define dependent subjects | OIR owns projection, coverage, OIR semantics, identity, and refusal | Realization or independent OIR consumer | OIR may not reinterpret Protocol, Interface, or plan |
| Standalone OIR admission | OIR carrier and dependency owners | OIR | Realization/interpreter | Local admission cannot mint source-relative coverage |
| OIR/plan to SupplierBinding | OIR/plan own abstract requirements | Realization owns exact immutable binding formation | Emitter/interpreter/realizer | Binding cannot change endpoint semantics, self-prove providers, or carry live authority |
| SupplierBinding to live provider authority | Binding owns exact designations; provider environment owns current resources | Realization owns resolution and narrow local admission | Realizer | Provider availability and authority are process-local and vanish at serialization |
| OIR + binding to realization | OIR defines preserved behavior | Realization owns production and `RealizesOir` checking | Deployment/operator | Producer output cannot prove its own correspondence by packaging |
| Realization to deployment | Realization defines artifact and authorized resource roles | Realization deployment subdomain | Operator and invocation binder | Physical resources cannot authorize new semantics |
| Deployment to invocation/result | Interface/OIR/realization/deployment define accepted join | Realization runtime subdomain | Caller/operator and later evidence recorder | Runtime inputs cannot change fixed endpoint behavior |
| Observation to EvidenceRecord | Producing domain defines raw result | Evidence owns record schema and attribution | Evidence appraiser | Recording cannot widen or reinterpret the observation |
| EvidenceRecord to ClaimAssessment | Claim owner defines proposition; Evidence defines records | Evidence owns appraisal vocabulary and procedure | Relying consumer | Appraiser applies policy but cannot authorize use for every consumer |
| ClaimAssessment to RelianceDecision | Evidence owns assessment meaning | Relying consumer owns intended-use decision | The consumer or external action gate | Reliance cannot redefine evidence or semantic truth |

No bridge here belongs in `foundation/` merely because several rows contain an
ID, regime, refusal, or capability. Extraction requires genuinely shared
semantics, authority, lifetime, and failure behavior.

## 16. Scenario pressure and opportunity results

### 16.1 One Protocol, two Interfaces

```text
P + I1 + verifier -> O1
P + I2 + verifier -> O2
```

Expected result: `ProtocolId` is equal; `ProtocolInterfaceId` and normally
`OirId` differ. Protocol-level Analysis can be reused. Endpoint-level ABI,
malformed-input, projection, realization, and conformance claims cite the
specific Interface/OIR. This is the target replacement for carrier-label
dependence.

### 16.2 One Protocol, two ProverPlans

For verifier projection, both plans are irrelevant and the verifier OIR is the
same Interface-bound subject. For prover projection:

- if both plans remain entirely below OIR, a generic prover OIR may remain the
  same and supplier/realization bindings differ explicitly; or
- if the plans select distinct canonical prover programs while preserving the
  fixed Protocol, the tagged plan basis and `OirId`s differ.

This scenario keeps plan freedom without allowing a plan to rewrite
verifier-visible behavior.

### 16.3 Source-free OIR

A new process admits OIR, checks its identity and local contract preimages,
and may bind suppliers or execute it under a permitted local policy. It reports
`LocalOirValid`. It reports Protocol coverage as unknown until it receives the
source and rechecks or validates sufficient durable projection evidence.

### 16.4 One OIR, two supplier bindings

```text
O + B1 -> R1 carrying artifact content A1
O + B2 -> R2 carrying artifact content A2
```

`OirId` remains unchanged. Binding and realization IDs differ; artifact
content IDs normally differ but may coincide when the produced package bytes
are equal. Each realization requires its own preservation basis and evidence.
Equal endpoint results on selected vectors may relate observations but do not
merge realization identities or establish universal equivalence.

### 16.5 One realization, two deployments

Embedding the same artifact in a process and activating it as a remote service
preserves the realized artifact identity while changing deployment binding,
instance, resources, invocation behavior, operational observations, and
reliance context. Network or service policy cannot change the accepted proof
language; if it does, the wrapper is a separately modeled Interface, policy,
or Protocol rather than mere deployment.

### 16.6 Verifier reject, refusal, and failure

Three runs over the same OIR can produce:

```text
Completed(Reject(check_failure))
InvocationRefusal(missing required provider/resource authority)
OperationalFailure(executor or service failed)
```

Only the first is a Protocol-level negative answer. A metrics or API layer
that collapses all three loses information required by Evidence and reliance.

### 16.7 Partial operational effects

An emitter publishes a manifest before a later build step fails, or a
deployment activates one of two services before the second fails. The target
result is `PartialEffectFailure` plus an occurrence observation naming the
published or live residue. No `RealizedEndpointArtifact`, complete deployment,
or endpoint verdict is inferred. Retry and cleanup use the effect contract,
not semantic identity.

### 16.8 One Evidence record, two consumers

A pinned replay record may support a narrow implementation-correspondence
assessment under one Evidence policy. A development status page may rely on it
to report a tested fixture, while a release policy may deny deployment because
its required target, freshness, or coverage grade differs. Both reliance
decisions can be correct without changing the record or endpoint semantics.

### 16.9 New opportunity exposed by the separation

The model permits independent alternatives without a shadow Protocol model:

- another projector can propose OIR and use the same source-relative checker;
- a source-free consumer can safely use locally admitted OIR while reporting
  coverage as unknown;
- several supplier bindings and targets can compete below one fixed endpoint;
- direct interpretation and standalone emission can be two realizations of
  the same OIR rather than rival semantic authorities;
- deployment can vary resource topology without reminting Protocol or OIR;
- Evidence can compare multiple projectors, emitters, interpreters, or
  deployments under explicit facets; and
- each consumer can adopt a different reliance threshold without contaminating
  semantic admission.

## 17. Current-to-target gap and handoff ledger

| Area | Current correspondence | Stage 2 target skeleton | Later owner must complete |
|---|---|---|---|
| Interface input | Projection reads current carrier ABI labels | Explicit admitted `ProtocolInterface[I -> P]` is mandatory | Stage 3 Interface fields; Stage 4B exact projection reads |
| ProverPlan input | Current prover skeleton uses routes embedded in sealed PIR | Tagged plan basis at projection or explicit below-OIR realization basis | Stage 3 obligation/plan schema; Stage 4B placement per field |
| Projection result | OIR plus private retained source backing and `COV_realized` checks | Portable OIR plus source-relative paired capability carrying `ProjectionCorrect` | Stage 4B relation, grammar, source map, checker |
| Standalone OIR | Local identity and cited contract re-admission | `LocalOirValid` explicitly separate from source coverage | Stage 4B local admission basis |
| Supplier binding | Closed C++ execution profiles and explicit Rust binding files | Identified exact binding subject plus separately admitted provider capability | Stage 4B requirement/binding/provider schemas |
| Emission | Source-free Rust crate generation, embedded provenance, vectors, deterministic fixture output | Effectful production separated from named realization-preservation checking | Stage 4B target contracts, artifact identity, checker/grade, effect model |
| Direct interpretation | Execution profile chosen per run | Interpreter/profile pair classified as one concrete realization capability | Stage 4B correspondence grade and run contract |
| Deployment | Architecture and roadmap roles; no generalized implemented surface | Portable deployment binding separated from live activation capability | Stage 4B topology, resource, lifecycle, partial-effect schemas |
| Invocation | Direct CLI/library execution over OIR/profile and caller maps/bytes | Interface-aware bind step, narrow invocation capability, typed effectful run | Stage 4B request/result/session APIs and operational semantics |
| Observation/run record | Logs/results and normative prover record requirements are distributed | Producing-domain raw observation with exact occurrence and outcome category | Stage 4B run/observation schemas |
| Evidence record | Pinned tests, replays, evaluations, and documents | Evidence-owned attributable record ingress | Stage 6 record schema, authentication, redaction, catalog |
| Appraisal | No generalized implemented evidence policy | Policy-qualified `ClaimAssessment` distinct from record validity | Stage 6 policy language, reference values, freshness, aggregation |
| Reliance | Project/status/user decisions remain informal or document-specific | Consumer-owned intended-use decision | Stage 6 interface to relying policies; each consumer owns concrete rules |

### 17.1 Stage 2 provisional decisions

The following should enter cross-workstream convergence as recommended target
decisions:

1. Require an admitted `ProtocolInterface` for every endpoint projection.
2. Use a tagged plan basis; never read `ProverPlan` through ambient compiler or
   realization state.
3. Separate `LocalOirValid` from source-relative `ProjectionCorrect` in names,
   types, capabilities, and serialization behavior.
4. Default to direct source-relative checking plus a paired in-process
   capability. Add a durable projection record only for a named independent
   consumer.
5. Make supplier binding an exact closed designation. Keep a broad catalog
   outside binding identity and forbid ambient provider selection.
6. Treat supplier binding configuration and live resolved provider authority
   as different objects.
7. Separate effectful realization production from the named relation that
   admits its output, even where one trusted implementation initially combines
   them.
8. Separate deployment configuration, activation occurrence, and live
   capability.
9. Separate invocation binding, completed role-specific result, operational
   failure, and partial effects.
10. Preserve the four-step evidence chain:
    observation -> record -> appraisal -> use-specific reliance.
11. Use content identities for immutable subjects/configurations and occurrence
    identities for production, activation, invocation, and appraisal events.
12. Do not introduce one universal transition record or capability type.

### 17.2 Deliberate Stage 4B deferrals

This note does not select:

- exact OIR operations, block signatures, carrier schema, or identity bytes;
- the exact protected-trace and source-map definition of `ProjectionCorrect`;
- whether each permitted ProverPlan field belongs above or below OIR;
- a complete abstract supplier requirement vocabulary;
- supplier binding file/API schema, provider lifecycle, or target contracts;
- the target-specific `RealizesOir` relation or conformance grades;
- trusted emitter versus validator/certificate placement per backend;
- artifact/package format, build system, cache, atomic publication, or
  deterministic-build requirement;
- deployment topologies, setup/key/resource schemas, service discovery, or
  revocation mechanism;
- invocation/session APIs, exact result classes, concurrency, retries,
  sensitivity controls, or full operational semantics; or
- complete raw observation and run-record schemas.

These questions remain bounded by the identities, authorities, outcome
categories, and no-backflow rules above.

### 17.3 Deliberate Stage 6 deferrals

This note does not select:

- a universal Evidence record encoding or signature scheme;
- exact evidence facets, grades, aggregation algebra, or issuer registry;
- disclosure, redaction, retention, and provenance-of-provenance mechanisms;
- an Evidence policy language, trust-anchor model, freshness scheme, or
  reference-value service;
- `ClaimAssessment` and `RelianceDecision` serialized schemas;
- release, publication, deployment, or project-status relying policies; or
- automatic derivation of public status from records.

Stage 6 inherits the separation of raw producer meaning, attributable record,
policy-qualified assessment, and consumer-owned decision.

### 17.4 Reversal and reopening triggers

Reopen a provisional choice when:

- projection still needs a carrier-only field after Interface and plan closure;
- a plan field cannot be placed above or below OIR without changing protected
  verifier-visible behavior;
- a named independent consumer makes rechecking projection impractical and
  justifies a durable certificate;
- provider selection changes protected OIR behavior rather than merely
  realizing it;
- an effectful producer cannot expose a meaningful completion/partial-effect
  boundary;
- a target has no practical independent realization checker and its trusted
  boundary must be accepted explicitly;
- deployment or invocation policy changes the semantic value or accepted
  language rather than selecting already-authorized resources;
- a serialized capability is genuinely required across a process boundary and
  needs a separate reconstruction protocol; or
- an Evidence or relying consumer requires a stable portable object whose
  scope cannot be expressed by the Stage 6 record/assessment split.

None of these triggers permits a quiet category merge. A changed design must
identify the new owner, relation, identity dependency, capability, and
no-backflow rule.

## 18. Bounded conclusion

The current implementation provides a strong starting pattern: projection
checks source coverage while source and OIR coexist; standalone consumers
reauthenticate only what OIR locally contains; supplier gaps are refusals; and
verifier verdicts remain distinct from prover output and execution errors.

The Stage 2 target makes the remaining authorities explicit. Interface and
optional plan inputs close projection. OIR and source-relative projection
authority separate at serialization. Supplier designation, production,
preservation checking, deployment, activation, invocation, observation,
recording, appraisal, and reliance each receive their own typed boundary. This
is enough structure for Stage 3, Stage 4B, and Stage 6 to co-design their
schemas without allowing downstream operation or policy to redefine upstream
semantics.
