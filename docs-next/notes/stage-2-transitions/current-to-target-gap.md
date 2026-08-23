# Current-to-target architecture gap map

> **Document kind:** Temporary Stage 2 comparison and handoff ledger
> **Document state:** Converged target comparison; temporary handoff
> **Authority:** None. Verified-current entries summarize the observational
> [current transition catalog](current-transition-catalog.md). Selected-target
> entries summarize the clean-sheet architecture in the
> [target transition catalog](target-transition-catalog.md),
> [cross-case synthesis](cross-case-synthesis.md), and
> [convergence record](convergence.md). This page does not change current
> authority, make the target normative, or authorize implementation.
> **Scope:** Architectural differences between the inspected current system and
> the selected Stage 2 target, with exact later owners.
> **Disposition:** Durable conclusions have been absorbed into their owning
> documents. Retain this comparison for downstream handoff and delete it with
> the temporary Stage 2 package at the later deletion gate.

## 1. How to read this map

The two sides of every row have different epistemic status:

- **Verified current** is a compressed statement about the inspected current
  specifications, implementation entry points, and tests. The linked current
  catalog owns the detailed evidence paths, conflicts, and limits.
- **Selected target** is a clean-sheet architectural conclusion ratified at
  non-normative architecture level. It is not an
  implementation claim and is not constrained by compatibility with current
  APIs, carriers, or persisted data.
- **Implementation consequence** states what an eventual conforming
  implementation would have to represent or check. It is not a migration
  step, priority, work estimate, or authorization to edit code.
- **Later owner** names the package that must define the exact schema and
  relation. Stage 8 eventually decides how the checkout should conform; it
  does not own the meaning.

The disposition vocabulary is deliberately about concepts rather than files:

| Disposition | Meaning |
|---|---|
| **Keep** | Preserve a current architectural invariant, possibly behind different types or code |
| **Reframe** | Preserve the useful role while changing its inputs, authority, factorization, or claimed relation |
| **New** | Add a subject or transition selected by Stage 1/2 but absent as an explicit current boundary |
| **Retire** | Exclude a current shortcut or ambiguous authority pattern from the ideal target; this is not a deletion instruction |

One row may be both **Keep** and **Reframe** when the current separation is
sound but its exact subject boundary is not.

## 2. Architectural delta at a glance

### 2.1 Verified current spine

The current checkout has a strong but uneven set of boundaries:

```text
text or family description
  -> Open PIR
  -> resolve + seal -> identified pir.sealed
  -> persist -> decode -> admit under retained ProtocolEnvironment
       |-> purpose-specific views and conditional analysis
       |-> checked transform -> resealed/re-admitted successor
       |-> paired source-relative OIR projection
       `-> reopen -> raw Open PIR

admitted PIR + relation contract -> post-seal correspondence report
OIR + execution profile -> direct invocation
OIR JSON + binding + runtime path -> emitted Rust crate
```

Generalized deployment, evidence appraisal, and reliance are architectural or
normative intentions rather than implemented end-to-end authorities. The
current catalog also finds no explicit semantic-regime subject, independently
identified Protocol Interface, or independently identified Prover Plan.

### 2.2 Selected target spine

The selected target makes every determining input and claimed relation
explicit:

```text
AuthoringUnit
  -> ResolvedAuthoringUnit + exact ResolutionClosure
  -> CanonicalProtocolCandidate
  -> AuthenticatedCanonicalProtocol
  -> AdmittedProtocol[CoreId, ProtocolId, ProtocolRegime]
       |-> AdmittedProtocolInterface[InterfaceId -> ProtocolId]
       |-> AdmittedProverPlan[PlanId -> ProtocolId]
       |     `-> checked PlanRealizes(PlanId, ProtocolId)
       |-> relation correspondence / property judgments
       |-> admitted successor + checked Protocol relation
       `-> Interface/role/(tagged Plan basis) -> OIR

AdmittedOIR + exact SupplierBinding
  -> resolve live provider authority
  -> realization production occurrence
  -> RealizesOir check -> AdmittedRealization
  -> DeploymentBinding -> live deployment capability
  -> bound invocation -> run occurrence and role-specific result
  -> EvidenceRecord -> ClaimAssessment -> use-specific RelianceDecision
```

The common layer supplies contract shape, closure, identity-effect, outcome,
replay, and no-backflow rules. Semantic truth remains with the domain or bridge
that owns each named relation. There is no universal `TransitionId`, fact
root, portable transition record, or generic `valid` judgment.

## 3. Cross-cutting architecture map

| ID | Disposition | Verified current | Selected target contract | Architectural reason | Implementation consequence | Later owner |
|---|---|---|---|---|---|---|
| X1 | **Keep** | Admission, correspondence, analysis, compilation, projection, execution, and evidence intentions already have non-uniform authority shapes; no current universal transition object is required by an inspected consumer. | Domain- or bridge-owned typed contracts remain the semantic authority; a shared layer exposes only descriptive fields and global invariants. | Similar metadata does not make admission, derivability, correspondence, effects, and policy one relation. | Catalog/lint infrastructure may share a projection schema, but dispatch must end in exact domain types and checkers. | Project/Foundation by extraction throughout Stages 3--7; domain owners retain semantics |
| X2 | **New** | Specification revision, exact declaration references, profiles, and provider references partially qualify meaning, but there is no explicit `SemanticRegime` or stable cross-regime comparison key. | Every semantic subject and checker takes an exact typed regime; cross-regime comparison is an explicit named migration or correspondence relation. | Equal bytes under changed rules need not denote equal meaning, and a silent regime change breaks functional closure. | Subject identities, admission bases, caches, checkers, and diagnostics must carry or resolve exact regime references. | Stages 3, 4A, 4B, and 6 per domain; Stage 7 reconciles evolution rules |
| X3 | **Reframe** | Protocol identity closes over cited vocabulary, but admitted artifacts retain a broader environment and some consumers read carrier labels or routes excluded from `ProtocolId`. | Every pure transition closes over exact subjects, declared reads, dependency preimages, and checker regime; successful resolution retains the exact used closure, not an opportunistic resolver. | Hidden reads make the advertised transition non-functional and make replay or comparison ambiguous. | APIs and checked results must expose exact closure manifests; carrier-only fields must move to Protocol, Interface, Plan, or be removed from the read set. | Stage 3 owns Protocol/Interface/Plan closure; Stages 4A/4B own consumer closures; Stage 7 audits globally |
| X4 | **Keep** and **Reframe** | `DecodedPirArtifact` and `AdmittedPirArtifact` are distinct; admitted storage is immutable and process-local; serialization ends capability continuity. | Keep narrow opaque local capabilities, but parameterize them by the exact subject, regime, and minimal admission basis. Bytes preserve content references, never authority. | Content authentication and authority to consume a checked subject are different states. | Receiving processes must decode, authenticate, resolve, and re-admit; no serialized field may reconstruct a live capability by assertion. | Stage 3 lifecycle contracts; Stage 4B live operational capabilities; Stage 7 consistency |
| X5 | **Reframe** | Identities are domain-specific in practice, but several result/configuration subjects have no explicit identity model and current retained context can vary behind the same `ProtocolId`. | Use owner-defined content identities for immutable subjects, occurrence identities for effects, and paired capabilities for local checked relations. Declare `Preserve`, `Construct`, `Relate`, `Configure`, `Instantiate`, `Observe`, or `Decide` per edge; add no global `TransitionId`. | Identity must answer which subject is the same, not merely that a procedure ran. | Each durable subject needs a canonical preimage and regime; ephemeral judgments need no ID unless a named consumer requires persistence. | Stages 3, 4A, 4B, and 6 per subject; Stage 7 identity audit |
| X6 | **Reframe** | Current APIs distinguish some refusals and failures, but relation disagreement conflicts with refusal prose, property analysis lacks a general successful-negative result, and full run outcomes are not uniformly represented. | Outcomes preserve formation, support, procedure completion, proposition status, and produced subject/judgment/observation as independent dimensions. | `false`, unsupported, inconclusive, refusal, verifier rejection, operational failure, and partial effects lead to different legal next actions. | Domain-specific result sums must retain negative judgments and partial-effect frontiers; a shared diagnostic envelope may not collapse them. | Stages 3, 4A, 4B, and 6; Stage 7 reconciles terminology |
| X7 | **Keep** and **Reframe** | Small deterministic boundaries are recomputed; derivations can be replayed; compiler and projection use stronger paired or replayed checks. Current compiler checking can share producer implementation and is not automatically independent validation. | Recompute cheap closed predicates; split proposer from validator only when the validator is materially smaller or more stable; introduce a durable certificate only for a named independent consumer. | A universal producer/witness protocol adds machinery without reducing trust, while genuinely search-heavy edges benefit from small acceptance checkers. | Every edge must name its proposition, checker independence, replay class, and persistence consumer; unsupported independence is reported as residual trust. | Exact mechanism chosen by Stages 3, 4A, 4B, and 6; Stage 5 may discover new consumers |
| X8 | **Retire** | Current artifacts and reports are heterogeneous, and no inspected consumer requires a universal portable transition graph. | Do not introduce a universal transition artifact, universal fact root, global error enum with semantic authority, or complete portable package in v0. | Such a schema would create identity, compatibility, retention, dispatch, and authority commitments before a consumer justifies them. | Shared tooling consumes lossless domain projections or adapters; portable objects remain claim-scoped and owner-defined. | Stage 5 may reopen for a demonstrated cross-system consumer; Stage 7 preserves the default |
| X9 | **Reframe** | Current transition sequences can be composed operationally, but matching IDs or provenance adjacency does not establish a mathematical end-to-end relation. | Separate procedural sequencing, relation-specific composition, Analysis-owned property transport, Protocol composition, and operational effect sequencing. | Assumptions, maps, observers, quantitative loss, intentional change, and partial effects cannot be recovered from adjacency. | Composition APIs need explicit owner-provided laws; generic graph tooling may display edges but cannot infer transitivity. | Stage 3 structural composition; Stage 4A property/transform composition; Stage 4B operational sequencing; Stage 5 system modes |
| X10 | **New** | General effect and policy transitions are absent or distributed across tools, logs, and architecture prose. | Effectful work produces occurrence-scoped observations with completion and partial-effect states; appraisal and reliance remain downstream policy decisions. | Pure semantic arrows cannot represent resource activation, publication, failure residue, time, revocation, or consumer policy. | Operational APIs need occurrence IDs, effect boundaries, cleanup/rollback metadata where meaningful, and no authority backflow into semantic subjects. | Stage 4B effects and operations; Stage 6 appraisal/reliance |

## 4. Protocol lifecycle and construction map

| ID | Disposition | Verified current | Selected target contract | Architectural reason | Implementation consequence | Later owner |
|---|---|---|---|---|---|---|
| L1 | **Reframe** | Hand-authored MLIR and the FRI family generator produce raw Open PIR. There is no general source-language import judgment or authoritative source correspondence. | `Author` and `Import` produce an unauthoritative `AuthoringUnit`; provenance and any source correspondence are separate claims. | Authoring success must not acquire Protocol authority, and several frontends should be able to converge on one canonical boundary. | Workbench values need explicit source snapshots, profiles, dependencies, and provenance without minting Protocol IDs. | Stage 3 authoring/canonical ingress; imported-source correspondence stays with its source bridge |
| L2 | **Reframe** | Resolution is an internal seal phase that forms the cited vocabulary table; no independent resolved type or capability exists. | `Resolve` produces `ResolvedAuthoringUnit` plus a complete typed `ResolutionClosure`, still without Protocol authority. | Separating actual reads from normalization makes hidden dependencies inspectable and permits alternative authoring carriers. | The resolver must return immutable exact-read closure and distinct missing, ambiguous, cyclic, unsupported, and unavailable outcomes. | Stage 3 |
| L3 | **Reframe** | Seal resolves, checks whole Open PIR structure, constructs `pir.sealed`, and mints one current `ProtocolId`; its public raw MLIR type is not itself an opaque capability. | Factor `Normalize`, `Authenticate Protocol`, and `Admit Protocol`. Normalization constructs a physical canonical candidate; authentication recomputes Core/construction/Protocol identities and dependencies; admission establishes the complete Protocol predicate and mints local authority. | Construction, identity authentication, and normative admissibility are separate claims and may have different trust boundaries. | Distinct candidate/authenticated/admitted states and checkers are required even if one implementation shares a traversal. | Stage 3 |
| L4 | **Keep** and **Reframe** | Persist preserves Protocol identity in MLIR bytecode; decode authenticates transport/structure/ID; admit rechecks seal under a retained environment. | Persist is admission-gated canonical representation; decode remains transport-local; re-authentication and re-admission use the exact regime and minimal dependency basis. Unauthoritative workbench caches use a different envelope. | Persistence must preserve a subject without laundering admission or relying on an open-ended environment. | Artifact APIs must distinguish canonical Protocol artifacts from caches and keep decode, authentication, and admission types non-interchangeable. | Stage 3 carrier/lifecycle; Stage 7 wire-policy consolidation |
| L5 | **Keep** and **Reframe** | Purpose-specific views are derived from admitted backing; some plain aggregates rely on producer provenance and may read current labels/routes. | `ConsumerView<Q>` is question-scoped, locally authority-narrowing, and closed over explicit Interface/Plan inputs where relevant; it normally has no independent ID. | A view should expose only what one checker may read and must not become a shadow fact root. | View constructors must be source-owned and opaque or independently recheckable; consumer code may not consult ambient carrier state. | Stages 3, 4A, and 4B per consumer |
| L6 | **Keep** | Reopening clones an admitted source into raw mutable PIR and discards derivative authority while the original remains admitted. | `Reopen` yields a new unauthoritative `AuthoringUnit` with lineage; even a no-op branch must authenticate and admit again. | Mutability and admission authority are incompatible at a semantic boundary. | Mutable handles must not alias admitted backing or retain an active semantic capability. | Stage 3 |
| L7 | **Reframe** | Static link combines Open PIR components into a newly checked Open PIR proposal; it is distinct from current checked compiler transformation. | Keep authoring-unit link as workbench construction. Add separate Protocol composition that constructs a new Core/Protocol candidate with occurrence namespaces, seams, total schedule, challenges, failures, terminals, and obligations. | Workbench graph combination is not semantic composition, and child admission cannot be inherited by a composite. | Linking and composition require different types and checkers; composite output must undergo whole-Protocol authentication and admission. | Stage 3; Stage 5 studies higher composition modes |
| L8 | **Reframe** | Current sealed PIR acts as carrier, semantic subject representation, and identity-bearing container; the current identity does not expose the selected Stage 1 Core/Protocol factorization. | Canonical PIR is one closed MLIR carrier for `InteractiveCore + ChallengeInterpretation`; `CoreId`, construction identity, and `ProtocolId` remain carrier-independent semantic identities. | Fresh-coin and Fiat--Shamir Protocols may share a Core while differing as Protocols, and alternative authoring/import paths must not redefine meaning. | Canonical encoding and authentication must recompute the factored IDs; MLIR legality remains structural rather than semantic authority. | Stage 3 |

## 5. Dependent subjects and semantic bridges

| ID | Disposition | Verified current | Selected target contract | Architectural reason | Implementation consequence | Later owner |
|---|---|---|---|---|---|---|
| S1 | **New** and **Retire** | Projection and relation correspondence infer ABI/interface facts from admitted carrier labels that are excluded from current Protocol identity. No separate `ProtocolInterfaceId` exists. | Form, authenticate, and admit an identified `ProtocolInterface[I -> P]`. It owns external naming, packaging, lossless pre-semantic decoding, entry points, malformed-input behavior, and relation/application binding, but cannot change Protocol meaning. Retire hidden carrier-label ingress. | The same Protocol may support several external interfaces, while equal `ProtocolId` alone cannot justify fields erased by its identity. | Interface-sensitive consumers must take an exact admitted Interface; canonical IDs and admission checks must reject transcript-, order-, check-, or accepted-language changes disguised as interface fields. | Stage 3 co-designs Interface with Relations; Stage 4B completes endpoint reads |
| S2 | **New** and **Retire** | Construction routes embedded in sealed PIR partially serve planning needs; there is no separate `ProverPlanId`. | Form, authenticate, and admit a dependent Prover Plan, then separately check `PlanRealizes` for total accounting of the exact Protocol's abstract obligations. Retire ambient or duplicated plan reads. | Plan identity and admission do not prove cross-subject obligation coverage; verifier meaning still belongs to Protocol while witness construction DAGs and execution choices may vary independently. | Plan fields must be assigned exactly once: either a tagged `InterfaceAndPlan` projection basis accompanied by exact coverage authority or an explicit below-OIR realization input; verifier projection never reads a Plan. | Stage 3 Plan/obligation schema; Stage 4B placement; Stage 4A completeness consequences |
| S3 | **New** | Relation compilation is currently external; post-seal tooling loads a `RelationContract`, and there is no pre-seal admitted relation-interface ingress. | Relation-owned admission creates an independent relation-interface subject; artifact interpretation yields a `RelationArtifactObservation` over exact bytes and format. | A relation definition, its serialized artifact, an observation about that artifact, and its correspondence to a Protocol are different subjects and authorities. | Relation candidates, IDs, regimes, adapters, observations, and local capabilities need explicit types before Protocol correspondence is checked. | Stage 3 Relations |
| S4 | **Keep** and **Reframe** | Current relation tooling compares an admitted PIR view with a relation contract and optional bytes, distinguishing computed, cross-checked, disagreed, and asserted facts; prose and negative-result behavior conflict. | `RelationCorrespondsAtInterface` relates exact admitted Protocol, Interface, relation interface, optional artifact observation, and bridge regime; affirmative and negative correspondence are successful judgments with residual obligations. | Disagreement is information, not malformed input, and relation truth or witness satisfaction does not follow from interface correspondence. | The checker must consume narrow source-owned views, type successful negatives, and never mint Protocol or relation authority. | Stage 3 Relations |
| S5 | **Keep** and **Reframe** | Current soundness/completeness analysis uses authenticated views, explicit plans, rules, bindings, and hypotheses to derive conditional judgments; a general supported-negative result is absent. | Analysis consumes an exact property-subject tuple, question, regime, basis, derivation plan, hypotheses, and source-owned views; it returns conditional, quantitative, affirmative, or explicitly justified negative `PropertyJudgment` plus a checked derivation. | Property meaning depends on the chosen subject tuple, and failed proof search is not negative truth without completeness. | Analysis schemas must separate query, derivation, conclusion, theorem premises, and portability. Independent replay makes a durable derivation a persistence candidate; persistence is selected only after the named-consumer, stable-checker, exact-closure, retention, and compatibility gate passes. | Stage 4A Analysis |
| S6 | **Reframe** | The current compiler combines provider proposal, replay/authentication of the successor, constraints/objectives, and recomputed selection; no durable general request/result schema exists. | First propose a candidate, independently authenticate/admit it, then check one exact Protocol relation, then select among an explicitly complete candidate domain. `NoSelection` may be a successful decision. | Target validity, source-target preservation/refinement, and optimization choice are independent propositions. | Compiler providers cannot grant successor authority; relation validators name observers/maps/assumptions/regimes; selection declares domain completeness, objectives, and ties. | Stage 4A Compiler |
| S7 | **New** | Current analysis has an FS-related rule inside the existing artifact-qualified model, but the current subject model does not represent the selected Stage 1 pair of Protocols over a shared Core. | Construct and admit the FS Protocol ordinarily; check theorem-backed `FSCompile` as a separate relation between exact fresh-coin and FS Protocols, construction, occurrence/prefix map, regimes, and assumptions. | Target formation is not Fiat--Shamir correspondence, and shared Core identity is not Protocol equality. | FS construction uses the ordinary Protocol lifecycle; the bridge needs its own checker inputs and result without reminting either Protocol. | Stage 3 defines construction and bridge semantics with Stage 4A Analysis |
| S8 | **New** | Checked transformation does not currently provide one general property-specific transport boundary; adjacency or preservation annotations cannot establish transported judgments. | Analysis-owned `PropertyTransport` consumes a source judgment, exact checked source-target relation, occurrence map, transport rule, assumptions, and quantitative substitutions. | Each property has different hypotheses and losses; a compiler relation alone cannot authorize every conclusion. | Downstream judgments cite both the checked relation and a replayable transport derivation; unsupported transport remains explicit. | Stage 4A Analysis |

## 6. Endpoint, operational, and evidence map

| ID | Disposition | Verified current | Selected target contract | Architectural reason | Implementation consequence | Later owner |
|---|---|---|---|---|---|---|
| E1 | **Keep** and **Reframe** | Current projection returns a paired source/OIR artifact and checks source-relative realized coverage; standalone OIR admission checks only local identity and cited contracts. Projection currently infers Interface/Plan-like facts from carrier content. | `Project endpoint` consumes admitted Protocol, Interface, role, and tagged `InterfaceOnly` or `InterfaceAndPlan(admitted Plan, checked PlanRealizes capability)` basis. Successful projection establishes distinct `LocalOirValid(O)` and paired `ProjectionCorrect(P,I,role,basis,O)` results. Standalone admission can re-establish only `LocalOirValid`. | Local target validity cannot establish omitted-source absence or source-obligation coverage, and Plan admission cannot establish obligation coverage. | Projection and standalone admission need distinct types, diagnostics, replay inputs, and serialization behavior; source-free consumers report coverage as unknown. | Stage 4B OIR |
| E2 | **Reframe** | Current C++ execution profiles and Rust emitter bindings select suppliers, but there is no stable admitted general supplier-binding subject or live provider-authority model. | `SupplierBinding` is an identified immutable exact closure over OIR requirements, target, optional below-OIR Plan, and selected provider references; locally resolved provider authority is a separate capability. | A portable designation can remain stable while provider availability, revocation, or process-local authority changes. | Binding identity excludes unselected catalog entries; realization/invocation must receive admitted live providers rather than trust a parsed binding assertion. | Stage 4B Realization |
| E3 | **Reframe** | Rust emission produces a crate from OIR JSON, binding, runtime path, and options; direct interpretation executes OIR with an execution profile. Neither is a general admitted `oir-realize` result. | Separate effectful realization production from target-specific `RealizesOir` checking; admit the realization only after the named relation is established or an explicit trusted-producer boundary is accepted. | Production/build success and selected-vector evidence are not universal semantic preservation. | Each target must declare artifact identity, production occurrence, checker grade or trusted boundary, exact supplier/toolchain closure, and partial publication behavior. | Stage 4B Realization |
| E4 | **New** | General deployment is architecture-only and has no implemented binding, activation, or capability lifecycle. | `Prepare deployment` admits immutable role/resource/policy configuration; `Activate deployment` creates a live scoped, possibly revocable deployment capability and an occurrence observation. | Deployment configuration is portable content; activation is effectful current authority and may fail partially. | Separate IDs/types are required for deployment binding, instance/occurrence, and live authority, with explicit rollback or residue reporting where meaningful. | Stage 4B Realization/operations |
| E5 | **Reframe** and **New** | Direct CLI/library invocation returns verifier verdict or prover bytes under an execution profile; a generalized Interface-aware invocation binding and full run lifecycle are absent. | Bind exact Interface, live deployment, request, inputs, policy, and capabilities into a narrow invocation capability; execution returns a role-specific completed result plus operational observation or typed failure. | Malformed interface input, authority refusal, resource failure, verifier rejection, and prover completion have different owners and meanings. | APIs must separate bind refusal from execution, preserve verifier rejection as completed semantics, and identify the run occurrence without reminting Protocol/OIR identity. | Stage 4B OIR/Realization |
| E6 | **Reframe** and **New** | Current endpoint prose asks for attributable run facts, but public result types are narrower and observations remain distributed among results, diagnostics, logs, fixtures, and reports. | Producing domains emit occurrence-scoped raw observations; Evidence forms an `EvidenceRecord` over an exact claim, subjects, issuer, procedure, environment/pins, regime, and disclosure scope. | A semantic result and an attributable record about its occurrence have different schemas, confidentiality, retention, and trust. | OIR/Realization define raw observations; Evidence authenticates and packages only claimed facets without making the record prove its claim. | Stage 4B raw run/observation; Stage 6 Evidence record |
| E7 | **New** | There is no generalized implemented evidence appraisal or scoped reliance-decision authority. | `Appraise evidence` returns policy-qualified positive, negative, insufficient, stale, or indeterminate assessment. A separate consumer-owned decision permits, denies, conditions, limits, or defers one intended use. | Record validity, claim support, and permission to act can legitimately differ by consumer, time, trust anchors, and policy. | Assessment and reliance must be separate typed inputs/outputs; no evidence or policy result may flow backward into Protocol, OIR, or realization meaning. | Stage 6; each relying consumer owns its concrete policy |

## 7. Retirement ledger

The following target exclusions are cross-cutting enough to state together.
They are architectural prohibitions for the selected model, not assertions
that every current code path exhibits the pattern and not instructions to
delete an implementation:

| Retired pattern | Replacement | Owner of enforcement |
|---|---|---|
| Carrier labels or routes as undeclared semantic/interface inputs | Identified Protocol, Interface, Plan, or explicit transition input | Stages 3 and 4B |
| A broad retained resolver as permission for later ambient lookup | Minimal identified dependency/admission basis plus transition-specific closure | Every semantic owner; Stage 7 audit |
| Raw mutable `pir.sealed` handles as public admission authority | Opaque immutable admitted capability over authenticated content | Stage 3 |
| Construction routes as an implicit Prover Plan | Explicit admitted Plan with one declared consumption boundary per field | Stages 3, 4A, and 4B |
| One `valid`/failure channel for negative judgment, unsupportedness, refusal, rejection, and operational failure | Relation-owned typed outcomes preserving independent dimensions | All domain stages |
| Provenance adjacency or matching IDs as semantic composition | Explicit relation, property-transport, Protocol-composition, or effect-sequencing law | Stages 3--5 |
| Source-free OIR admission as evidence of source projection coverage | `LocalOirValid` only; source-relative `ProjectionCorrect` requires exact source inputs | Stage 4B |
| Parsed supplier/deployment configuration as live authority | Re-resolved narrow process-local provider/deployment capability | Stage 4B |
| Production, build, fixture, or run success as universal realization correctness | Named target-specific `RealizesOir` result or explicit residual trusted boundary | Stage 4B |
| Observation or authentic record as self-appraisal or use authorization | Observation -> EvidenceRecord -> ClaimAssessment -> consumer RelianceDecision | Stage 6 |
| Speculative universal transition/fact artifact | Domain-owned results and purpose-specific certificates for named consumers | Stage 5 reopening gate; Stage 7 default |

## 8. Coverage audit

Every transition family required by the Stage 2 charter is represented:

| Charter boundary | Map row |
|---|---|
| Author or import | L1 |
| Resolve for seal | L2 |
| Seal | L3 and L8 |
| Persist, decode, admit | L4 |
| Derive consumer view | L5 |
| Reopen and discard authority | L6 |
| Static link | L7 |
| Checked Protocol transform and successor authentication | S6 |
| Relation-interface ingress | S3 |
| Post-seal relation correspondence | S4 |
| Property analysis | S5 |
| OIR projection | E1 |
| Supplier binding | E2 |
| Endpoint realization | E3 |
| Deploy | E4 |
| Invoke | E5 |
| Record or attribute observation | E6 |
| Appraise evidence and make a use-specific reliance decision | E7 |

The map also covers boundaries introduced by the selected Stage 1/2 target:
typed regimes and exact closure (X2--X3), Interface and Plan admission
(S1--S2), semantic Protocol composition (L7), FS Protocol construction and
`FSCompile` (S7), property transport (S8), standalone OIR admission (E1),
realization checking (E3), deployment activation and invocation binding
(E4--E5), and the full evidence/appraisal/reliance chain (E6--E7).

## 9. Later-stage handoff

The rows above allocate meaning, not implementation order:

- **Stage 3** must make Core, Protocol, canonical PIR, lifecycle, Interface,
  Plan, relation ingress/correspondence, FS construction/bridge, and structural
  composition exact. It inherits the closure, capability, and typed-outcome
  constraints rather than a ready-made schema.
- **Stage 4A** must make property subject selection, derivation, successful
  negatives, checked Protocol relations, compiler domain/selection,
  `FSCompile` cooperation, and `PropertyTransport` exact.
- **Stage 4B** must make OIR observables, `LocalOirValid`,
  `ProjectionCorrect`, plan placement, supplier binding, `RealizesOir`,
  deployment, invocation, effects, and raw observations exact.
- **Stage 5** must test the joined system for additional composition modes and
  named independent consumers. It is the principal reopening point for
  purpose-specific certificates or a stronger portable package.
- **Stage 6** must define evidence records, appraisal, freshness/trust, and
  reliance without semantic backflow.
- **Stage 7** must assign normative owners, reconcile regimes/identities and
  remove duplication across the complete corpus.
- **Stage 8** alone turns the selected contracts into a checkout conformance
  classification and implementation plan.

## 10. Reversal and coverage notes

The selected architecture should be reopened, with the affected owner and
claim named, if later concrete evidence shows any of the following:

1. Two or more relation families have genuinely identical semantics,
   authority, lifetime, composition, and consumer requirements sufficient to
   justify a shared executable algebra.
2. A named independent consumer requires a uniform portable transition graph
   and cannot be served by domain adapters or purpose-specific records.
3. Re-admission or direct rechecking is unavailable or uneconomic while a
   stable, materially smaller claim checker and certificate can be defined.
4. A proposed validator must duplicate the complete producer or access hidden
   private state, so the claimed trust reduction is not real.
5. A hidden read changes an outcome after advertised inputs remain equal; the
   input closure, regime, or owning subject must then be corrected.
6. An Interface or Plan field cannot be assigned to exactly one side of the
   Protocol/OIR/realization boundary without changing protected Protocol
   behavior.
7. An effectful activity has no meaningful completion or partial-effect
   frontier, requiring its operational contract to be reformulated.
8. A new source-bearing proof permits a standalone OIR consumer to check
   source coverage; that proof would be a new relation input, not an inference
   from `LocalOirValid`.

`Keep` never means that current files, names, schemas, or implementations are
already ideal. `Retire` never authorizes removal before Stage 7 authority
consolidation and Stage 8 conformance planning. A reversal must state the exact
subjects, regimes, identities, authority, relation, consumer, compatibility
promise, and neighboring transitions affected.

## 11. Non-claims

This map does not claim that:

- the selected target has been specified normatively, implemented, tested,
  benchmarked, formally verified, or migrated;
- the current conflicts cataloged here are security findings or implementation
  bugs;
- current code must be reorganized to mirror the target documentation;
- every proposed checker has a practical independent implementation or compact
  witness;
- any portable certificate, transition wire format, global fact store, or
  complete carrier-neutral Protocol package is required in v0;
- an admitted Protocol is sound, complete, relation-satisfying, projectable,
  realizable, deployed, or suitable for a particular use; or
- Stage 2 has chosen exact public type names, encodings, hashes, diagnostics,
  policies, APIs, migration order, or compatibility behavior.

The gap map is complete at the architectural boundary level defined by the
Stage 2 charter. Completeness of the later domain schemas, proofs, targets,
policies, and implementation correspondence remains the responsibility of
their named stages.
