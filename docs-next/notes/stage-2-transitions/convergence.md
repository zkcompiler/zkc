# Stage 2 transition and bridge convergence

> **Document kind:** Temporary Stage 2 research convergence record
> **Document state:** Complete Stage 2 convergence; absorbed into durable
> architecture and retained as a temporary research record
> **Authority:** None. This page records the reviewed Stage 2 target decision.
> It does not define normative syntax, mint a capability, select a public API
> or wire format, authorize implementation work, or begin Stage 3.
> **Decision scope:** Transition ownership, authority, closure, identity,
> outcome, replay, composition, checker-placement, persistence, Interface,
> ProverPlan, operational-effect, Evidence, and relying-policy boundaries.
> **Inputs:** The selected
> [Stage 1 architecture](../../project/protocol-ir-architecture.md), the
> [Stage 2 charter](../stage-2-transition-and-bridge-charter.md), the
> [current catalog](current-transition-catalog.md),
> [external cases](cases/transition-and-checking-models.md),
> [candidate frameworks](candidate-frameworks.md),
> [lifecycle](lifecycle-spine.md),
> [semantic bridges](semantic-bridges.md),
> [endpoint and operational bridges](endpoint-operational-bridges.md), the
> [cross-case synthesis](cross-case-synthesis.md), the
> [selected target catalog](target-transition-catalog.md), and the
> [scenario results](scenario-results.md).
> **Precedence inside this temporary package:** The decisions and
> rectifications on this page explain the selected result; their corrections
> have been incorporated into the target catalog and durable architecture.
> The durable architecture owns the selected non-normative target.
> **Disposition:** Durable promotion, the bounded Stage 3 entry contract, and
> closure validation are complete. Retain this package as research evidence
> until the later deletion gate.

## 1. Decision

Stage 2 **ratifies the disciplined hybrid**, with the corrections in Section
4:

```text
project-owned descriptive discipline and cross-domain invariants
        |
        +--> domain- and bridge-owned subjects, relations, and judgments
        +--> capability-centric process-local authority lifecycle
        +--> direct recomputation for small closed predicates
        +--> proposal plus relation-specific validation when checking is
        |    materially smaller, more stable, or independently realizable
        +--> explicit trusted boundary when no such validator exists
        +--> effect contracts and occurrence observations for live activity
        +--> policy application for appraisal and reliance
        `--> purpose-specific durable result only for a named consumer
```

This is one architectural rule for choosing among several mechanisms, not an
agreement to let each subsystem improvise. Every transition must expose the
same descriptive questions about exact subjects, authorities, read closure,
semantic regimes, identity effects, outcomes, replay, composition, residual
trust, and consumer need. The answer remains owned by the domain whose
proposition or effect is at stake.

The selected v0 target has:

- no universal transition semantic type;
- no global `TransitionId`;
- no universal transition artifact, certificate, validity bit, checker
  registry with semantic authority, or generic composition law;
- no serialized continuation of process-local authority; and
- no backward authority path from observation, Evidence, appraisal, or
  reliance into semantic subjects.

The useful commonality is a lintable, inspectable **projection of concrete
contracts**. It may support documentation generation, catalog queries, graph
views, API-conformance checks, and later orchestration. It is not a fact root
and does not interpret an unknown domain relation.

## 2. Why this decision survived convergence

The conclusion rests on four independent evidence classes.

1. **Fixed Stage 1 architecture.** Protocol, Interface, Plan, OIR, Analysis
   judgments, operational observations, and reliance decisions are already
   distinct subject or result categories. Fresh-public-coin and Fiat--Shamir
   Protocols share a Core but have different Protocol identities and require
   a separate `FSCompile` relation.
2. **Current reconstruction.** The checkout already distinguishes decode from
   admission, paired source/OIR authority from standalone OIR validity,
   property judgments from Protocol authority, checked successors from
   compiler selection, and verifier rejection from operational failure. It
   does not contain one latent universal relation or one current consumer for
   a heterogeneous transition wire object.
3. **External mechanisms.** Verified compilation and translation validation
   require an exact relation and accepted domain; proof-carrying and
   certificate models justify evidence only for a precise claim and checker;
   MLIR legality is structural rather than semantic proof; capability models
   distinguish live authority from data; transport specifications distinguish
   decoding, integrity, and compatibility; and provenance/appraisal systems
   distinguish statements, evaluation, and reliance. None supplies a complete
   zkc design by analogy.
4. **Integrated scenarios.** The hybrid preserves every required distinction
   across equivalent authoring histories, cross-process re-admission,
   Interfaces, Plans, relation disagreement, negative analysis, FS
   construction, search-heavy compilation, source-free OIR, target refusal,
   suppliers, realization, partial effects, and divergent relying policies.
   No tested scenario needs Candidate B's universal semantic or wire center.

Migration convenience, current class names, and the current MLIR carrier did
not decide the clean target. Current evidence was used to find hidden inputs,
authority discontinuities, and actual consumers, not to preserve accidental
API shape.

## 3. Candidate verdicts

| Candidate | Convergence decision | Selected contribution | Why the rest is not selected | Reopening evidence |
|---|---|---|---|---|
| A: domain-owned typed contracts | **Selected as the global ownership baseline** | Concrete owners define subject meaning, exact relations, judgments, effects, diagnostics, and refusal semantics; Project owns the descriptive completeness discipline | A alone does not enforce local least authority or decide checker placement | Domain adapters repeatedly fail to preserve common closure, outcome, replay, or composition discipline even with linting and cross-owner review |
| B-local: universal typed algebra | **Not selected as the v0 semantic center** | Typed references, inspectable catalog projections, and graph tooling are retained without semantic authority | Important relations have no shared algebra or generic composition law; domain dispatch would retain all real semantics while adding a central runtime layer | A proven subset of important pure relations has identical laws and a named generic consumer gains materially more than adapters cost |
| B-wire: universal transition artifact | **Rejected as a v0 product commitment** | No universal wire contribution is selected | It would freeze subject references, outcomes, relation kinds, witnesses, effects, provenance, and evolution before owners or consumers stabilize | A named heterogeneous cross-process consumer, retention window, stable registry, independent checker model, and demonstrated advantage over purpose-specific objects all exist |
| C: capability-centric lifecycle | **Selected for process-local authority gates** | Authentication, admission, views, projection, binding, deployment, and invocation use narrow opaque authority with explicit lifetime and serialization loss | Capabilities do not define mathematical truth, portable evidence, occurrence semantics, or relying policy | Authority cannot be enforced without ambient mutable state, FFI or distribution makes reconstruction impractical, or capability proliferation obscures rather than narrows authority |
| D: proposal plus per-edge validation | **Selected conditionally per edge** | Search-heavy normalization, checked Protocol change, projection, property derivation, and realization may separate a volatile proposer from a stable exact checker | A producer/witness layer adds no value for cheap checks; invocation is not replayable validation; a duplicate checker does not reduce trust | Per-edge measurement shows the checker duplicates production, needs unavailable private state, cannot state incompleteness honestly, or has no consumer benefit |
| A + C + selective D + direct/effect/policy alternatives | **Selected v0 transition architecture** | Local semantic ownership, explicit authority, demand-driven validation and persistence, and low default wire commitment | It requires disciplined catalog maintenance and exact per-family specifications | A simpler architecture passes the same closure, authority, scenario, composition, and consumer tests with materially lower cost or greater option value |

Candidate letters refer only to the Stage 2 transition-framework portfolio.
They do not rename or modify the completed Stage 1 IR alternatives.

## 4. Rectifications incorporated into the selected target catalog

The [target transition catalog](target-transition-catalog.md) is the complete
selected target inventory. The following corrections were incorporated into
it before durable promotion.

| Provisional tension | Converged resolution | Reason |
|---|---|---|
| The semantic-bridge dossier types relation correspondence over an `AuthenticatedProtocolInterface`, while the endpoint dossier and target catalog require an admitted Interface | A normative Interface-sensitive bridge consumes `AdmittedProtocolInterface[I -> P]`. Authentication only authorizes the separate Interface admission step | External decoding and binding must satisfy the complete Interface predicate before another domain relies on them; mere identity authentication is too weak |
| Relation-artifact interpretation is variously called an observation, judgment, or “negative interpretation result” | Its primary result is `RelationArtifactObservation`. Formation, format mismatch, cross-checked mismatch, unavailable dependency, unsupported adapter, and I/O failure remain typed outcomes. Only the later Relations-owned correspondence step yields `RelationCorrespondenceJudgment` | A format reader observes or attributes facts; it does not own Protocol/relation correspondence or relation truth |
| The target catalog's checker matrix can be read as already selecting a portable property-derivation artifact | No portable derivation schema is selected in Stage 2. A checked derivation is a strong **candidate** for persistence when a named independent consumer, stable checker, closure, retention need, and compatibility policy exist | A plausible consumer shape is not an actual consumer or product promise; the same consumer-justified persistence gate applies everywhere |
| The projection row can be read as collapsing target-local formation and source-relative coverage into one capability | Projection success establishes two logically named results: `LocalOirValid(O)` and `ProjectionCorrect(P,I,role,basis,O)`. One paired in-process capability may carry both bases, but serialization leaves an OIR subject that must be locally re-admitted and does not retain source coverage | Target-local validity and source/target coverage have different input closures, replay behavior, and source-free meaning |
| Plan admission and `PlanRealizes` were at risk of being collapsed into one authority | Plan admission establishes Plan-owned well-formedness and dependency closure. The separate `PlanRealizes(L,P)` judgment establishes structural obligation accounting. An admitted plan-coverage capability is only a local wrapper over that checked relation, not a second semantic predicate | Plan formation, authentication, admission, structural coverage, projection, realization, and honest-prover completeness must remain separate |
| A canonical candidate “claims” Core, construction, and Protocol IDs before authentication | Claimed IDs are unauthoritative expected values. `Authenticate` independently recomputes canonical form, dependency closure, regime-qualified identities, and any expected-ID equality | Candidate metadata cannot become identity authority through producer assertion |

No correction changes the candidate verdict or transition topology. The first
four close real category ambiguities; the last two constrain terminology so a
later schema cannot inflate authority.

## 5. Ratified charter-level choices

The following table decides every cross-cutting choice left to Stage 2. Names
remain semantic roles rather than selected API spellings.

| Choice | Decision | Consequence |
|---|---|---|
| Contract ownership | Source, bridge/checker, target, and relying-consumer authority are named independently; the exact proposition stays with its domain or bridge owner | Shared tooling may require fields but cannot decide their truth |
| Common layer | Use a descriptive contract schema, typed reference vocabulary, global invariants, and completeness linting | No universal runtime sum type, fact root, or wire authority follows |
| Subject references | References are family-, identity-, and regime-qualified; occurrence, contract, policy, and subject references remain different categories | Equal bare digests do not establish substitutability across regimes or subject families |
| Lifecycle center | Use `AuthoringUnit -> ResolvedAuthoringUnit -> CanonicalProtocolCandidate -> AuthenticatedCanonicalProtocol -> AdmittedProtocol` as the logical spine | One implementation may fuse traversals but must preserve each logical postcondition and refusal |
| Author/import | Treat both as unauthoritative proposal formation; source correspondence is a separate optional claim | Parser, importer, or generator success never admits a Protocol |
| Resolve | Resolve against an immutable snapshot and bind the exact typed `ResolutionClosure` actually read | Uncited resolver growth is normatively irrelevant |
| Normalize | Produce the one physical closed canonical candidate plus typed side outputs; do not trust producer history or claimed IDs | Authentication and admission remain independent of normalizer search |
| Authentication versus admission | Keep identity/dependency authentication logically separate from whole-Protocol semantic admission | Neither identity equality nor canonical legality implies admissibility or a cryptographic property |
| Retained basis | Retain only the immutable regime, dependencies, and checker basis needed for advertised operations | Broad registries and future opportunistic reads are forbidden inside admitted authority |
| Official Protocol persistence | Gate the canonical deployable artifact writer on `AdmittedProtocol`; if candidate interchange is later needed, use a visibly unauthoritative workbench/cache envelope | Producer-side grade is clear, while every receiver still re-authenticates and re-admits |
| Representation boundary | Serialization, raw copying, mutation, reopening, and unmediated FFI end local capability continuity | Bytes may preserve authenticated subject identity only after checking; they never preserve authority by assertion |
| Semantic regimes | Separate subject, relation/judgment, checker, carrier/transport, local-admission-policy, evidence-policy, and intended-use-policy regimes | Cross-regime use needs an explicit migration, correspondence, or intentional-change relation |
| Consumer views | Derive question-scoped views from admitted subjects and exact auxiliary inputs | Views are not mutable mirrors or a universal fact root |
| Protocol Interface | Authenticate and admit a separately identified dependent Interface; every Interface-sensitive bridge consumes its exact admitted capability | Carrier labels and packaging metadata cannot be hidden bridge inputs |
| Prover Plan | Authenticate and admit a separately identified Plan, then check structural `PlanRealizes` separately | Plan admission is not completeness, supplier correctness, projection, or realization |
| Plan placement | Use `InterfaceOnly` or `InterfaceAndPlan` explicitly. A Plan enters OIR identity exactly when projection reads it; otherwise it is an explicit below-OIR realization input | Verifier projection never consumes a Plan; one Plan field cannot arrive ambiently at two seams |
| Authoring link versus Protocol composition | Keep raw authoring link distinct from admitted semantic composition | Composition constructs a new Core candidate with explicit occurrences, seams, schedule, challenges, failures, terminals, dependencies, and obligations |
| Relation ingress | Admit the relation-domain interface before optional artifact interpretation | Relation bytes, interface meaning, Protocol identity, and relation truth remain separate |
| Relation correspondence | Check exact `(Protocol, Interface, relation interface, optional artifact observation, regime)` and allow affirmative or successful negative judgments | Correspondence proves neither relation truth nor witness satisfaction |
| Property analysis | Select the exact property-subject tuple; check an explicit derivation plan under an Analysis-owned basis; allow conditional, quantitative, affirmative, supported negative, inconclusive, unsupported, and refusal outcomes | Search failure is not negative truth; Interface- or Plan-sensitive questions name those subjects |
| Checked Protocol change | Propose a target, independently authenticate and admit it, then check one exact predecessor/target relation with observers, maps, assumptions, regimes, and intentional changes | Target admission and relation truth are independent; property transport is separate |
| Compiler selection | Select only among already admitted, relation-checked candidates under a complete declared domain, constraints, objectives, ties, and configuration | “Best” means best only over that checked domain; no decision artifact is selected by default |
| Fiat--Shamir | Construct and admit an FS Protocol separately from checking theorem-backed `FSCompile`; transport each property through an Analysis-owned rule | Shared Core does not mean equal Protocol, universal preservation, or automatic security transport |
| OIR projection | Consume admitted Protocol, admitted Interface, role, tagged Plan basis, OIR regime, and exact dependencies; keep `LocalOirValid` distinct from `ProjectionCorrect` | Source-free OIR can be locally used but reports source coverage as unknown without sufficient source-bound checking |
| Supplier binding | Form an exact identified designation over OIR requirements, optional below-OIR Plan, target, supplier snapshot, and binding regime; keep live provider authority separate | Selection and ABI compatibility do not prove provider correctness or permanent availability |
| Realization | Separate effectful production from `RealizesOir` checking; use a target validator only when practical, otherwise state a verified or trusted producer boundary honestly | Emission, deterministic bytes, tests, and packaging do not prove semantic realization by themselves |
| Deployment and invocation | Separate deployment specification, binding, activation, live capability, invocation binding, execution result, and occurrence observation | Verifier rejection is a completed semantic result; supplier refusal, operational failure, and partial effects are different outcomes |
| Evidence and reliance | Preserve `observation -> EvidenceRecord -> ClaimAssessment -> RelianceDecision`, with the producer, Evidence owner, and relying consumer distinct | Attribution is not truth, appraisal is not universal permission, and reliance cannot change semantic history |
| Checker placement | Choose in order: direct recomputation; smaller per-result validator; explicit trusted procedure; effect contract; policy application | No checker is called independent merely because a producer is rerun |
| Persistence | Introduce a domain-owned durable checked result only for a named process, trust, release, cache, audit, or retention consumer with stable closure, checker, compatibility, and supersession rules | “No transition artifact” is a complete design choice, not unfinished work |
| Identity | Domain subjects use domain identity; checked results use domain result identity only if persisted; effects use occurrence identity; capabilities normally have no semantic identity | Producer trace, certificate, subject, configuration, and occurrence IDs never collapse into a global transition ID |
| Outcomes | Preserve procedure, input, check/judgment, authority, and effect dimensions; each owner exposes only valid combinations | Negative judgment, unsupportedness, inconclusive checking, refusal, operational failure, partial effect, appraisal, and denial cannot collapse into one Boolean or error |
| Replay | Qualify every replay as recomputation, independent validation, certificate verification, re-authentication/re-admission, observational reproduction, or non-replayable attribution | Operational replay creates a new occurrence; byte replay does not reconstruct authority automatically |
| Composition | Distinguish procedural sequencing, relation-specific mathematical composition, certificate conjunction or checked chaining, Protocol/Core composition, operational sequencing, Evidence aggregation, and reliance | Matching intermediate IDs or graph adjacency never establishes an end-to-end theorem |

## 6. Fixed v0 transition invariants

The following invariants are mandatory inputs to every later owning stage.
They are fixed at the architectural level even though exact domain schemas are
not yet selected.

1. **Typed subject rule.** Every semantic source, target, auxiliary subject,
   occurrence, contract, policy, and regime is typed and independently
   identifiable where its owner requires identity.
2. **Extensional closure rule.** For a deterministic semantic transition,
   equal admitted sources, explicit auxiliaries, exact dependency closure,
   semantic/checker regimes, and result-affecting configuration produce the
   same normative outcome. A changed result exposes a missing input or a
   wrongly classified effect.
3. **Minimal-authority rule.** A capability carries only the immutable checked
   basis and permitted operations it advertises; additional material enters a
   later transition as an explicit typed input.
4. **One-primary-postcondition rule.** A physical procedure may return several
   logical results, but formation, authentication, admission, relation
   checking, operation, appraisal, and reliance remain separately named.
5. **Named-relation rule.** `valid`, `verified`, `lowered`, `preserved`, and
   `checked` are insufficient without the exact domain relation, direction,
   admitted domain, observers, assumptions, quantities, and limits.
6. **Identity-effect rule.** Each contract declares identities consumed,
   preserved, constructed, related, configured, instantiated, observed,
   decided, or cited only as provenance.
7. **No-identity-laundering rule.** Equal `ProtocolId` cannot substitute for
   equal Interface, Plan, regime, checker, target, supplier, capability,
   observation, assessment, or policy inputs.
8. **Capability-loss rule.** Bytes, mutable derivatives, unmediated FFI, and
   process crossings contain data and references, not a live admission,
   correspondence, deployment, or invocation capability.
9. **Protected-observer rule.** Equivalence, refinement, distributional
   correspondence, projection, realization, and intentional change name every
   protected observer and the relation direction.
10. **Qualified-outcome rule.** Successful negative results, refutation,
    unsupportedness, inconclusive checking, malformed input, refusal,
    operational failure, partial effects, negative appraisal, and reliance
    denial remain distinguishable.
11. **Scoped-replay rule.** A replay claim names exactly what is repeated,
    which closure is reconstructed, and which proposition or observation it
    establishes.
12. **Lawful-composition rule.** Semantic composition requires an explicit
    theorem or constructor; procedural adjacency, matching IDs, certificates,
    provenance, appraisal, and reliance do not supply one.
13. **No-backflow rule.** Target validity, execution results, observations,
    Evidence, appraisal, and reliance cannot redefine upstream meaning or mint
    upstream authority.
14. **Fail-closed-extension rule.** Unknown meaning-bearing subject,
    relation, regime, witness, effect, Evidence, or policy kinds are
    unsupported for semantic use, even if their outer transport is retained.
15. **Consumer-justified-persistence rule.** Every durable checked result names
    its consumer, exact claim, checker, closure, retention and compatibility
    promise, authentication, supersession, and cheaper rejected alternative.
16. **Effect-frontier rule.** Live production, deployment, invocation, and
    recording name external actions, completion, publication, residual state,
    retry/idempotence, cleanup/compensation, and capability consumption.
17. **Producer-independence rule.** Target semantic identity excludes search
    history, heuristic seeds, producer release, score, and witness unless they
    change canonical target meaning. Several producers may converge on one
    target without merging their attempts or evidence.

These rules are the common semantic discipline. A later generic mechanism may
be extracted only after at least two concrete transitions demonstrate the same
semantic role, authority issuer and lifetime, outcome meaning, replay and
serialization behavior, composition law, and relying-consumer need.

## 7. Selected transition topology

The target inventory is complete at Stage 2 resolution:

```text
author / import
  -> resolve
  -> normalize canonical candidate
  -> authenticate Protocol
  -> admit Protocol
  -> persist / decode / re-authenticate / re-admit
  -> derive scoped view / reopen

raw authoring link
admitted Protocol composition -> new candidate -> ordinary authentication

Interface candidate -> authenticate -> admit
Plan candidate -> authenticate -> admit -> check PlanRealizes
relation interface -> authenticate/admit -> optional artifact observation

property analysis
Protocol successor proposal -> target admission -> exact step checking
compiler domain checking -> selection
FS Protocol construction -> FSCompile -> property-specific transport

Protocol + Interface + role + tagged plan basis
  -> locally valid OIR + ProjectionCorrect paired authority
  -> standalone OIR re-admission loses source-relative authority
  -> exact supplier binding
  -> effectful realization production -> RealizesOir check
  -> deployment preparation -> activation
  -> invocation binding -> execution result + observation
  -> Evidence record -> appraisal -> use-specific reliance
```

The detailed contracts, owner matrices, closure tables, identity effects,
outcomes, replay classes, and checker alternatives are retained in the target
catalog and its lifecycle, semantic, and endpoint dossiers as research and
handoff detail. The corrections in Section 4 are part of this selected
topology.

## 8. Interface and ProverPlan closure

### 8.1 Interface

`ProtocolInterface` is an authenticated and admitted dependent subject over
one exact `ProtocolId`. It may own external names, positions, containers,
entry points, malformed external-input behavior, and codecs only when they
decode before and preserve fixed Protocol meaning. It may not change public
semantic values, proof-event order, transcript inputs or framing, challenges,
checks, claims, terminals, proof ABI already observed by Protocol, or the
accepted language.

Protocol-level questions do not read an Interface. External relation
correspondence, endpoint projection, external acceptance, realization ABI,
and invocation consume the exact admitted Interface. Compiler requests may
cite one explicitly, but a resulting Protocol relation cannot hide it.

Stage 3 must provide the complete field ledger, identity preimage, admission
predicate, and narrow exported views. The fixed test is substitutive: changing
an omitted Interface while all declared inputs remain equal must not change a
normative result.

### 8.2 ProverPlan

`ProverPlan` is an authenticated and admitted dependent subject over one exact
`ProtocolId`. Protocol owns abstract prover obligations and their canonical
occurrences. Plan owns a construction or witness DAG, private dependencies,
and eligible below-Protocol choices. Structural `PlanRealizes` accounts for
every abstract obligation by a Plan step or an explicit typed unresolved
requirement.

Neither Plan admission nor `PlanRealizes` establishes honest-prover
completeness, supplier correctness, performance, verifier acceptance, or
backend realization. Those require separate Analysis, binding, realization,
or execution results.

Each Plan field has one earliest semantic reader:

```text
changes canonical prover OIR
  -> explicit InterfaceAndPlan projection basis
  -> ProverPlanId participates in OirId

changes only below-OIR algorithms, scheduling, buffering, or suppliers
  -> plan-independent OIR
  -> exact admitted Plan enters supplier binding or realization
```

A field that changes proof events, distributions, transcript actions, checks,
external proof ABI, or accepted language belongs to a different Protocol, not
to a Plan. Verifier projection never consumes a Plan.

## 9. Outcomes, replay, and composition

The conceptual outcome factorization is ratified for review and schema design,
but it is not one mandated runtime enum:

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

Concrete owners define the valid product subset. For example, a complete
negative property decision is `Completed + Established + Negative`; a sound
incomplete checker that cannot decide is `Inconclusive`; verifier rejection
is a completed endpoint result; missing supplier authority is a refusal or
operational failure; and a reliance denial is a successful consumer-policy
decision.

Replay names one or more exact classes:

| Class | Establishes |
|---|---|
| Deterministic recomputation | The same result under the same closed pure contract |
| Independent validation | One named relation for exact proposed subjects within checker scope |
| Certificate verification | Only the durable claim encoded under the exact checker regime |
| Re-authentication and re-admission | New local authority over a reconstructed semantic subject |
| Observational reproduction | A new occurrence and observation under a named environment |
| Non-replayable attribution | Who reported what under which procedure, not truth or reproducibility |

Composition has no global transitivity. Procedural sequencing passes typed
preconditions. A relation theorem carries exact maps, observers, assumptions,
losses, and regimes. Certificate chaining establishes only a separately
checked conjunction or composed claim. Protocol composition constructs a new
Core. Operational sequencing owns causal effects and partial failure.
Evidence aggregation and reliance remain policy operations.

## 10. Current-to-target gap and conflict disposition

The current checkout is correspondence evidence, not a constraint on the
ideal model. The following inventory is sufficient to route later design and
implementation work without treating the gaps as defects.

| Area | Current correspondence | Selected target difference | Later owner |
|---|---|---|---|
| Regimes | Revision, exact references, profiles, and providers serve as several implicit version axes | Typed subject, relation, checker, transport, and policy regimes are explicit and noninterchangeable | Stage 3 first; each later domain completes its regime |
| Seal lifecycle | Resolution, identity, semantic checks, and carrier mutation are substantially fused | Logical Resolve, Normalize, Authenticate, and Admit postconditions are separate; one traversal may implement them | PIR in Stage 3 |
| Admission closure | Admitted PIR retains a complete `ProtocolEnvironment` beyond the identity-cited subset | Retain the minimal immutable admission basis; later inputs are explicit | PIR in Stage 3; consuming domains own added inputs |
| Interface | Relations and projection can read author labels erased from Protocol identity | Admitted `ProtocolInterfaceId` closes every Interface-sensitive bridge | PIR/Relations in Stage 3; OIR in Stage 4B |
| Plan | Construction routes are embedded and no separate Plan subject exists | Dependent `ProverPlanId`, Plan admission, structural `PlanRealizes`, and explicit placement | PIR in Stage 3; Analysis/OIR/Realization later |
| Linking and composition | Current static link returns raw Open PIR | Retain raw authoring link and add a distinct semantic Core constructor | PIR/Relations in Stage 3 |
| Relation ingress | Current relation contracts are loaded post-seal; no admitted pre-Protocol interface role exists | Independent relation-interface admission, optional artifact observation, then exact correspondence | Relations in Stage 3 |
| Relation disagreement | Specification language can read as refusal while the tool emits a negative disagreement report | After both subjects form and comparison runs, disagreement is a successful negative judgment; malformed, unsupported, or unavailable inputs are not | Relations in Stage 3 |
| Analysis | Selected derivations and portable witnesses exist over current artifact-qualified subjects | Exact question-selected Protocol/Interface/Plan/relation subjects and regimes; no durable general schema selected yet | Analysis in Stage 4A |
| Compiler | Successor re-admission and deterministic replay share producer-side implementations and environment | Per-result named relation validation where economical; bounded selection recomputation; honest trusted boundary otherwise | Compiler/Analysis in Stage 4A |
| Fiat--Shamir | Current analysis uses the earlier artifact-qualified model | Distinct FS Protocol construction, theorem-backed `FSCompile`, then property-specific transport | PIR/Relations Stage 3; Analysis Stage 4A |
| Projection | Paired PIR/OIR backing checks coverage; standalone OIR checks local facts; labels and routes remain carrier-derived | Exact Interface/role/tagged-Plan input; explicit `LocalOirValid` and `ProjectionCorrect`; no portable projection record by default | OIR in Stage 4B |
| Supplier binding | Execution profiles and emitter binding files provide bounded configuration | Identified exact configuration plus separately admitted live provider authority | Realization in Stage 4B |
| Emission inputs | The effective current result-affecting tuple is wider than one documented tuple | Every result-affecting runtime path, target, option, vector corpus, provider, and toolchain choice is explicit in production or checking closure | Realization in Stage 4B |
| Realization | Narrow Rust emission exists without a general admitted `oir-realize` result | Effectful production and a named `RealizesOir` check are separate | Realization in Stage 4B |
| Endpoint result and record | Public execution results are narrower than the normative attributable run record | Endpoint semantic result and raw attributable operational observation are separate subjects; neither substitutes for the other | Realization in Stage 4B; Evidence in Stage 6 |
| Deployment, appraisal, reliance | General forms are architecture-only or absent | Separate configuration, live authority, occurrence, Evidence, assessment, and consumer-decision boundaries | Realization Stage 4B; Evidence and consumers Stage 6 |
| Documentation ownership | The current overview omits the separately canonical Relations owner | Durable ownership maps must name Relations explicitly | Project documentation promotion |

This table is a design handoff, not an implementation migration order. It
does not claim current code is defective, insecure, or conformant to the
selected target.

## 11. Scenario and falsification verdict

All charter scenarios have an explicit result under the selected
architecture. The review did not merely search for failures; it also recorded
option value enabled by the separation.

| Scenario group | Convergence verdict |
|---|---|
| Equivalent histories, resolver substitution, persistence, reopen, and regime/transport variation | Passes through canonical authentication, extensional closure, identity/authority separation, and mandatory re-admission |
| Two Interfaces and two Plans | Passes through explicit dependent identities and earliest-reader placement; no hidden carrier, compiler, or realization state is permitted |
| Relation ingress, later bytes, negative correspondence, and property outcomes | Passes through separate subject admission, observation, judgment, and qualified outcome products |
| FS construction, `FSCompile`, property transport, checked successors, and compiler optimum | Passes through separately checked subject formation, pair relations, property rules, and domain-completeness claims |
| Unsupported projection and source-free OIR | Passes through typed refusal plus the strict separation of local validity and source coverage |
| Supplier alternatives, realization, verifier rejection, prover output, and two deployments | Passes through configuration/content/occurrence identity separation and exact claim strength |
| Partial effects, Evidence, unknown future kinds, and missing dependency preimages | Passes through effect frontiers, no backflow, fail-closed semantic extension, and complete closure |
| Repeated-child Protocol composition | Passes only through a distinct Stage 3 Core constructor; transition or certificate chaining is explicitly insufficient |

The cross-candidate falsifiers become permanent review tests:

- hidden-read substitution is rejected by extensional closure;
- identity and capability laundering are rejected by exact auxiliary inputs
  and representation-boundary authority loss;
- relation inflation and composition laundering are rejected by named
  relations and explicit laws;
- negative-result confusion is rejected by the qualified outcome model;
- effect erasure is rejected by occurrence and partial-effect contracts;
- authority cycles are rejected by independent owner roles and no backflow;
- wire-without-consumer is rejected by the persistence gate;
- diagnostic collapse and unknown semantic kinds are rejected by typed local
  outcomes and fail-closed extension;
- validator duplication is rejected by the validator-economy test; and
- shared-mechanism extraction is rejected unless full semantic, authority,
  lifecycle, replay, composition, and consumer equivalence is demonstrated.

The architecture additionally enables multiple authoring front ends, multiple
producers behind one acceptance boundary, reusable Protocol analysis across
Interfaces, Plan-placement experiments without identity leakage, remote
checking through claim-scoped results rather than portable authority,
assurance escalation per edge, queryable provenance without a fact root,
explicit cross-regime migration, and effect-aware retries. These are enabled
options, not v0 implementation or product requirements.

## 12. Durable promotion map

The temporary research package was absorbed as follows.

| Durable destination | Material to promote | Material that must not be promoted as authority |
|---|---|---|
| `project/transition-and-bridge-architecture.md` | Hybrid decision, owner roles, common contract discipline, mechanism-selection rule, persistence gate, outcome/replay/composition model, no-backflow and extraction rules | Candidate letters, raw code-trace logs, or one universal semantic schema |
| `project/protocol-ir-architecture.md` | Stage 2 result summary, corrections, cross-stage handoff, and Stage 3 entry contract | Superseded draft wording listed in Section 4 |
| `pir/` | Lifecycle spine, canonical candidate/authentication/admission split, minimal closure, persistence grade, capability loss, Interface/Plan subject seams, Protocol composition boundary | Current fused `SealEngine` behavior as the target definition |
| `relations/` | Relation-interface ingress, artifact observation, admitted-Interface correspondence tuple, affirmative/negative judgment, ownership and non-claims | Relation truth inferred from bytes, seal, or correspondence |
| `analysis/` | Exact property-subject rule, explicit-plan derivation, successful negative/inconclusive distinctions, `FSCompile`, and `PropertyTransport` seams | An already-selected portable derivation schema or universal preservation flag |
| `compiler/` | Proposal/target-admission/relation-check/selection separation, checked-domain completeness, validator-economy rule, and explicit trusted fallback | Search success, target ID, replay, or score as relation proof |
| `oir/` | Admitted Interface/tagged Plan projection inputs, `LocalOirValid`, `ProjectionCorrect`, source-free non-claim, identity and serialization rules | Source coverage inferred from an OIR digest or embedded coordinate |
| `realization/` | Supplier configuration/live-authority split, production/check separation, realization/deployment/invocation identities, capabilities, outcomes, and effect frontiers | Emission or execution success as semantic realization or reliance |
| `evidence/` | Observation/record/appraisal/reliance chain, owner separation, attribution limits, policy and occurrence distinctions | Provenance as truth or appraisal as universal use authority |
| Future decision records | Accepted non-obvious choices, rejected universal algebra/wire default, admitted-only official persistence, and their exact reversal conditions | Temporary scenario narration or unreviewed alternatives |
| `foundation/` | Only a mechanism later proven to have identical semantics, authority, lifetime, outcomes, replay, composition, and consumers in at least two domains | Generic IDs, envelopes, or capability traits extracted merely from similar fields |

No durable page depends on this temporary file for architectural authority
after absorption. Durable pages may continue to link to it as research
evidence until the later deletion gate.

## 13. Deliberate deferrals and exact owners

Deferral preserves option value but does not weaken the fixed invariants.

### 13.1 Stage 3: Protocol semantics and Relations co-design

Stage 3 owns:

- exact `InteractiveCore`, `ChallengeInterpretation`, Protocol, canonical PIR,
  occurrence, schedule, port, event, terminal, dependency, and abstract
  obligation schemas;
- the physical canonical-form authentication predicate and whole-Protocol
  admission predicate;
- the minimal retained authentication and admission bases;
- complete Interface and Plan schemas, regimes, identity preimages,
  admission predicates, narrow exports, canonical references, and structural
  `PlanRealizes` rule;
- relation-interface schema, dependencies, identity, optional artifact
  observation, and `RelationCorrespondsAtInterface`;
- exact common definitions or ownership boundaries for the selected relation
  names, including maps, observer sets, assumptions, quantities, and
  intentional change;
- deterministic FS subject construction and the occurrence/transcript-prefix
  exports consumed later by `FSCompile`; and
- semantic Core composition, including repeated occurrences, seams,
  interleaving, domain separation, challenge behavior, failure/terminal
  propagation, dependencies, and obligations.

### 13.2 Stage 4A: Analysis and Compiler

Stage 4A owns exact property-subject variants, Analysis bases and derivation
schemas, affirmative/negative/conditional/quantitative/inconclusive variants,
checked-step schemas, compiler domain and selection contracts, validator
economics per transform family, `FSCompile` theorem/model checking, and
property-specific transport rules. It must identify an actual independent
consumer before selecting any durable derivation or checked-step format.

### 13.3 Stage 4B: OIR and Realization

Stage 4B owns exact OIR grammar and identity, projection relation and source
map, each Plan field's above/below-OIR placement, supplier requirements and
bindings, target-specific `RealizesOir`, trusted/validated backend grades,
artifact and deployment schemas, invocation/session behavior, capability
mechanics, operational outcomes, protected effect frontiers, retry, cleanup,
and raw run observations.

### 13.4 Stage 6: Evidence and relying consumers

Stage 6 owns Evidence record schemas, attribution and authentication,
disclosure and retention, appraisal policy and freshness, assessment
aggregation, and the interface to consumer-owned reliance decisions. Each
consumer still owns its intended-use policy; Stage 6 cannot centralize all
permission.

### 13.5 Project/product and implementation work

Project/product work owns any concrete independent release, cache, audit, or
retention consumer and its compatibility window. Only that evidence can
justify a new claim-scoped durable artifact. Implementation architecture,
migration order, language APIs, code generation, tests, and compatibility
follow the owning specifications; none is selected in Stage 2.

## 14. Reversal conditions

The selected architecture is intentionally revisable under evidence, not
preference alone.

1. Reconsider a shared executable algebra only when important transition
   families demonstrate identical semantics, authority, outcomes, replay,
   composition, and consumer need, and adapters otherwise duplicate that
   algebra.
2. Reconsider a universal wire object only for a named heterogeneous
   cross-process consumer with a stable relation registry, independent
   checkers, retention/compatibility promise, and measured advantage over
   purpose-specific results.
3. Reconsider capability-first local authority if exact closure cannot be
   enforced, handles capture mutable ambient state, cross-language loss cannot
   be made explicit, or legitimate consumers cannot reconstruct authority
   economically.
4. Reconsider proposal/validator separation per edge when validation
   duplicates production, requires hidden/private unavailable state, cannot
   expose incompleteness, or is less stable than the producer.
5. Reconsider direct rechecking or the no-certificate default when a named
   consumer cannot access the required checker or inputs, cost is
   prohibitive, or an independent trust/release/retention boundary requires a
   smaller claim-scoped proof.
6. Reconsider admitted-only official Protocol persistence when a concrete
   supported workflow must exchange canonical pre-admission candidates and a
   distinctly unauthoritative cache envelope cannot meet it.
7. Reconsider the authentication/admission factorization if Stage 3 cannot
   assign a predicate without circular authority or unavoidable duplicate
   semantic interpretation and no claim-preserving logical split exists.
8. Reopen an Interface or Plan classification if a field cannot be assigned
   without changing fixed Protocol observations, or if equal declared inputs
   still permit different bridge results.
9. Reopen a Plan's OIR-versus-realization placement if one earliest reader
   cannot be assigned without duplicating authority or losing a required
   canonical behavior distinction.
10. Reopen an effect contract when no meaningful completion,
    publication/commit, partial-effect, retry, or residual-authority frontier
    can be stated.
11. Reopen any transition immediately when an undeclared read changes its
    normative result, an unknown kind is accepted semantically, or evidence or
    policy creates upstream authority.
12. Strengthen the common catalog layer if concrete domain projections cannot
    be linted for owners, closures, regimes, identity effects, outcomes,
    replay, composition, consumers, and non-claims without semantic drift.

A reversal must name the affected subjects, authorities, proposition,
identity and capability effects, wire promise, neighboring consumers, and
replacement invariant. It may not be implemented as an untyped extension to a
generic record.

## 15. Non-claims

- This convergence record is non-normative and does not begin Stage 3.
- It does not select final Rust, C++, MLIR, JSON, file, operation, attribute,
  class, hash, error, diagnostic, certificate, signature, or policy schemas.
- It does not prove Protocol admission, relation truth, witness satisfaction,
  soundness, completeness, knowledge, zero knowledge, `FSCompile`, compiler
  correctness, projection correctness, realization, endpoint conformance,
  Evidence sufficiency, or reliance adequacy for any concrete zkc artifact.
- It does not establish that a smaller independent validator exists for any
  particular compiler, projector, normalizer, or backend.
- It does not describe current deterministic replay as independent
  translation validation.
- It does not claim that opaque host-language types alone enforce capability
  safety across threads, plugins, FFI, languages, or processes.
- It does not introduce a stable transition, admission, correspondence,
  projection, derivation, compiler-decision, realization, Evidence, appraisal,
  or reliance wire object.
- It does not infer source coverage from standalone OIR, semantic truth from a
  digest or signature, correctness from producer success, or permission from
  appraisal.
- It does not classify current correspondence gaps as bugs or security
  findings and does not constrain the ideal design by migration cost.
- Static specifications, implementation paths, and tests were inspected as
  bounded correspondence evidence. This Stage 2 research pass did not execute
  tests or establish implementation conformance.
- No implementation, migration, release, compatibility, or public roadmap
  work is authorized by this document.

## 16. Stage 2 output and exit-gate audit

### 16.1 Required-output audit

| Charter output | Evidence | Result |
|---|---|---|
| Current typed catalog and owners | [Current transition catalog](current-transition-catalog.md) | Complete for the charter inventory, including current conflicts and non-claims |
| Selected target catalog (the charter's provisional target output) | [Target transition catalog](target-transition-catalog.md) with the Section 4 corrections incorporated | Complete at Stage 2 architectural resolution |
| Full transition contracts | [Lifecycle](lifecycle-spine.md), [semantic bridges](semantic-bridges.md), [endpoint/operational bridges](endpoint-operational-bridges.md), and target catalog | Complete for source/result category, authority, closure, relation, identity, outcomes, capability, replay, residual trust, and later owner; exact domain schemas are deliberately downstream |
| Bridge-owner matrix | Semantic, endpoint, and target dossiers | Complete; source, bridge/checker, target, and relying owner remain separate |
| Closure/read-set and regime matrices | Lifecycle, semantic, endpoint, synthesis, and target dossiers | Complete at transition-family resolution; exact field closures route to owning stages |
| Identity-effect matrix | Lifecycle, endpoint, synthesis, and target dossiers | Complete; no global transition identity selected |
| Qualified outcome/refusal taxonomy | Synthesis, endpoint, target, and Section 9 | Complete as a conceptual factorization; domains later choose valid variants |
| Interface boundary and field ledger | Target catalog, endpoint dossier, and Section 8 | Boundary complete; exact field schema is the bounded Stage 3 task |
| Plan obligation/realization ledger | Target catalog, endpoint dossier, and Section 8 | Boundary complete; exact obligations and per-field placement are Stage 3/4B tasks |
| Checker/witness alternatives | External cases, semantic/endpoint dossiers, synthesis, and Section 5 | Complete per major family, including direct, validated, trusted, effect, policy, and no-artifact choices |
| Scenarios, opportunities, counterexamples | [Scenario results](scenario-results.md) and Section 11 | Complete; all required falsification classes exercised conceptually |
| Current-to-target correspondence and gaps | Current catalog, domain dossier gap ledgers, and Section 10 | Complete at architecture resolution; not an implementation migration plan |
| Durable decisions, deferrals, owners, reversal triggers | Sections 3--5 and 12--14 | Complete |
| Explicit Stage 3 entry contract | Section 17 | Complete and bounded; later consumed by Stage 3.0 activation |

### 16.2 Charter exit-condition audit

| Exit condition | Result | Basis |
|---|---|---|
| Every current and selected target boundary has an unambiguous source and result category | Pass | Current and target inventories plus Section 7 |
| Every contract names authorities, closure, regimes, binding time, relation, identity, outcomes, capabilities, replay, owner, residual trust, and non-claims | Pass at Stage 2 resolution | Dossiers and common contract requirements; exact later schemas are explicitly assigned |
| No boundary is described only as valid, lowered, or checked | Pass | Named transition relations and Section 5 |
| Negative judgment, refusal, unsupportedness, inconclusive checking, and operational failure cannot be confused | Pass | Qualified outcome model and scenario `S4`, `S5`, `E3`, and `E5` |
| Interface labels and ambient environments are explicit | Pass | Admitted Interface, exact dependency closure, and forbidden ambient-read rules |
| Every Interface- or Plan-sensitive transition consumes its exact input | Pass | Section 8 and tagged projection basis |
| At least one meaningful checker alternative was compared per major family | Pass | External case matrix and per-domain checker tables |
| A clean-room Stage 3 reviewer need not infer semantics from current C++ names | Pass | Section 17 provides semantic inputs and bounded outputs independently of implementation types |
| No universal record, certificate, or ID was introduced from shared table fields | Pass | Candidate B decision and consumer-justified persistence rule |

Both the **research exit gate** and the **Stage 2 absorption gate** pass. The
selected material was promoted according to Section 12; durable navigation,
the manifest, domain status pages, and the design program were updated; the
bounded Stage 3 gate was incorporated into its durable Project owner; and the
temporary package was recorded as absorbed and retained as research evidence.

Stage 2 is **complete**. At this record's closure Stage 3 had not started; it
was later activated, consumed this handoff, and completed on 2026-08-22.

## 17. Bounded Stage 3 entry contract

Stage 3 may begin only after explicit activation. The completed absorption
steps in Section 16 establish its fixed inputs:

```text
selected Stage 1 Protocol architecture
+ this Stage 2 disciplined-hybrid transition architecture
+ corrected target transition inventory
+ exact closure, authority, identity, outcome, replay, composition,
   persistence, Interface, Plan, and no-backflow invariants
```

Stage 3's central question is:

> What exact closed Protocol, canonical PIR, Interface, Plan, relation-domain
> subjects, and composition laws satisfy the selected architecture without
> importing carrier metadata, compiler state, backend state, or policy into
> Protocol meaning?

Stage 3 must deliver:

1. the complete `InteractiveCore`, `ChallengeInterpretation`, Protocol, and
   canonical PIR semantic model, including one total observable schedule;
2. canonical occurrence, port, challenge, claim, check, terminal, dependency,
   and abstract prover-obligation references;
3. a unique physical canonical-form contract, semantic identity preimages,
   and the exact authentication/admission predicate split;
4. minimal immutable authentication and admission bases with no open-ended
   resolver authority;
5. exact Interface and Plan schemas, regimes, IDs, admission, exported views,
   structural `PlanRealizes`, and the field/earliest-reader ledger;
6. relation-interface ingress, optional artifact observation, and exact
   `RelationCorrespondsAtInterface` inputs and outcomes;
7. exact ownership and mathematical signatures for Core/Protocol equality,
   trace, distributional, intentional-change, FS, projection, Plan, and
   property-transport seams, without prematurely implementing later owners;
8. deterministic FS Protocol construction and the occurrence/transcript maps
   required by later theorem-backed analysis;
9. semantic Protocol composition with tagged repeated occurrences, face maps,
   causal seams, interleaving, challenge/domain-separation policy,
   failure/terminal propagation, and new closure and identity;
10. direct-check, validator-candidate, trusted-boundary, and no-durable-result
    classifications for Stage 3-owned transitions; and
11. narrow, typed handoff views and transition skeletons for Analysis,
    Compiler, OIR, Realization, and Evidence.

Stage 3 must not define complete Analysis, Compiler, OIR, Realization,
deployment, Evidence, appraisal, or reliance schemas; select a universal
transition artifact; or treat current C++ and MLIR organization as semantic
authority. It may use MLIR as the selected primary v0 canonical carrier while
keeping Protocol meaning language-independent.

## 18. Converged conclusion

Stage 2 selects uniform rigor without a universal semantic lowest common
denominator:

```text
shared contract discipline, not shared truth
domain relations, not generic validity
explicit closure, not retained ambient environments
local capabilities, not serialized authority
validators where materially useful, not everywhere
trusted procedures named honestly when validation is not economical
durable claims for real consumers, not speculative wire products
typed effects and occurrences, not pure-arrow fiction
evidence and policy downstream, never semantic backflow
composition by an owned law, never adjacency
```

This is the complete Stage 2 research decision. It has been absorbed into the
durable target architecture and closes Stage 2. It does not start Stage 3.
