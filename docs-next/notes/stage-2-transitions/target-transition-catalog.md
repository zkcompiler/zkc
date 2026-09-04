# Target transition catalog

> **Document kind:** Temporary Stage 2 convergence artifact
> **Document state:** Converged Stage 2 target inventory; temporary handoff
> **Authority:** None. This catalog records the target contracts selected by
> Stage 2 convergence. It does not define normative
> syntax, public APIs, wire formats, or implementation status.
> **Inputs:** The fixed Stage 1 Protocol architecture, the current transition
> reconstruction, lifecycle and bridge dossiers, external case research, and
> the Stage 2 scenario portfolio.
> **Disposition:** Reviewed rules have been promoted into their durable architecture
> and domain boundaries. Retain this detailed inventory for later package
> handoff, then delete it before `docs-next/` authority cutover.

## 1. Purpose and selection boundary

This page answers the Stage 2 catalog question:

> What exact transitions connect zkc's subjects, which authority does each
> transition consume or create, and what relation does a successful result
> actually establish?

The target is deliberately **not** one universal transition IR, artifact,
identifier, checker, or error type. The catalog uses one descriptive schema so
that unlike transitions can be reviewed at equal resolution. Concrete
semantics, result types, and checkers remain domain-owned.

The catalog selects a disciplined hybrid architecture:

1. domain- or bridge-owned typed contracts are the ownership baseline;
2. the Protocol lifecycle uses narrow process-local immutable capabilities;
3. complex or search-heavy producers are separated from relation-specific
   validators when the validator is materially smaller or more stable;
4. cheap deterministic predicates are recomputed directly;
5. effectful activities produce occurrence-scoped observations rather than
   pretending to be pure semantic arrows; and
6. a durable certificate is introduced only for a named independent consumer
   that cannot economically recheck the claim from exact inputs.

This selection fixes transition architecture and boundary rules. Stages 3,
4, and 6 still complete the exact domain schemas named below.

## 2. Common contract model

### 2.1 Four non-collapsible layers

Every transition contract keeps these roles separate:

```text
semantic subject or operational resource
  -> proposal, construction, interpretation, or activity
  -> checked result, judgment, or attributed observation
  -> capability or policy decision authorizing one use
```

- A **subject** has meaning and identity from its owning domain.
- A **procedure or activity** may propose a subject, search for one, execute an
  effect, or assemble a record. Running it does not make its claim true.
- A **checked result** establishes one named predicate over exact inputs.
- A **capability or reliance decision** authorizes only the operations or use
  its owner defines. It does not become subject identity or universal truth.

The source owner, bridge/checker owner, target owner, and relying consumer are
named independently. None may redefine another role through a convenient
encoding.

### 2.2 Functional-closure rule

For every pure deterministic transition `F`:

```text
equal source subjects and authority states
+ equal identified auxiliary inputs and complete declared read closure
+ equal semantic regimes and checker contract
---------------------------------------------------------------
= equal normative outcome and result
```

If a result changes after only an undeclared resolver entry, Interface, Plan,
configuration, theorem, target, supplier, policy, or carrier field changes,
the contract is incomplete. The missing material becomes an explicit input or
the read is removed.

A resolver may be broad at lookup time, but a successful immutable result
binds the exact resolved closure it actually depends on. Unrelated resolver
growth cannot change a recheck. Effectful transitions instead bind one exact
occurrence and report the environment, nondeterministic choices, and partial
effects necessary to interpret that occurrence; they do not promise equal
observations for equal semantic subjects.

### 2.3 Qualified outcomes

There is no project-wide `valid : bool`. Each contract preserves at least
these independent questions when applicable:

```text
Did the input form the required source type?
Was the construct, regime, target, or question supported?
Did the procedure complete, fail before effects, or fail after partial effects?
Did a checker establish, refute, conditionally establish, or fail to decide
  its exact proposition?
What subject, judgment, observation, capability, assessment, or decision
  resulted?
```

Consequently:

- a negative correspondence or decidable negative analysis can be a
  successful judgment;
- failure to find a derivation is not negative truth without a completeness
  theorem;
- an unsupported projection does not invalidate its Protocol;
- verifier rejection is a completed semantic endpoint result;
- supplier refusal and executor failure are not verifier rejection;
- a negative appraisal and a reliance denial are successful policy results;
  and
- malformed input, missing authority, unsupportedness, inconclusive checking,
  refusal, operational failure, and partial-effect failure remain distinct.

One shared diagnostic envelope is permitted only when it preserves every
domain-owned variant and does not grant a stronger common meaning.

### 2.4 Identity-effect classes

Every row declares one of these effects:

| Class | Meaning |
|---|---|
| Preserve | The same semantic subject is represented or re-authorized; no new semantic identity is inferred |
| Construct | A new subject is formed and receives its owning-domain identity |
| Relate | Existing subjects are unchanged; a checked relation or judgment cites them |
| Configure | A dependent immutable configuration subject is formed without changing its source subject |
| Instantiate | A live or occurrence-scoped identity is created from immutable configuration and current resources |
| Observe | An occurrence produces attributed material without changing the observed subject |
| Decide | A policy-qualified assessment or use decision is created without changing its inputs |

There is no global `TransitionId`. A domain result or certificate receives an
identity only when its owner and a real consumer require persistence. The ID
authenticates that result object; it does not prove the embedded claim, replace
source or target IDs, or preserve a capability.

### 2.5 Capability and serialization rule

Capabilities are opaque, narrow, process-local authority over immutable
subjects or live resources. A capability may be copied only according to its
own lifetime and alias rules. Immutable admission and projection capabilities
may support read-only sharing; deployment and invocation capabilities may be
linear, revocable, expiring, or single-use.

Serialization always yields subject/configuration bytes and ordinary
references, never continued local authority. A receiving process decodes,
authenticates, resolves the exact dependency closure, and re-admits. A durable
certificate can let the receiver verify one named claim, but it still cannot
serialize the sender's capability.

## 3. Mechanism-selection rule

For each transition, the owner chooses a checking and persistence mechanism in
this order:

1. State the exact proposition or operational postcondition the consumer
   needs.
2. Identify all subjects, regimes, dependencies, configurations, policies,
   protected observers, and effects that determine it.
3. Recompute a small deterministic predicate directly when all inputs are
   locally available.
4. For search, optimization, synthesis, or complex production, separate the
   proposer from an exact per-result validator when that validator is
   materially smaller, more stable, or independently implementable.
5. If no practical validator exists, name the trusted producer and the exact
   limitation rather than implying independent checking.
6. Keep a successful result as an in-process paired capability or ordinary
   domain result while its consumers share the process and rechecking is
   cheap.
7. Create a durable witness or certificate only when a named consumer needs
   cross-process verification, independent release, caching, retention, or
   trust separation and the certificate closes over every semantic input.

No transition receives a durable record merely to make the pipeline look
uniform. No candidate receives independent-checking credit when validation
reruns the same producer implementation under another name.

## 4. Protocol lifecycle catalog

Names in these tables are descriptive contracts, not selected public symbols.

| Transition | Exact source and inputs | Success and claimed relation | Identity/capability effect | Principal non-claims and outcomes | Preferred mechanism |
|---|---|---|---|---|---|
| Author | Explicit source fragments, authoring profile, options | Mutable `AuthoringUnit` proposal | No semantic ID or authority | Parse/generation success is not Protocol formation or correspondence | Direct construction |
| Import | Immutable external-source snapshot, importer semantics, import options and dependencies | `AuthoringUnit`, provenance, and optionally a separately checkable correspondence proposal | No Protocol authority; external identity cited as provenance | Import does not prove source/target equality; underspecification remains explicit | Producer plus source-specific checker when correspondence matters |
| Resolve | `AuthoringUnit`, immutable resolver snapshot, resolution profile | `ResolvedAuthoringUnit` plus complete typed `ResolutionClosure` | No Protocol ID; closes actual reads | Missing/ambiguous/cyclic reference differs from unsupported schema or unavailable resolver | Direct deterministic resolution |
| Normalize | Resolved unit, Protocol regime, normalization profile, explicit choices | One physical `CanonicalProtocolCandidate`, dependency manifest, extracted Interface/Plan candidates, source map, optional witness | Carries unauthoritative expected Core/construction/Protocol IDs; no authority | Candidate existence or producer-asserted identity is not authentication, admission, or source correspondence | Producer; target authentication/admission always independent |
| Authenticate Protocol | Canonical candidate or decoded canonical carrier, exact Protocol regime, dependency preimages, optional expected IDs | `AuthenticatedCanonicalProtocol`; canonical form, dependency closure, and all semantic IDs recompute | Constructs independently recomputed IDs; confirms optional expected-ID equality; mints local authentication capability | Does not establish whole-Protocol admissibility or any property | Small bounded direct checker |
| Admit Protocol | Authenticated Protocol and exact normative regime checker | `AdmittedProtocol` satisfying the whole-Protocol predicate | Preserves IDs; mints opaque immutable local admission capability | Does not establish soundness, completeness, projection, or suitability policy | Direct deterministic recomputation |
| Persist Protocol | Admitted Protocol and exact transport schema | Canonical Protocol artifact representing the same semantic subject | Preserves semantic IDs; optional byte digest; destroys capability continuity | Byte equality/digest is not semantic admission | Admission-gated producer; unauthoritative workbench caches use a different envelope |
| Decode Protocol carrier | Bytes, exact transport schema, resource bounds, optional transport selector | Immutable decoded carrier | No semantic authority; transport identity only | Parse/schema success is not semantic authentication or admission | Direct parser and carrier checker |
| Derive consumer view | Admitted Protocol, exact question, explicit Interface/Plan when relevant, view schema and consumer authority | Question-scoped immutable `ConsumerView<Q>` | Narrows local authority; normally no independent ID | Cannot read carrier labels or ambient resolver state; view is not a fact root | Direct source-owned projection; durable only for a named consumer |
| Reopen | Admitted Protocol | Independent mutable `AuthoringUnit` with origin lineage | Editable branch has no active ID/capability; source remains admitted | A no-op branch still re-authenticates and re-admits | Direct clone/raise with authority discard |
| Link authoring units | Raw or resolved authoring units and explicit link plan | New unauthoritative authoring proposal | No inherited identity or authority | Workbench linking is not semantic composition | Direct checked authoring operation |
| Compose Protocols | Admitted child occurrences, explicit composition plan and Protocol regime | New canonical composite candidate with occurrence namespaces, seams, schedule, challenges, failures, and obligations | Carries unauthoritative expected new Core and Protocol IDs; no inherited output capability | Graph union, child-ID reuse, and transition-chain adjacency are insufficient | Producer plus whole-composite authentication/admission; Stage 3 defines composition checker |

Authentication and admission are logically distinct even when one
implementation shares traversal. `AdmittedProtocol` retains the minimal exact
regime and admission/dependency basis, not an open-ended resolver that later
consumers may query opportunistically.

## 5. Dependent Protocol subjects

### 5.1 Protocol Interface

| Transition | Exact source and inputs | Success and claimed relation | Identity/capability effect | Preferred mechanism |
|---|---|---|---|---|
| Form Interface candidate | Extracted or authored Interface content, exact Protocol reference and Interface regime | Closed Interface candidate over canonical Protocol ports/events | Carries an unauthoritative expected dependent `ProtocolInterfaceId` | Direct construction |
| Authenticate Interface | Candidate, exact admitted or authenticated Protocol reference, Interface regime and dependencies | Identity and dependency closure recompute | Constructs the independently recomputed Interface ID; confirms optional expected-ID equality; mints local authentication capability | Direct checker |
| Admit Interface | Authenticated Interface plus admitted Protocol | `AdmittedProtocolInterface[I -> P]`; every external decode/mapping preserves the already-fixed Protocol meaning | Preserves IDs; mints narrow local capability | Direct relation-specific checker |

The Interface may own external names and positions, packaging, value codecs
that decode before Protocol meaning, role entry points, malformed external
input behavior, and relation/application port binding. It may not change
semantic public values, proof-event order, transcript inputs or framing,
challenges, checks, claims, terminal outcomes, accepted language, or any
encoding already observed by the Protocol.

Every Interface-sensitive consumer receives an exact admitted Interface. No
consumer may recover it from author labels or carrier metadata. Protocol-only
Analysis is reusable across Interfaces; relation correspondence, projection,
external acceptance, realization ABI, and invocation bind the exact
`ProtocolInterfaceId`.

### 5.2 Prover Plan

| Transition | Exact source and inputs | Success and claimed relation | Identity/capability effect | Preferred mechanism |
|---|---|---|---|---|
| Form Plan candidate | Authored/extracted plan, exact Protocol reference, Plan regime | Closed plan candidate over canonical abstract prover obligations | Carries an unauthoritative expected dependent `ProverPlanId` | Direct construction or planner proposal |
| Authenticate Plan | Candidate, exact Protocol reference, Plan regime and plan dependencies | Plan identity and dependency closure recompute | Constructs the independently recomputed Plan ID; confirms optional expected-ID equality; mints local authentication capability | Direct checker |
| Admit Plan | Authenticated Plan plus admitted Protocol and exact Plan regime | `AdmittedProverPlan[L -> P]`; every Plan reference and owned constraint is well formed against the exact Protocol | Preserves IDs; mints narrow local Plan capability | Direct Plan-owned checker |
| Check `PlanRealizes` | Admitted Plan, admitted Protocol, exact obligation map and coverage regime | Structural `PlanRealizes(L, P)` accounting for every abstract prover obligation by a Plan step or explicit typed requirement | Relates exact Plan and Protocol IDs; mints a paired local coverage capability | Direct coverage and boundary checker |

Plan admission establishes Plan-owned structural well-formedness and dependency
closure. The separate `PlanRealizes` check establishes total structural
accounting of the exact Protocol's abstract prover obligations. Neither
establishes honest-prover completeness, supplier correctness, performance, or
verifier acceptance. Those are separately qualified judgments.

A plan is consumed at the earliest boundary that reads each field:

```text
plan changes canonical prover OIR
  -> projection uses InterfaceAndPlan and OirId depends on ProverPlanId

plan leaves canonical OIR unchanged and chooses only below-OIR algorithms,
scheduling, buffering, or suppliers
  -> realization receives the exact admitted Plan explicitly
```

Verifier projection never consumes a Plan. A generic prover-obligation
skeleton may use an explicit `InterfaceOnly` basis; a plan-specialized prover
program uses `InterfaceAndPlan`. The same plan fact cannot arrive implicitly
at both projection and realization.

## 6. Semantic bridge and checked-change catalog

| Transition | Exact source and inputs | Success and claimed relation | Identity/capability effect | Principal non-claims and outcomes | Preferred mechanism |
|---|---|---|---|---|---|
| Admit relation interface | Relation-interface candidate, relation regime, exact declaration dependencies | Admitted relation-domain interface subject | Constructs relation-interface ID and local capability | Does not consume a Protocol or prove relation truth/satisfaction | Direct relation-owned checker |
| Interpret relation artifact | Admitted relation interface, immutable artifact bytes, exact format adapter | `RelationArtifactObservation` with computed/cross-checked facts and typed format, mismatch, support, availability, and I/O outcomes | Interface ID preserved; byte identity cited | Reader authority does not become correspondence, relation truth, or a relation judgment | Exact adapter; durable observation only if consumed later |
| Check relation correspondence | Admitted Protocol, admitted Interface, admitted relation interface, optional artifact observation, bridge regime | Affirmative or negative `RelationCorrespondsAtInterface` with agreements, disagreements, and residual obligations | Relates exact IDs; no source changes | No witness satisfaction, relation truth, security property, or projection result | Relations-owned checker over narrow source views |
| Analyze property | Exact admitted property-subject tuple, question, analysis basis/regime, derivation plan, hypotheses and source-owned views | Conditional, quantitative, affirmative, or explicitly supported negative `PropertyJudgment` plus checked derivation | Subjects unchanged; conclusion and derivation IDs distinct if durable | Search failure is not negative truth; cited theorem truth is an explicit premise | Analysis-owned plan checker; durable derivation only after the Section 3 named-consumer persistence gate passes |
| Propose Protocol successor | Admitted predecessor, application, exact transform definition and producer configuration | Unauthoritative canonical successor proposal and optional witness/trace | Carries an unauthoritative expected target ID only | Proposal, lineage, or score is not legality/preservation | Untrusted or deterministic producer |
| Check Protocol step | Admitted predecessor, independently authenticated/admitted successor, named relation, observer set, maps, assumptions, regimes, exact checker | Positive or negative per-result relation such as `ProtocolEq`, `TraceEq`, `TraceRefines`, distributional relation, or `IntentionalChange` | Relates exact IDs; source/target authority unchanged | Structural lineage does not transport properties | Relation-specific validator; recompute small families |
| Compile and select | Source, exact request, complete declared candidate domain, checked steps, property results, constraints/objectives/ties and compiler configuration | Selected already-admitted successor plus checked path/comparison, or successful `NoSelection` over a complete domain | Selection creates no Protocol ID; decision ID only if a consumer requires persistence | Winner validity alone does not prove optimum; no-selection is not malformed input | Recompute bounded v0 domain; later domain witness only if needed |
| Construct FS Protocol | Core or fresh-coin Protocol, exact transcript construction, Protocol regime | Admitted FS Protocol over the same Core and distinct Protocol ID | Constructs new Protocol ID; shares Core ID | Target formation is not `FSCompile` or any security property | Deterministic Protocol constructor plus ordinary authentication/admission |
| Check `FSCompile` | Exact fresh and FS Protocols, construction, occurrence/prefix map, theorem/model basis, regimes and assumptions | Theorem-backed `FSCompile` judgment for exactly the stated construction relation | Relates two Protocol IDs; no subject changes | Does not automatically transport every property | Dedicated bridge checker co-designed by PIR semantics and Analysis |
| Transport property | Source property judgment, checked source/target relation, exact occurrence map, transport rule, assumptions and quantitative substitutions | Target property judgment plus checked derivation | Subjects unchanged; new conclusion/derivation if identified | Relation adjacency or preservation annotation is insufficient | Analysis-owned proof checker |

The order for a nonidentity checked step is:

```text
propose target -> authenticate target -> admit target
               -> check exact source/target relation
               -> use checked step in compiler selection or property transport
```

An admitted target may exist even when its proposed relation to one source is
refuted. Target admission and source/target correspondence are independent.

## 7. Endpoint and operational catalog

| Transition | Exact source and inputs | Success and claimed relation | Identity/capability effect | Principal non-claims and outcomes | Preferred mechanism |
|---|---|---|---|---|---|
| Project endpoint | Admitted Protocol, admitted Interface, role, tagged `InterfaceOnly` or `InterfaceAndPlan(admitted Plan, checked PlanRealizes capability)` basis, OIR regime and cited dependencies | Canonical OIR satisfying `LocalOirValid(O)` plus paired `ProjectionCorrect(P,I,role,basis,O)` capability with exact source coverage | Constructs `OirId`; source IDs cited | The two predicates remain logically distinct; Plan admission alone is insufficient for a Plan-sensitive basis; unsupported/coverage refusal does not invalidate source; no supplier or property claim | Direct source-relative checker; allow alternative proposer plus same validator later |
| Admit standalone OIR | OIR carrier, OIR regime, expected ID and local dependency closure | `AdmittedOir` satisfying `LocalOirValid` | Preserves OIR ID; local capability | Cannot establish origin or source-obligation coverage | Direct local checker |
| Form supplier binding | Admitted OIR, explicit below-OIR Plan and checked `PlanRealizes` capability when read, target contract, exact binding proposal, binding regime and referenced provider designations | Identified immutable exact closed `SupplierBinding` | Configures new binding ID; OIR unchanged; no live provider authority | Requirement closure and matching designations do not prove provider correctness, availability, or authority | Direct exact-closure checker |
| Resolve supplier authority | Admitted OIR, exact `SupplierBinding`, immutable provider-resolver snapshot, provider-admission policy and regime | Narrow process-local provider authority for the exact OIR/Plan/target/binding tuple | Preserves subject IDs; mints local revocable or lifetime-bounded capability | Parsed binding bytes do not grant access; unavailability, revocation, incompatibility, and refusal remain distinct | Direct resolution and authority admission; repeat after serialization or authority expiry |
| Produce realization | Admitted OIR, exact supplier binding, live admitted provider authority, request and toolchain closure | Realization candidate and emission observation | Constructs artifact/package content identity and production occurrence | Production success, build success, or embedded manifest does not prove realization | Producer; effects and partial publication explicit |
| Check realization | OIR, binding, realization candidate, exact target checker/regime | `AdmittedRealization` with named `RealizesOir` relation | Artifact ID preserved; paired relation capability or domain result | Evidence on selected vectors is not universal preservation | Target-specific validator, verified producer, or explicit trusted boundary |
| Prepare deployment | Admitted realization, immutable deployment specification, resource snapshot, policy and regime | Admitted deployment binding resolving only authorized roles | Configures `DeploymentBindingId` | Does not activate resources or change endpoint semantics | Direct configuration/policy checker |
| Activate deployment | Deployment binding, operator authority and activation request | Live scoped deployment capability plus activation observation | Instantiates deployment occurrence/instance identity | Serialized binding is not live authority; partial activation is reported | Effectful operation with explicit rollback/revocation contract |
| Bind invocation | Live deployment capability, admitted Interface, request, input capabilities, policy and invocation regime | Narrow bound invocation capability | Configures/instantiates invocation occurrence inputs | Interface malformed, authority refusal, and resource unavailability are not endpoint rejection | Direct join and authority-attenuation checker |
| Invoke endpoint | Bound invocation and executor capability | Role-specific completed result plus raw operational observation, or operational/partial-effect failure | Creates run occurrence; semantic subject IDs unchanged | Verifier reject is completed; prover output is not acceptance or completeness | Effectful execution |

Projection keeps two propositions distinct:

```text
LocalOirValid(O)
ProjectionCorrect(P, I, role, basis, O)
```

A source-free consumer may safely admit and use OIR under a policy that needs
only local validity. It reports source coverage as unknown unless it rechecks
with admitted source subjects or verifies a sufficient source-bound
certificate. `OirId`, embedded source coordinates, or a source digest cannot
prove absence of omitted obligations.

Supplier binding, realization production, realization checking, deployment
configuration, activation, invocation binding, and execution remain separate
even if one product command initially combines them. Each combined command
must report which semantic gates completed and which external effects remain.

## 8. Observation, evidence, appraisal, and reliance catalog

| Transition | Exact source and inputs | Success and claimed relation | Identity/capability effect | Principal non-claims and outcomes | Preferred mechanism |
|---|---|---|---|---|---|
| Record evidence | Producer-owned observation/receipt/comparison, exact claim and subjects, issuer/recorder, procedure, environment/pins, evidence regime and disclosure scope | Attributable bounded `EvidenceRecord` | Observes; creates record ID if durable | Authentic record does not prove claim, procedure adequacy, freshness, or trust | Evidence-owned formation/authentication |
| Appraise evidence | Exact evidence set, claim, evidence policy, reference values, trust anchors, context/time | Positive, negative, insufficient, stale, or indeterminate `ClaimAssessment` | Decides under evidence policy; optional assessment ID | Negative/insufficient is not checker refusal; assessment is not use authorization | Evidence-owned policy evaluator |
| Decide reliance | Assessments, consumer, intended use, consumer policy, current state and trust context | Permit, deny, condition, limit, or defer one use | Consumer-owned scoped decision/capability if any | Different consumers may decide differently; reliance does not change evidence or semantics | Consumer policy |

Raw observations remain owned by the producing domain. Evidence governs how
material is attributed and scoped. Appraisal governs what follows under one
evidence policy. The relying consumer alone governs whether that assessment is
adequate for one action. No arrow points backward from these layers into
Protocol, Interface, Plan, OIR, realization, or execution meaning.

## 9. Read-closure and semantic-regime matrix

The table names the minimum closure category; exact fields belong to later
owners.

| Transition family | Semantic subject closure | Additional explicit closure | Regime requirement | Forbidden ambient reads |
|---|---|---|---|---|
| Resolve/normalize | Workbench snapshot and resources actually consulted | Resolver snapshot, normalization profile and choice vector | Authoring/import and Protocol regimes as applicable | Lookup order, registry enumeration, defaults, randomness, or optimizer state not named as inputs |
| Protocol authentication/admission | Canonical Protocol plus exact semantic dependency preimages | Expected IDs and normative checker | Exact Protocol regime; change cannot preserve ID silently | Interface, Plan, compiler, target, supplier, theorem, evidence, policy |
| Interface/Plan admission | Exact dependent subject plus its Protocol | Subject-specific dependencies and obligation/port map | Exact Interface or Plan regime plus referenced Protocol regime | Carrier labels, compiler state, provider state |
| Relation correspondence | Protocol, Interface, relation interface, optional artifact observation | Bridge checker/model | Exact bridge and subject regimes | Soundness catalog, OIR, backend, relying policy |
| Analysis | Exact question-selected subject tuple | Analysis basis, plan, hypotheses, theorem/model authority | Exact Analysis and subject regimes | Mutable fact mirrors, compiler cache, hidden Interface/Plan |
| Checked transform/compiler | Predecessor, admitted targets, exact relations | Producer config, transform definitions, complete domain, request, constraints/objectives | Exact source/target, relation, Analysis, and compiler regimes | Backend feasibility or unlisted provider/environment state |
| Projection | Protocol, Interface, role, tagged optional Plan, OIR target | Projection checker and cited dependency closure | Exact subject and OIR regimes | Carrier labels, compiler plan, supplier implementations |
| Supplier binding/realization | OIR, binding/Plan/target and exact providers | Resolver snapshot, toolchain, checker | Exact OIR, binding, target, and realization regimes | Unselected catalog entries, mutable latest-provider lookup |
| Deployment/invocation | Realization/deployment plus exact resource occurrence | Policies, current resource snapshot, live capabilities, inputs | Exact operational regimes and epochs | Unversioned mutable resources or unscoped authority |
| Evidence/appraisal/reliance | Exact observations/records/assessments and claim | Issuer, procedure, policies, trust anchors, context/time | Exact evidence/policy regimes | Implicit trust, current-time or revocation state omitted from replay-sensitive claims |

Semantic regime, identity encoding, canonical carrier schema, transport schema,
dependency schema, local policy, checker implementation, and producer release
are distinct axes. A transition records only the axes its meaning or replay
requires. Decoder success under one transport revision never proves semantic
comparability across regimes.

## 10. Checker, replay, and persistence matrix

| Family | Default v0 check | Replay class | Durable result posture |
|---|---|---|---|
| Canonical authentication/admission | Direct bounded recomputation | Re-authenticate and re-admit | Protocol artifact only; no admission receipt |
| Interface/Plan/relation-interface admission | Direct owner recomputation | Re-admit exact dependent subjects | Subject artifacts only if named exchange needs them |
| Property analysis and transport | Explicit-plan proof checking | Independent derivation verification | Portable derivation remains a candidate only after a named consumer, stable checker, closure, retention need, and compatibility policy exist |
| Protocol transform | Per-result validation; deterministic reconstruction for small families | Independent validation or recomputation | Checked-step certificate only for named consumer |
| Compiler selection | Recompute complete bounded domain | Decision recomputation | No decision wire schema until external consumer exists |
| `FSCompile` | Dedicated theorem/model checker | Re-run checker or proof verification | Defer certificate until a real consumer exists |
| Projection | Direct source-relative check and paired capability | Reproject/recheck with source | No portable projection record by default |
| Standalone OIR | Direct local admission | Re-admit locally | OIR artifact carries no source coverage |
| Supplier binding | Direct exact closure and ABI checking | Re-resolve and re-admit | Portable configuration may persist; live authority does not |
| Realization | Target-specific validator, verified producer, or explicit trusted producer | Recheck/certificate/evidence according to target | Per-target only after checker and consumer are concrete |
| Deployment/invocation | Operational binding and execution | New occurrence, not authority replay | Configuration/observations may persist; live capabilities do not |
| Evidence/appraisal | Record validation and policy evaluation | Claim-specific verification; freshness where required | Domain-owned records and assessments only |

“Replay” is always qualified as deterministic recomputation, independent
validation, certificate verification, re-authentication, observational
reproduction, or non-replayable attribution. Equal content inputs do not merge
two operational occurrences.

## 11. Composition rules

The target supports five different notions of composition:

1. **Procedural sequencing:** one result capability satisfies the next step's
   input precondition. This establishes no end-to-end mathematical relation by
   itself.
2. **Relation composition:** exact relation owners provide a rule that carries
   source/target maps, assumptions, protected observers, quantitative losses,
   intentional changes, and regimes. Matching intermediate IDs is necessary
   but insufficient.
3. **Property transport:** Analysis checks a property-specific rule over a
   source judgment and checked relation. A transform annotation cannot replace
   it.
4. **Protocol composition:** Stage 3 constructs and admits a new Core with
   explicit occurrence namespaces, causal seams, schedule, challenges,
   failures, terminals, and obligations. It is not transition chaining.
5. **Operational sequencing:** Realization and runtime own effect order,
   rollback, retry, concurrency, and partial-failure rules. Pure-arrow laws do
   not apply by default.

A certificate chain proves only the conjunction or composed claim that an
explicit composition checker establishes. Provenance adjacency is not
transitivity.

## 12. Stage 3 seam ledgers

### 12.1 Interface field-ownership rule

| Field class | Owner and Stage 3 obligation | Consumers |
|---|---|---|
| Canonical semantic ports, proof events, values and order | Protocol/Core; define stable canonical occurrence references | Interface, Relations, OIR, Analysis |
| External names, positions, containers and entry points | Protocol Interface, if decoding precedes and preserves Protocol meaning | Relations, OIR, invocation |
| External value/proof encoding | Interface only when it bijectively or explicitly losslessly decodes to fixed semantic values/events | OIR and invocation |
| Relation/application binding | Interface plus relation-owned correspondence rule | Relations and endpoint projection |
| Malformed external input and interface refusal | Interface | OIR abstract execution and invocation |
| Transcript-visible framing, proof-event order, checks, accepted language | Protocol, never Interface | Every downstream consumer |

Stage 3 must define the exact Interface schema, identity encoding, admission
predicate, and narrow views used by Relations and OIR. It must reject any field
whose classification would let an Interface change fixed Protocol meaning.

### 12.2 Plan obligation/realization rule

| Field or obligation | Owner and Stage 3 obligation | Later consumer |
|---|---|---|
| Verifier-visible message, distribution, transcript action, proof ABI, check and terminal | Protocol/Core | OIR verifier/prover projections and Analysis |
| Abstract prover obligation and occurrence identity | Protocol/Core | Plan admission and completeness Analysis |
| Construction/witness DAG and explicit private dependency | Prover Plan | Planned prover projection or realization |
| Plan algorithm, scheduling, buffering and parallelism | Plan; mark whether canonical OIR reads it | OIR or Realization, never ambiently both |
| Typed unresolved provider requirement | Plan or Protocol obligation, with one exact owner | Supplier binding |
| Structural coverage | `PlanRealizes` checker over exact Protocol and Plan | Planned projection and completeness Analysis |
| Honest-prover completeness | Analysis judgment over Protocol, Plan, relation/witness and supplier assumptions | Compiler/relying consumers |

Stage 3 must define canonical obligation references, the Plan identity
preimage, total structural coverage, and which plan facts are visible to the
Stage 4B projection/realization split. A Plan that changes verifier-visible
behavior is rejected as a Plan and must instead construct a different
Protocol.

## 13. Catalog coverage and deliberate deferrals

This catalog covers every current admitted boundary and every selected target
boundary named by the Stage 2 charter:

```text
author/import -> resolve -> normalize -> authenticate -> admit
persist -> decode -> re-authenticate -> re-admit
derive view -> reopen -> authoring link / semantic composition
Interface and Plan admission
relation ingress / artifact interpretation / correspondence
property analysis / checked Protocol step / compiler selection
FS construction / FSCompile / PropertyTransport
endpoint projection / standalone OIR admission
supplier binding / realization production and checking
deployment preparation and activation
invocation binding and execution
observation -> evidence -> appraisal -> reliance
```

It deliberately does not select:

- exact grammar, operation, attribute, class, hash, byte, file, or diagnostic
  spellings;
- complete Interface, Plan, relation, Analysis, Compiler, OIR, Realization, or
  Evidence schemas;
- a theorem prover, solver, certificate proof system, or one backend checker;
- portable transition, projection, compiler-decision, or admission records;
- historical compatibility or cross-regime migration rules; or
- implementation sequencing from the current checkout.

Those deferrals do not permit later owners to introduce ambient inputs,
collapse result categories, serialize local authority, infer source coverage
from source-free targets, or replace named relations with generic validity.

## 14. Reversal conditions

Reopen this target when concrete evidence shows that:

- two or more relation families possess genuinely identical semantics,
  authority, lifetime, composition, and consumer needs that justify a shared
  executable algebra;
- a uniform portable transition DAG has a named independent consumer whose
  needs cannot be served by domain adapters;
- a supposedly small validator must duplicate its entire producer or access
  hidden/private state, invalidating the producer/checker split;
- bounded re-admission or rechecking is too expensive or unavailable for a
  named consumer and a claim-scoped certificate has a smaller stable checker;
- a plan field cannot be placed at exactly one explicit OIR or realization
  boundary without changing Protocol behavior;
- an operational transition lacks a meaningful completion or partial-effect
  frontier; or
- a hidden read or new consumer invalidates functional closure of any row.

Reopening must identify the affected subjects, authorities, relation,
identity, capability, wire promise, and neighboring consumers. It may not
quietly add a field to a generic record and call the contradiction resolved.

## 15. Converged conclusion

The catalog's commonality is deliberately architectural: exact inputs,
authority roles, closure, identity effects, outcome dimensions, replay class,
and consumer need are reviewed everywhere. The semantic result remains local:
admission, derivability, preservation, correspondence, projection coverage,
realization, observation, appraisal, and reliance are different propositions.

This provides uniform rigor without a universal semantic lowest common
denominator. It lets zkc use MLIR for construction and transformation, opaque
capabilities for safe in-process consumption, small validators where they are
valuable, portable proof objects where a real consumer exists, and ordinary
direct recomputation everywhere else.
