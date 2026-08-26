# Transition and bridge architecture

> **Document kind:** Architecture decision
> **Document state:** Active
> **Target decision status:** Selected Stage 2 package result; integrated
> semantic-kernel closure remains under revalidation
> **Provisional owner:** `project`
> **Authority:** Non-normative target architecture for `docs-next/`. The
> current specifications under [`docs/`](../../docs/README.md) remain
> authoritative until normative consolidation and explicit cutover. This page
> selects the v0 transition architecture; it does not select public APIs, wire
> formats, exact domain schemas, or implementation.
> The [v0 Semantic Design Program](v0-design-program.md#14-progress-and-change-control)
> owns the live integrated-closure gate.

> **K2/K3-B reconciliation notice — 2026-08-27:** The shared transition,
> authority, recomputation, and outcome separations below remain design inputs.
> Protocol, Interface, Plan, and projection examples that use pre-K2 ports,
> abstract prover obligations, or authored event coordinates are historical
> where they conflict with the active
> [Interactive Core](../pir/interactive-core.md) and
> [Fiat--Shamir construction](../pir/fiat-shamir.md). K3-B reconciled the
> dependent [Interface and Plan](../pir/interfaces-and-plans.md),
> [Relations](../relations/relation-model.md), and
> [canonical carrier](../pir/canonical-pir.md) targets. It rejected the rule
> that plan-specialized OIR commits to the whole `ProverPlanId`; K3-D still owns
> any OIR-specific view, its exact read partition, and its identity effect.
> Those exact owners supersede conflicting Interface-sensitive relation and
> whole-Plan examples below.

## 1. Decision

The v0 target uses **domain-owned typed transition contracts under shared
project invariants**, not one universal transition algebra or artifact.

The architecture combines four mechanisms deliberately:

```text
shared descriptive contract schema and enforceable invariants
        |
        +--> narrow process-local capabilities for admitted authority
        |
        +--> direct recomputation for small closed predicates
        |
        +--> proposal + relation-specific validation when checking is
        |    materially smaller or more stable than production
        |
        +--> an explicit trusted boundary when no practical validator exists
        |
        `--> a purpose-specific durable result only for a named consumer

effectful operation -> attributed observation -> evidence record
                    -> policy-qualified appraisal -> use-specific reliance
```

The common layer makes every edge answer the same architectural questions. It
does not make their propositions interchangeable. Protocol admission,
relation correspondence, property derivation, checked change, projection,
realization, invocation, appraisal, and reliance remain different results
owned by different domains.

This decision preserves the useful uniformity of a typed catalog while
avoiding a premature universal `Transition` runtime type, `TransitionId`, wire
envelope, checker registry, fact root, or composition law.

## 2. Why this is the right center

The researched transition families share metadata but not semantics:

- authentication asks whether a carrier denotes its claimed canonical
  subject;
- admission asks whether that complete subject satisfies its normative
  regime;
- a checked Protocol step relates two already admitted subjects;
- Analysis derives one qualified conclusion about an exact subject tuple;
- projection establishes source-relative endpoint coverage;
- standalone OIR admission establishes only target-local validity;
- execution creates an occurrence and may leave partial external effects;
- appraisal evaluates evidence under one policy; and
- reliance authorizes one consumer's use.

Forcing them into one semantic algebra would either erase these distinctions or
reintroduce them as domain-specific payloads and exceptional rules. A
universal portable artifact would additionally freeze unresolved relation,
effect, policy, retention, and compatibility choices before a v0 consumer
requires it.

The selected architecture instead centralizes only what is genuinely common:
complete input closure, typed subject references, owner separation, exact
postconditions, identity and authority effects, qualified outcomes, replay
class, composition discipline, no-backflow, and persistence justification.

## 3. One conceptual model, several concrete contracts

Every transition family preserves four non-collapsible layers:

```text
Subject
  immutable meaning and domain identity

Attempt or activity
  construction, search, interpretation, checking, execution, or policy work

Checked result or observation
  exact proposition, judgment, admitted target, or occurrence outcome

Authority or reliance
  local permission to consume a result, or policy-qualified permission to act
```

Running a procedure does not make its claim true. A checked result does not
automatically authorize every use. An identity authenticates a subject or
record; it does not prove a relation. Evidence can inform appraisal but cannot
flow backward and change Protocol or OIR meaning.

The source owner, producer, bridge or checker owner, target owner, and relying
consumer are named independently. One implementation may perform several
logical steps in one traversal, but it must expose their distinct
postconditions and failure surfaces.

## 4. Shared invariants

Every durable transition contract must satisfy these project-wide rules.

1. **Typed subjects.** Every semantic source, target, and auxiliary subject is
   named by family, identity, and semantic regime.
2. **Complete closure.** Every value that can change a normative result is an
   explicit immutable input or is carried by an exact typed capability.
3. **Named postcondition.** “Valid,” “verified,” “checked,” and “lowered” are
   insufficient without an owned predicate, relation, judgment, observation,
   or policy decision.
4. **Separate authorities.** Source meaning, production, checking, target
   admission, and reliance cannot authorize one another by convenience.
5. **Explicit identity effect.** Each contract says which identities it
   preserves, constructs, relates, configures, instantiates, observes, or
   decides over.
6. **Explicit capability effect.** Each contract says which local authority it
   mints, narrows, shares, consumes, discards, or reconstructs.
7. **Qualified outcomes.** Negative judgments, unsupported questions,
   inconclusive checks, refusals, endpoint rejection, operational failure, and
   partial effects remain distinguishable.
8. **Protected observations.** Preservation, refinement, compilation, or
   intentional change names its direction, domain, assumptions, observer set,
   and quantitative loss where applicable.
9. **Scoped replay.** Recompute, validate, verify a certificate, re-admit,
   reproduce observations, and authenticate attribution are different claims.
10. **Lawful composition.** Procedural adjacency is not mathematical
    transitivity, Protocol composition, operational sequencing, or reliance.
11. **Authority ends at representation boundaries.** Bytes, mutable clones,
    ordinary FFI values, and provenance do not preserve a local capability.
12. **No authority backflow.** Target validity, observations, evidence,
    appraisal, and reliance cannot redefine or admit an upstream subject.
13. **Fail-closed meaning.** Unknown meaning-bearing subjects, regimes,
    relations, witnesses, or effect kinds are unsupported.
14. **Consumer-justified persistence.** Every durable checked result names its
    independent consumer, retention need, checker, compatibility commitment,
    and cheaper alternative.

The project may later make this descriptive schema machine-readable and lint
catalog completeness. Such a projection remains capability-neutral and does
not own the truth of domain results.

## 5. Functional closure and semantic regimes

For a pure deterministic transition `F`:

```text
equal exact subjects and authority states
+ equal identified auxiliary inputs and complete dependency closure
+ equal semantic and checker regimes
---------------------------------------------------------------
= equal normative outcome and result
```

If an undeclared resolver entry, Interface, ProverPlan, theorem, compiler
configuration, target, supplier, policy, or carrier label can change the
answer, the contract is incomplete. The missing material becomes an explicit
input or the hidden read is removed.

A broad resolver may be used while resolving. An immutable result binds only
the exact closure it actually consumed. Later unrelated resolver growth must
not change rechecking. A capability may carry that closed basis; it may not
grant opportunistic access to an open-ended environment.

Effectful activities do not promise equal observations from equal semantic
subjects. They instead bind one occurrence and record the environment,
nondeterministic choices, completion frontier, and externally visible partial
effects needed to interpret that occurrence.

Semantic regime, identity encoding, carrier schema, transport schema, checker
implementation, producer release, and local policy are separate evolution
axes. A decoder accepting bytes under one transport revision does not establish
semantic comparability under another regime.

## 6. Outcome model

The architecture does not define a project-wide `valid : bool`. Each domain
preserves the applicable dimensions of this conceptual product:

```text
procedure:
  completed | refused | failed-operationally | partial-effect-failure

input:
  formed | malformed | unresolved | unsupported | unauthenticated
  | inadmissible | not-applicable

check:
  established | refuted | inconclusive | not-run

result:
  subject | capability | affirmative judgment | negative judgment
  | conditional judgment | quantitative judgment | endpoint result
  | observation | assessment | reliance decision
```

A complete decidable query returning false is a successful negative judgment.
Failure to find a proof is not negative truth without a completeness theorem.
Projection refusal does not invalidate its Protocol. Verifier rejection is a
completed endpoint result, while supplier refusal and executor failure are
operationally different. A negative appraisal and a reliance denial are
successful policy results.

A shared diagnostic envelope is permitted only if it preserves every
domain-owned variant and does not confer a stronger common meaning.

## 7. Identity, capability, and persistence

### 7.1 Identity effects

Contracts use these conceptual effects; exact identity types remain
domain-owned:

| Effect | Meaning |
|---|---|
| Preserve | Represent or re-authorize the same semantic subject |
| Construct | Form a new semantic subject and its domain identity |
| Relate | Leave subjects unchanged and establish a result over their exact identities |
| Configure | Form an immutable dependent configuration without changing its source |
| Instantiate | Create a live or occurrence-scoped identity from configuration and resources |
| Observe | Attribute material to one occurrence without changing the observed subject |
| Decide | Form a policy-qualified assessment or use decision |

There is no global `TransitionId`. Immutable subjects use domain content
identities. A checked relation or derivation receives an identity only when a
real durable consumer needs it. Effectful production, activation, invocation,
recording, and appraisal use occurrence identities. Producer history does not
enter target semantic identity unless it changes canonical target meaning.

### 7.2 Capabilities

Capabilities are opaque, narrow, process-local authority over immutable
subjects or live resources. Their concrete families define copying, borrowing,
threading, attenuation, revocation, expiry, and single-use behavior. A content
identifier is not a capability, and a capability normally has no semantic
identity of its own.

Serialization carries content, configuration, references, and optionally one
purpose-specific checked claim. It never carries continued local authority.
A receiver decodes, authenticates, resolves the exact dependency closure, and
re-admits or verifies the exact claim before minting new local authority.

### 7.3 Durable results

The default is to persist semantic subject bytes, recompute cheap checks, and
keep expensive checked claims local until a named consumer needs exchange,
independent release, caching, retention, or trust separation. A durable result
then belongs to the relation domain and binds the exact subject tuple, regimes,
auxiliary inputs, checker contract, outcome, limits, and witness needed for its
claim.

Likely purpose-specific candidates include independently replayed Analysis
derivations, source-bound projection certificates for a real source-free
consumer, target-specific realization results, and attributable Evidence
records. Admission receipts, compiler decisions, projection records, and one
universal transition artifact are not v0 defaults.

## 8. Mechanism-selection rule

For every edge, its owner applies this order:

1. State the exact proposition or operational postcondition a consumer needs.
2. Close it over every semantic subject, dependency, configuration, policy,
   protected observer, regime, and effect that can change the answer.
3. Recompute a small deterministic predicate directly when exact inputs are
   locally available.
4. For search, optimization, synthesis, or complex production, separate the
   proposer from a per-result validator only when that validator is materially
   smaller, more stable, or independently implementable.
5. If no practical validator exists, name the trusted producer and its exact
   residual trust instead of implying independent checking.
6. Use a paired process-local capability while the exact subjects coexist and
   rechecking is cheap.
7. Introduce a durable witness or certificate only for a named independent
   consumer and only when its checker closes over every semantic input.

Running the producer twice is reproducibility, not automatically independent
validation. A certificate is not preferred merely because a transition can be
drawn as an arrow.

## 9. Selected lifecycle spine

The canonical Protocol lifecycle is:

```text
AuthoringUnit
  -> ResolvedAuthoringUnit
  -> CanonicalProtocolCandidate
  -> AuthenticatedCanonicalProtocol
  -> AdmittedProtocol
```

- authoring and import produce proposals, not Protocol authority;
- resolution binds an immutable snapshot and complete actual read closure;
- normalization forms one physical canonical candidate and may separately
  extract Interface and ProverPlan candidates;
- authentication recomputes canonical form, identities, regime, and
  dependency closure;
- admission establishes the complete normative Protocol predicate and mints
  an opaque immutable local capability;
- official Protocol persistence is admission-gated, while workbench caches
  use an unmistakably unauthoritative envelope;
- decoding reconstructs a carrier, not authority;
- consumer views are question-scoped and cannot become a universal fact root;
- reopening creates an independent mutable branch and discards output
  authority even when no edit follows;
- authoring link constructs a new proposal; and
- semantic Protocol composition constructs and admits a new
  `InteractiveCore`, rather than inheriting child authority.

Authentication and admission are logically distinct even if one
implementation shares a traversal. `AdmittedProtocol` retains the minimal
exact admission basis, not an open resolver that downstream consumers may
query opportunistically.

## 10. Dependent Protocol subjects

### 10.1 `ProtocolInterface`

Interface formation, authentication, and admission are separate from Protocol
admission. An admitted Interface may define external names, positions,
containers, lossless decoding before Protocol meaning, role entry points,
external malformed-input behavior, and relation/application bindings. It may
not change canonical semantic values, proof-event order, transcript inputs or
framing, challenge behavior, checks, claims, accepted language, or terminal
outcomes.

Every interface-sensitive relation, projection, or invocation consumes the
exact dependent `ProtocolInterfaceId`. Protocol-only Analysis remains reusable
across Interfaces. Carrier labels and metadata cannot substitute for an
Interface.

### 10.2 `ProverPlan`

Plan formation, authentication, and admission establish the Plan's own closed
meaning. A separate
`PlanRealizes(AdmittedProtocol, AdmittedPlan, PlanRealizesRegime)` judgment
establishes structural coverage of the exact Protocol's abstract prover obligations. It
does not establish honest-prover completeness, supplier correctness,
performance, or verifier acceptance.

A Plan enters the earliest transition that actually reads it:

```text
if it changes canonical prover OIR:
  projection uses InterfaceAndPlan and OirId includes ProverPlanId

if it selects only below-OIR algorithms, scheduling, buffering, or suppliers:
  OIR remains plan-independent and realization receives the Plan explicitly
```

Verifier projection never consumes a Plan. A field that changes
verifier-visible events, transcript actions, checks, proof ABI, or accepted
language belongs to a different Protocol, not a Plan.

## 11. Transition-family ownership

| Family | Selected contract and owner | Principal non-claim |
|---|---|---|
| Author, import, resolve, normalize | PIR workbench forms and closes proposals | Formation does not authenticate or admit a Protocol |
| Authenticate and admit Protocol | PIR owns canonical identity and whole-Protocol admission | Admission establishes no cryptographic property or endpoint support |
| Persist, decode, re-admit, reopen | PIR transport and lifecycle own representation changes and authority loss | Bytes and no-op content do not preserve capability continuity |
| Interface and Plan lifecycle | PIR authenticates and admits each dependent identity; exact bridges consume admitted subjects | Dependent identity does not prove correspondence, coverage, or completeness |
| Relation ingress and artifact interpretation | Relations admits a relation interface and separately interprets optional artifacts | Reader authority and successful parsing do not establish relation truth |
| Relation correspondence | Relations owns `RelationCorrespondsAtInterface` over exact Protocol, Interface, and relation subjects | Correspondence is not witness satisfaction, Protocol equality, or a property theorem |
| Property analysis | Analysis owns qualified judgments and explicit-plan checking | Search failure is not a negative judgment |
| Checked Protocol change | A producer proposes; PIR authenticates/admit the target; the relation-specific bridge validates predecessor and successor | A target ID or structural legality proves no source/target relation |
| Compiler selection | Compiler selects only among already admitted, relation-checked candidates over an exact domain | Winner validity does not establish optimality over an omitted candidate |
| FS construction | PIR deterministically forms and ordinarily admits the FS Protocol | Construction is not `FSCompile` |
| `FSCompile` | Analysis owns the theorem/model-backed judgment, co-designed against PIR semantics | It does not transport every property automatically |
| `PropertyTransport` | Analysis checks a property-specific rule over a source judgment and exact relation | Relation adjacency or a preservation annotation is insufficient |
| OIR projection | OIR owns role projection over exact Protocol, Interface, and tagged Plan basis | Unsupported projection does not invalidate the source |
| Standalone OIR admission | OIR owns `LocalOirValid` | Local validity cannot prove origin or omitted-source coverage |
| Supplier binding | Realization closes exact provider designations and separately resolves live provider authority | A binding does not prove provider correctness or permanent availability |
| Realization | Realization separates effectful production from target-specific `RealizesOir` checking | Emission or build success is not semantic realization |
| Deployment and invocation | Realization owns configuration, activation, binding, execution, and partial effects as distinct operations | Operational outcomes cannot redefine Protocol or OIR semantics |
| Evidence and appraisal | Evidence turns attributed observations into claim-scoped records and policy-qualified assessments | Authentic provenance is not truth or permission |
| Reliance | The consuming domain applies its own use policy | One assessment need not authorize another consumer or use |

Bridge ownership follows the result: the domain that defines the newly minted
result owns its contract and cites every source owner. Shared review does not
create shared semantic authority.

## 12. Selected semantic bridge rules

### 12.1 Checked change

The order for a nonidentity Protocol change is:

```text
propose successor
  -> authenticate successor
  -> admit successor
  -> check one exact predecessor/successor relation
  -> use that checked edge for selection or property transport
```

An admitted successor may exist even when its proposed relation to one
predecessor is refuted. Compiler selection therefore consumes already admitted
subjects and checked edges; it does not make them true by selecting them.

### 12.2 Fiat--Shamir

Three contracts remain separate:

1. deterministic construction and admission of an FS Protocol over an existing
   Core;
2. theorem- or model-backed `FSCompile` over exact fresh and FS Protocols,
   transcript construction, occurrence/prefix map, regime, and assumptions;
3. property-specific `PropertyTransport` under its own hypotheses and losses.

An FS Protocol may exist without an available `FSCompile` judgment. One
`FSCompile` result does not transport every property.

### 12.3 Projection

Projection keeps these propositions distinct:

```text
LocalOirValid(O)
ProjectionCorrect(P, I, role, plan_basis, O)
```

A paired projection capability may authorize source-relative use while the
admitted source subjects and OIR coexist. After serialization, standalone OIR
can be re-admitted locally, but source coverage is unknown unless a consumer
rechecks against the sources or verifies a sufficient source-bound result.
`OirId`, an embedded source reference, or a digest cannot prove that no source
obligation was omitted.

## 13. Composition and operational sequence

The architecture supports five different notions of composition:

1. **Procedural sequencing:** a result capability satisfies the next input
   precondition; this creates no end-to-end theorem.
2. **Relation composition:** an exact owner supplies a law carrying maps,
   assumptions, protected observers, losses, regimes, and intentional changes.
3. **Property transport:** Analysis checks one property-specific rule over a
   source judgment and checked relation.
4. **Protocol composition:** PIR constructs a new Core with tagged occurrences,
   causal seams, one total schedule, challenge policy, domain separation,
   failure propagation, and new obligation/dependency closure.
5. **Operational sequencing:** Realization defines effects, rollback,
   compensation, retries, concurrency, and partial-failure behavior.

A certificate chain establishes only the conjunction or composed claim that an
explicit checker proves. Matching intermediate identifiers or provenance
adjacency is insufficient.

Operational flow is intentionally longer than a single “realize” arrow:

```text
admitted OIR
  -> exact supplier binding
  -> narrow live provider authority
  -> effectful realization production occurrence
  -> target-specific RealizesOir check
  -> admitted realization
  -> deployment binding
  -> activation and live deployment capability
  -> invocation binding over exact Interface, request, inputs, policy, and regime
  -> endpoint execution with typed result and attributed observation
     or operational/partial-effect failure
```

Product commands may fuse these steps for usability, but must preserve which
gates completed and which external effects remain.

## 14. Evidence, appraisal, and reliance

The selected chain is:

```text
producer-owned observation
  -> Evidence-owned attributable record
  -> policy-qualified claim assessment
  -> consumer-owned use-specific reliance decision
```

The record binds its claim, subjects, issuer, procedure, environment, pins,
scope, and relevant occurrence. Appraisal adds evidence policy, trust anchors,
reference values, context, and time. Reliance adds the actual consumer,
intended use, and current use policy. Different consumers may therefore reach
different valid decisions over the same assessment without changing semantic
history.

No arrow in this chain points backward into Protocol, Interface, Plan, OIR, or
realization identity or admission.

## 15. What this enables

The selected architecture makes it possible to:

- support several authoring languages and normalizers behind one canonical
  Protocol acceptance boundary;
- let heuristic compilers, projectors, planners, and emitters compete while
  small stable validators remain authoritative where feasible;
- reuse one Protocol across several Interfaces and ProverPlans without hidden
  label or plan reads;
- reuse Protocol-level Analysis while separately keying interface-, plan-, and
  realization-sensitive judgments;
- operate on locally admitted source-free OIR while reporting source coverage
  honestly as unknown;
- vary suppliers, realizations, and deployments below one fixed endpoint
  contract;
- strengthen assurance per edge later without imposing certificates on the
  entire pipeline;
- distribute search and caching without serializing admission authority;
- expose capability-neutral provenance and catalog views without a universal
  semantic fact root; and
- evolve regimes through explicit checked migration relations rather than
  silent byte reinterpretation.

These are option-preserving consequences of the architecture, not
implementation or proof claims.

## 16. Deliberate deferrals

Stage 2 did not select:

- exact operation, API, type, attribute, diagnostic, hash, or file spellings;
- complete Protocol, Interface, Plan, relation, Analysis, Compiler, OIR,
  Realization, Evidence, or policy schemas;
- a theorem prover, solver, proof system, validator framework, or backend
  checker;
- portable admission, transition, projection, compiler-decision, or universal
  evidence records;
- compatibility windows or cross-regime migration formats;
- which concrete compiler, projection, and realization families possess a
  genuinely smaller independent validator; or
- an implementation migration sequence or conformance claim.

Stage 3 subsequently selected candidate Protocol, canonical PIR, Interface,
Plan, Relations, Fresh-to-Fiat--Shamir, and semantic Core-composition contracts
at its non-normative package resolution. Their integrated closure is reopened.
Analysis, Compiler, OIR, Realization, Evidence, concrete encodings and
checkers, compatibility, implementation, and migration remain with their later
owners. Historical deferrals cannot justify ambient inputs, generic validity,
serialized local authority, source coverage inferred from source-free targets,
or policy backflow.

The durable [v0 Semantic Design Program](v0-design-program.md) owns the stage
sequence and exit gates. Stage 3 completed its bounded package under the selected
[Protocol and Relations Architecture](protocol-and-relations-architecture.md).
A detailed historical handoff remains in the completed Stage 2 research
package, but no durable decision depends on retaining it. Stage 4A subsequently
completed its bounded package under the selected [Analysis and Compiler
Architecture](analysis-and-compiler-architecture.md); Stage 4B remains
unactivated.

## 17. Reversal conditions

Reopen the relevant decision when concrete evidence shows that:

- several important relation families share actual semantics, authority,
  outcomes, replay, composition laws, and a generic consumer, justifying a
  common executable algebra;
- a named heterogeneous cross-process consumer requires a universal durable
  transition DAG and domain adapters cannot serve it safely;
- a capability family cannot expose explicit lifetime and reconstruction
  across language, thread, FFI, plugin, or process boundaries;
- a named consumer cannot economically reconstruct required authority from
  subjects and claim-scoped results;
- a proposed validator duplicates its producer, requires unavailable hidden
  state, or cannot represent incompleteness honestly;
- rechecking becomes unavailable or prohibitively expensive for a real
  independent consumer;
- a plan field cannot be placed at exactly one explicit projection or
  realization boundary without changing Protocol behavior;
- an operational activity lacks a meaningful completion or partial-effect
  frontier; or
- any normative output changes after only an undeclared input changes.

Reopening must name the affected subjects, owners, relation, identity,
capability, outcome, consumer, wire commitment, and neighboring contracts. It
may not hide the contradiction inside a generic record.

## 18. Research basis and non-claims

This decision is the durable result of the temporary Stage 2 research package
routed through the
[temporary workspace inventory](../notes/README.md#working-note-inventory).
That package contains the current-system reconstruction, external
primary-source cases, equal-resolution candidates, independent scenario tests,
convergence record, and current-to-target gap map. Those notes are evidence for
this decision, not future normative dependencies.

In particular, this page does not claim:

- that any proposed transition, checker, capability, result, or schema is
  implemented;
- that current compiler replay is an independent translation validator;
- that current opaque C++ types form a complete capability system across FFI,
  threads, plugins, processes, or languages;
- that any Protocol property, checked change, projection, realization,
  completeness claim, `FSCompile`, or evidence assessment has been proven;
- that tests inspected during reconstruction establish more than bounded
  implementation correspondence; or
- that current implementation gaps are bugs or vulnerabilities.

Current-to-target migration and implementation conformance belong to later
program stages and must not constrain this clean-sheet target retroactively.
