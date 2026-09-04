# Stage 4A design forces and opportunities

> **Document kind:** Temporary design-force and opportunity record
> **Document state:** Completed and frozen Stage 4A.2 research synthesis;
> target-neutral
> **Authority:** None. This page constrains candidate comparison but does not
> define an Analysis or Compiler judgment, select a model, establish a theorem
> or compiler result, report implementation support, or authorize migration.
> **Prepared:** 2026-08-22
> **Inputs:** Frozen Stage 3 target contracts, current-model reconstruction,
> primary-source Analysis and Compiler cases, and ZK-specific theory cases
> **Disposition:** Absorb accepted forces, reversal conditions, and enabled
> capabilities into durable architecture and target specifications; delete
> this page with the temporary package.

## 1. Purpose and method

This page states what an ideal Stage 4A architecture must make true before any
particular type hierarchy, checker API, proof assistant, optimizer, or wire
format is favored.

The forces are derived from four independent sources:

1. the semantic subjects, views, authority, outcomes, and replay rules frozen
   by Stages 1--3;
2. the strongest current Soundness and Compiler mechanisms and their confirmed
   disagreements;
3. lessons and accumulated constraints from primary formal-analysis,
   validation, compiler, and ZK systems; and
4. capabilities that become possible only after Analysis meaning and Compiler
   policy are separated cleanly.

Current implementation cost, class layout, compatibility, and migration effort
are deliberately excluded from candidate selection. A force must follow from
meaning, authority, trust, consumer need, or option value—not from the ease of
retrofitting the checkout.

## 2. Whole-system invariant

The Stage 4A target must preserve this authority order:

```text
exact admitted subjects and owner-created views
  -> exact semantic question under an exact model and assumptions
  -> checked direct procedure, derivation, theorem correspondence, or certificate
  -> Analysis-owned qualified judgment

admitted predecessor
  -> unauthoritative proposal
  -> independent target authentication and admission
  -> exact checked predecessor/successor relation
  -> constraints and objectives over qualified facts
  -> complete-domain comparison or explicitly incomplete attempt result
  -> Compiler-owned qualified decision or non-decision report, respectively
```

No arrow may be replaced by a digest comparison, provider assertion, theorem
name, prior success receipt, score, cache entry, or serialized capability.

## 3. Analysis design forces

### A1. zkc owns proposition meaning

An Analysis question must have an exact zkc-native semantic meaning independent
of the tool that proves, refutes, approximates, or fails to answer it.

A Lean theorem, Rocq term, EasyCrypt lemma, SMT query, probabilistic checker,
test result, or paper citation may be part of a basis. It cannot be the identity
or meaning of the zkc proposition. Otherwise changing proof infrastructure
would silently change the subject of reasoning.

### A2. One lifecycle does not imply one universal payload

Equality, trace refinement, distributional distance, soundness, completeness,
knowledge, zero knowledge, cost, FS applicability, transport, and composition
share lifecycle needs:

- exact subjects and views;
- model and assumption closure;
- derivation or direct-check basis;
- qualified outcomes;
- authority and replay; and
- residual trust.

They do not necessarily share a subject tuple, result algebra, observer,
negative meaning, proof rule, or quantitative domain. A thin common envelope
may coordinate the lifecycle, but family-specific payloads must remain typed.

### A3. Every semantically read subject is explicit

Question identity must name every admitted subject and every owner-created view
whose information can affect the proposition or its answer. This includes, when
read:

- Protocol, Core, Interface, Plan, relation, definition, instance, witness
  occurrence, construction, composition, OIR, target, supplier, and endpoint
  subjects;
- exact maps and structural capabilities;
- observer, event, failure, and terminal projections; and
- dependency and interpretation regimes.

An ambient registry, namespace, loaded module, prover environment, or Compiler
context cannot supply hidden semantic input.

### A4. Read closures are complete and owner-created

An Analysis view is an attenuation of upstream authority, not a second
representation of the subject. Its owner declares the complete field and
dependency closure. Analysis may refuse an insufficient view or request a new
owner-defined view; it may not reopen carrier internals or infer missing facts
from bytes.

This keeps proposition identity stable when implementation representations
change.

### A5. Models and observers are proposition coordinates

The same subjects under different observations or semantic regimes can yield
different propositions. Exact question identity includes all applicable:

- core or operational semantics;
- trace alphabet and event projection;
- observer and visibility set;
- termination, divergence, stuck, abort, and failure treatment;
- probabilistic space, subdistribution/losslessness policy, coupling, and
  correlation;
- adversary initialization, auxiliary input, state, oracle access, rewinding,
  and resource bounds;
- transcript/hash or random-oracle model;
- cost machine, environment, and measurement model; and
- direction of refinement or implication.

There is no model-independent `TraceEq`, `Equivalent`, `Secure`, or `Cheaper`.

### A6. Security regimes remain distinct

Perfect, statistical, computational, concrete, and asymptotic conclusions
must not be collapsed. Extensional distribution equality does not establish
computational feasibility. A concrete finite bound does not automatically
become an asymptotic theorem. Any lift between regimes is an explicit checked
rule with its own assumptions and side conditions.

The preferred v0 research baseline is finite or subdistribution semantics with
typed symbolic concrete bounds and explicit certified asymptotic lifts. This
is a scope hypothesis for candidate testing, not yet a selected target.

### A7. Hypotheses form a typed dependency closure

Conditional Analysis is first class. A judgment retains, rather than hides:

- previously established exact judgments;
- declared cryptographic or hardness assumptions;
- semantic idealizations such as a random-oracle model;
- termination and losslessness conditions;
- adversary, state-separation, and oracle restrictions;
- quantitative side conditions;
- model- and statement-correspondence obligations; and
- explicit unproved assumptions introduced by an accepted rule.

Dependencies form an acyclic typed graph. Substitution, inheritance,
discharge, strengthening, weakening, and residual hypotheses are governed by
named rules rather than string manipulation.

An unmet correspondence or side condition may be retained only by changing
the proposition itself to an exact conditional claim such as
`Gamma |- P`. It cannot answer an unconditional request for `P`, mint the
unconditional capability, or satisfy a Compiler constraint that requested
`P`. If the requested proposition does not include the residual obligation,
the qualified operational outcome is `CannotAnswer`, not an affirmative
approximation.

### A8. Quantitative expressions are dimensioned

Probability, advantage, statistical distance, query count, running time,
rounds, field size, bytes, and asymptotic functions are not interchangeable
scalars. Each rule owns a total typed transformer over exact dimensions and
records every side condition.

No candidate may accept invalid units, negative loss where prohibited,
implicit rounding, an unevaluated comparison treated as true, or dropped
conditioning mass.

### A9. Proposition, basis, derivation, judgment, and replay identities differ

At minimum, the architecture must distinguish:

```text
Analysis proposition
  exact semantic claim

Derivation basis
  rules, models, theorems, assumptions, imports, encodings, and checker contract

Derivation
  one exact proof plan, proof term, refutation, or certificate

Qualified judgment
  proposition + completed semantic outcome + retained basis qualification

Replay occurrence
  one actual reconstruction/check event

Live capability
  process-local authority minted by the successful current check
```

Multiple derivations may support one proposition. Multiple independent
checkers may validate one derivation. Neither should change proposition
identity.

### A10. External formalization requires three correspondences

An external theorem can support an Analysis result only when the basis closes:

1. the exact elaborated external statement and assumption closure;
2. the mapping between its symbols, objects, semantics, and exact admitted zkc
   subjects; and
3. the sufficient implication direction from the checked external statement
   to the requested zkc proposition.

Literal equivalence is not always required. A checked sound abstraction or
one-way implication may suffice, but its direction and loss must be explicit.
Proof checking alone establishes none of these correspondence layers.

### A11. Checking lanes remain qualified

The architecture should permit several bases without pretending they carry the
same residual trust:

1. a complete direct decision procedure;
2. an internal typed derivation;
3. an external proof-assistant theorem with checked correspondence;
4. a proof-producing solver or independently checked certificate;
5. a trusted but non-proof-producing solver, explicitly qualified; and
6. measured or experimental Evidence consumed through a named sound inference
   rule, if one exists.

The outer semantic proposition remains stable across lanes. A universal proof
object is not required merely to offer a common envelope.

### A12. Negative meaning is family-specific and completeness-backed

`Negative` means either:

- an exact checked refutation or proof of the family's defined negation; or
- rejection by a complete decision procedure for the exact proposition.

Timeout, proof-search failure, certificate invalidity, solver `unknown`, model
unsupportedness, unavailable correspondence, or checker failure is not a
negative property result. A counterexample must retain the exact observer,
model, input, trace, or witness scope that makes it a fact.

### A13. Qualified operational outcomes remain distinct

The common lifecycle distinguishes:

```text
Affirmative
Negative
Unsupported
CannotAnswer
Refused
Malformed
CheckerFailure
```

Families may refine these variants, but may not collapse them into one false
or error bit. Only a completed semantic result may mint the corresponding live
judgment capability.

### A14. Direct relations stay semantically distinct

The target preserves separate typed families for:

- `CoreEq`;
- `ProtocolEq`;
- `TraceEq[observer]`;
- directed `TraceRefines[source,target,observer]`;
- distribution equality;
- directional or symmetric bounded distributional closeness;
- intentional change against protected and permitted observations; and
- cost comparison under an exact cost model.

Stronger relations may be derived only through rules carrying exact
determinacy, receptiveness, losslessness, adequacy, or observer premises.

### A15. Cryptographic properties use property-specific experiments

Soundness, knowledge, completeness, zero knowledge, and other selected
properties are not tags on a Protocol. Each family fixes:

- exact subject tuple;
- experiment or game;
- adversary and oracle interfaces;
- setup and initialization;
- success, failure, abort, and conditioning events;
- observer and auxiliary input;
- quantitative parameters and result; and
- admissible theorem and composition rules.

The target may provide an extensible profile mechanism, but v0 support is the
closed set of profiles with actual rule/checker contracts. An empty profile
catalog is honest support for a future family; it is not a proof result.

### A16. Structural FS construction and cryptographic FS reasoning differ

Affirmative `CheckedFSConstruction` establishes exact structural maps between
admitted Fresh and Fiat--Shamir Protocols. It does not establish a security
theorem.

The research must test a two-step Analysis factorization:

```text
exact structural construction
  + exact theorem/model applicability and bound transformer
  -> property-specific transport port

exact source property
  + affirmative applicable property port
  -> exact target property with explicit loss and residual hypotheses
```

This preserves Stage 3's structural separation while avoiding a false generic
claim that one `FSCompile` theorem transports every property.

### A17. Structural composition and property composition differ

`CheckedCoreComposition` supplies exact children, target, occurrence maps, and
structural wiring. Property composition separately states:

- the exact child property occurrences;
- shared, joint, imported, derived, and substituted randomness;
- captured failure and reach behavior;
- challenge correlation and oracle state;
- terminal combination and suppression;
- intentional changes;
- assumptions and bound combination; and
- the exact target property.

There is no default property preservation through structural composition.

### A18. Relation satisfaction needs one explicit semantic owner

Predicate truth for an admitted external relation instance must have one
explicit semantic owner. Relations is a plausible owner because definition,
instance, interpretation, and satisfaction form one base-relation surface.
Analysis is a plausible owner when satisfaction is treated as a checked
semantic question sharing its outcome and derivation lifecycle. The
target-neutral force does not choose between them. Cryptographic properties
may consume the result under either choice, and correspondence never implies
satisfaction.

Candidate evaluation must compare both ownership options explicitly against
authority locality, witness confidentiality, negative meaning, reuse by
non-Analysis consumers, checker placement, and dependency closure. Any
accepted owner preserves:

- exact relation definition, interface, instance, and interpretation regime;
- one occurrence-local secret witness capability;
- exact public and witness values;
- qualified outcomes and negative meaning;
- checker/model and dependency basis; and
- no leakage of witness material into public judgment identity or records.

### A19. Coverage is not a generic property

Protocol structural owners define the required observation, claim, round, or
obligation surface. Analysis may answer whether an exact set of qualified
property judgments covers that surface, but it cannot invent the required
surface. Candidate designs must distinguish structural coverage requirements
from property-coverage assessment and from endpoint realization coverage.

## 4. Compiler design forces

### C1. Production is replaceable and unauthoritative

MLIR transforms, e-graphs, SMT synthesis, verified rewriters, manual plans,
learned search, and future producers may all propose candidates. Producer
choice and search policy do not define Protocol meaning, target authority,
transform validity, domain completeness, or optimization truth.

Adding a new producer for an existing checked transform family should require
no new semantic authority. Adding a new transform family requires a new exact
relation and checker or theorem contract.

### C2. Proposal, target admission, and relation checking are separate

A proposal contains bytes or a construction plus unauthoritative maps, hints,
and certificates. PIR independently authenticates and admits the whole target.
The transform checker then consumes exact admitted predecessor and successor
subjects.

Target admission establishes only valid target Protocol meaning. It does not
establish that the proposal followed a requested transformation or preserved
any relation or property.

### C3. Transform relations are family-specific

Every transform family defines an exact contract with:

- predecessor and successor subject types;
- direction and observer/model;
- intentional-change policy;
- required maps and lineage;
- assumptions and side conditions;
- checker, proof, or certificate basis;
- qualified outcomes and residual trust; and
- the live capability emitted by an affirmative result.

A generic dispatch envelope is useful. A generic semantic `Equivalent` or
`Preserves` predicate is not.

### C4. Multi-step paths expose exact admitted intermediates

If a proposed plan claims several semantic steps, every semantic intermediate
used by a relation is independently admitted and every adjacent edge is
checked. Operational producer IR that carries no semantic claim may remain
unauthoritative.

An end-to-end relation may additionally be checked. It cannot replace adjacent
checks unless a named rule proves that the omitted intermediates are irrelevant
to the exact requested relation and consumers.

### C5. Lineage and semantic relation differ

Claim, event, challenge, and occurrence lineage identifies how source and
target parts correspond. It is a checked witness input to a semantic relation,
not the relation itself. Retain, remove, introduce, split, merge, fold, and
rename maps must be exact and family-appropriate.

### C6. Alternative, transition, qualification, and assessment identities differ

A closed domain needs an identity for every member before target admission,
including a member whose proposal is malformed or whose target later fails
admission. At minimum the architecture distinguishes:

```text
AlternativeDescriptorId
  one canonical pre-admission domain member or submitted alternative

TargetAlternativeId
  the independently admitted target, when admission succeeds

TransitionClaimId
  exact predecessor, admitted target, direction, relation/model,
  intentional changes, and semantically read path

QualificationBasisId
  checker, proof, certificate, assumptions, dependencies, and residual trust

AssessmentId
  request policy + alternative + available target and transition claims
  + the exact qualification, constraint, and objective inputs read
```

The qualification basis does not change transition meaning merely because a
different proof establishes the same claim. It remains bound into assessment,
decision, and replay, and it may distinguish assessed alternatives when the
request explicitly reads residual trust or proof basis.

Two proposals that reach the same admitted target may be deduplicated only by
an explicit domain rule showing that descriptor, path, basis qualification,
constraints, objectives, replay, and consumers are unaffected. Target identity
alone is not a safe universal deduplication key. Failed admission does not erase
the pre-admission member from a domain whose completeness claim included it.

### C7. Search result and comparison domain differ

The set a producer happened to find is not automatically the set over which an
authoritative decision claims completeness. The Compiler must identify:

- the proposal frontier;
- the declared comparison domain;
- the coverage/completeness basis for that domain;
- canonical membership and duplicate rules; and
- the set of fully assessed candidates.

Incomplete search may yield useful feasible or frontier results. It cannot
yield closed optimality or closed `NoSelection`.

### C8. Several domain forms may be valuable

Candidate testing should compare:

1. explicit finite submitted frontiers with no completeness beyond membership;
2. canonical finite grammar and bounds with full enumeration;
3. a symbolic finite domain with independently checked denotation and closure,
   plus a separate infeasibility or optimality certificate when claimed; and
4. incomplete heuristic exploration producing a qualified non-decision
   feasible or partial-Pareto report.

A symbolic certificate must bind the exact domain denotation, encoding
correspondence, finiteness, membership, duplicate policy, and coverage or
pruning claim. An optimality certificate proves neither domain closure nor
target admission, transition validity, constraint satisfaction, or objective
adequacy unless its independently checked statement explicitly includes those
obligations. Closure, infeasibility, and optimality certificates are distinct
bases even when one proof format can encode all three.

The v0 default should favor small canonical finite domains unless another form
demonstrates equal interpretability and replay. This is a research hypothesis,
not a conclusion.

### C9. Assessment is total only within declared supported questions

For each domain member the Compiler records target admission, transform
relation, required Analysis results, constraint evaluation, objective
availability, and any disqualifying fact. Unsupported or failed infrastructure
must not be reclassified as a semantic rejection.

A closed `NoSelection` requires complete domain coverage and a completed
eligibility answer for every member under the request's exact policy.

### C10. Constraints consume qualified facts without redefining them

A constraint specifies which exact qualified outcome and result predicate it
accepts. An affirmative eligibility premise requires the exact affirmative
capability. A negative result may be useful only to an explicitly negative
constraint; it cannot satisfy an affirmative premise.

The Compiler cannot weaken assumptions, reinterpret observers, coerce a
different property family, convert `CannotAnswer` to false, or compare bounds
from incompatible models.

### C11. Objectives are typed and basis-qualified

An objective states:

- exact value type and units;
- subject and model;
- derivation or observation basis;
- direction and comparison law;
- availability conditions; and
- deterministic tie policy.

Exact structural sizes, Analysis-derived cost models, and measured endpoint
performance are different sources. Measurements remain environment- and
procedure-qualified. Stage 4B endpoint feasibility or runtime cost cannot
become a hidden Stage 4A criterion when absent from the request.

### C12. Comparison policy is explicit

Lexicographic comparison, weighted aggregation, constrained minimization, and
Pareto selection are materially different claims. The candidate architecture
must not smuggle preference through provider order.

For deterministic single-winner selection, a canonical semantic candidate ID
is the safe default final tie-break. If proposal priority or user order matters,
it appears as an explicit objective or policy coordinate.

### C13. Attempt reports and qualified decisions are different products

Within the frozen Stage 3 ordering, only the following complete-domain results
are qualified Compiler decisions:

- selected best member of one declared complete finite domain; and
- no eligible member of one declared complete finite domain.

The Compiler attempt lifecycle must additionally represent:

- a checked feasible member without an optimality claim;
- a qualified partial frontier from incomplete exploration;
- search or assessment incomplete;
- unsupported request, model, or family;
- refused request;
- malformed request, proposal, attempt report, or decision record; and
- checker or infrastructure failure.

These are useful search, proposal, assessment, or operational reports, but they
do not mint `QualifiedDecision` authority. Promoting an incomplete-search
result to a new decision family would require the chartered Stage 3 reopening
procedure. Names may differ, but neither the meanings nor the authority kinds
may collapse.

### C14. The decision retains its interpretable basis

A decision identifies the request, comparison claim, domain basis, candidates
or coverage proof, assessments, comparator, tie rule, selected target or
closed no-selection fact, residual trust, and exact consumers. It does not
create Protocol admission, transform relation, property transport, or endpoint
feasibility.

### C15. Replay is independent of producer rerun

Cold decision replay reconstructs subjects and bases, rechecks admissions,
relations, Analysis inputs, constraints, objectives, domain coverage, and
selection, then mints fresh local authority.

This differs from:

- rerunning a mutable producer and observing the same candidate; and
- reproducing identical proposal bytes.

Neither producer reproducibility nor cache equality is required for semantic
decision replay.

## 5. Cross-domain forces

### X1. Capabilities prove only one exact fact

Live capabilities remain process-local, non-serializable authority for one
exact subject, question, basis, and successful result. Capability conversion
requires a named checked rule. A generic `Verified`, `Valid`, `Legal`,
`Preserved`, or `Accepted` capability is forbidden.

### X2. Persistence is consumer-justified

Cheap checks should be recomputed. A replay bundle is justified only by a named
independent consumer, trust separation, expensive reconstruction, release
boundary, or cross-process requirement. The bundle retains complete basis and
dependency identity but never live authority.

### X3. Caches are hints, never authority

A cache hit may avoid producer or proof search work. It becomes usable only
after exact basis matching and the required revalidation. Cache keys include
all semantics-, assumption-, checker-, domain-, objective-, and environment-
relevant identities. Unsupported basis drift makes an entry stale, not false.

### X4. Evidence and theorem conclusions differ

Tests, benchmarks, proof-check receipts, model-check traces, solver logs, and
runtime observations belong to Evidence as scoped observations. Analysis may
consume them only through an explicit inference rule that states why the
observation suffices for the exact proposition. Compiler may consume only the
resulting qualified Analysis judgment or an objective explicitly defined as a
measurement, never an unattributed receipt.

### X5. Extension is closed at semantic dispatch and open at production

The v0 semantic property, rule, model, relation, objective, and result profiles
are versioned closed sets with explicit extension boundaries. Producer
implementations and proof-search strategies are replaceable and open. Unknown
semantic tags are `Unsupported`, not dynamically trusted callbacks.

### X6. Trust is named, not implied by architecture style

The target distinguishes:

- semantic specification;
- trusted implementation;
- machine-verified checker;
- independently checked certificate;
- solver-trusted result;
- theorem/model correspondence trust;
- empirical observation; and
- consumer reliance.

A small checker is not automatically verified. A proof-producing tool is not
useful unless its proof and encoding are checked. A verified producer does not
automatically establish an unmodeled property.

### X7. Every checking chain has explicit trust roots

The architecture must say how the following become usable semantic inputs:

- family-profile and result-schema definitions;
- semantic-model definitions and model instances;
- rule and theorem schemas;
- claims that a direct procedure is sound or complete;
- external statement, subject, and model correspondences;
- certificate-language and query-encoding adequacy; and
- checker implementation correspondence to its specified algorithm.

Each item is either established by a named direct or mechanized root check,
derived from already established roots, or retained as explicit residual
trust. Moving a claim into another proof system does not close the chain unless
the translation and target logic are also bound. A correspondence checker
cannot defer its own meaning to an unbounded regress of unchecked
correspondence claims.

## 6. Capability-expanding opportunities

The redesign should be evaluated not only by whether it repairs current gaps,
but by whether its factorization enables new sound capabilities.

### O1. Proof-system-independent propositions

One exact zkc proposition can be supported by an internal derivation today and
an external formal proof tomorrow without changing consumer meaning. Multiple
independent bases can corroborate one proposition while preserving their
different residual trust.

### O2. Family-specific counterexamples as reusable facts

A complete direct checker may return an exact trace, input, witness, or model
counterexample. The negative result can then constrain Compiler eligibility,
guide producer search, or become Evidence without being collapsed into a
generic failure.

### O3. Property profiles without universalizing one logic

New property families can add exact subject/result/model/rule profiles behind
the common lifecycle. Zero knowledge, side-channel properties, robustness, or
new knowledge notions need not distort Soundness or equality results.

### O4. Property-specific FS and composition ports

Structural FS and composition capabilities can expose exact premise maps while
separate Analysis rules offer only the property ports actually justified by
known theorems. New research can add a property theorem without changing
Protocol admission or Compiler semantics.

### O5. Pluggable optimization producers

MLIR transformations, equality saturation, verified rewriting, SMT synthesis,
manual expert plans, and learned search can compete over the same exact
proposal and relation contracts. Producer innovation does not expand the
semantic trusted base.

### O6. Mixed verification strategies by transform family

Small stable transforms can be verified by construction; evolving transforms
can use instance validation; search-heavy transforms can carry certificates;
and unsupported families can remain unavailable. The common Compiler contract
does not force one method.

### O7. Honest useful results from incomplete search

The Compiler attempt can return a checked feasible candidate or partial Pareto
frontier in a non-decision search or assessment report without pretending the
search was complete. This enables heuristic and anytime optimization while
preserving the exact authority boundary of `QualifiedDecision`, optimality,
and `NoSelection` claims.

### O8. Symbolic domain-coverage certificates

Future certifying solvers can establish finite-domain coverage, infeasibility,
or optimality without materializing every candidate. Their certificates remain
separate from candidate relation and property bases.

### O9. Independent decision consumers

A deployment planner, release gate, or audit tool can cold-replay an exact
decision without rerunning the original producer. This becomes possible only
because proposal search, semantic checks, domain completeness, and selection
are separately identified.

### O10. Cross-layer objectives without hidden coupling

When Stage 4B later supplies exact endpoint feasibility or cost results,
Compiler can consume them as explicitly requested qualified inputs. The same
architecture supports purely Protocol-semantic selection now and endpoint-
aware selection later without retroactively changing candidate meaning.

## 7. Candidate falsifiers

Any candidate is rejected or revised if it permits one of the following.

1. Two Analysis propositions that differ in subject, observer, direction,
   initial state, auxiliary input, losslessness, adversary model, assumption,
   or semantic regime share one identity.
2. Changing a proof term, prover, checker occurrence, or search resource limit
   changes proposition meaning rather than only its basis or attempt.
3. A theorem name, proof file, successful exit code, or solver response mints
   an Analysis capability without exact statement and model correspondence.
4. A timeout, failed proof search, invalid certificate, solver `unknown`, or
   unsupported rule becomes a negative semantic result.
5. A conditional conclusion loses inherited or residual assumptions.
6. A bound transformer mixes dimensions, drops a side condition, or hides
   abort/failure mass.
7. Trace equality or refinement can be stated without an exact observer and
   termination/failure policy.
8. Distribution equality implies computational feasibility or cost without a
   separate checked rule.
9. Structural FS construction or Core composition transports a property by
   default.
10. Relation correspondence, equal bytes, or a Protocol admission result
    implies relation satisfaction.
11. A Compiler producer creates an admitted target or relation capability by
    assertion.
12. MLIR verification, transform execution, dialect legality, e-graph
    membership, or solver success implies Protocol transform validity.
13. A provider's discovered set silently becomes a complete domain.
14. Incomplete search, missing assessment, or operational failure produces
    closed `NoSelection` or optimality.
15. Provider ordinal resolves a semantic tie without an explicit policy.
16. A Compiler constraint reinterprets an Analysis family, model, hypothesis,
    or qualified outcome.
17. A measured objective lacks environment and procedure identity.
18. A persisted record, signature, or cache hit rehydrates live authority.
19. Decision replay requires mutable producer behavior rather than exact
    semantic inputs and bases.
20. The architecture must expose private witness material publicly to identify
    a relation-satisfaction judgment.
21. A declared domain member has no stable identity until after target
    admission, so failed admissions disappear from completeness accounting.
22. A feasible result, partial frontier, timeout, or incomplete assessment
    mints the same authority kind as a complete-domain Compiler decision.
23. A semantic model, family profile, completeness claim, correspondence, or
    checker implementation becomes trusted only by pointing to another
    unchecked adapter or callback.

## 8. Deliberate non-goals

Stage 4A does not need to:

- prove any concrete zkc protocol property;
- select one proof assistant, solver, optimizer, or producer;
- support arbitrary continuous probability or a universal measure-theoretic
  logic in v0;
- make every Analysis family decidable;
- make every transform family checkable;
- guarantee global optimization beyond an exact declared domain;
- define OIR projection, target realization, endpoint feasibility, or runtime
  execution;
- make all replay bundles portable across every version or environment;
- define implementation modules or APIs;
- plan migration or compatibility; or
- preserve current naming, registry, encoding, or class boundaries.

It must make every unsupported or deferred capability explicit and safe.

## 9. Equal-resolution candidate axes

Every candidate must answer the same axes before selection:

| Axis | Required resolution |
|---|---|
| Semantic center | Native family calculus, universal logic, external systems, direct checkers, or hybrid |
| Proposition family | Exact subjects, models, observers, parameters, results, and negative meaning |
| Identity | Proposition, basis, derivation, judgment, pre-admission alternative, admitted target, transition claim, assessment, attempt, capability, and persistence |
| Context | Views, read closure, hypotheses, dependencies, substitutions, and extensions |
| Checking | Direct, derivational, external theorem, solver, certificate, measurement, and trust qualification |
| Quantitative layer | Dimensions, expressions, side conditions, concrete/asymptotic regimes, and loss |
| Cross-family rules | Equality/refinement implications, FS, transport, composition, coverage, and satisfaction |
| Proposal plane | Producer freedom, plan/recipe form, hints, maps, and intermediate subjects |
| Transform plane | Target admission, exact family relation, checker method, lineage, and outcomes |
| Candidate/domain | Identity, deduplication, domain forms, completeness, pruning, and assessment |
| Policy plane | Constraints, objectives, comparison, ties, frontiers, no-selection, and incomplete search |
| Replay/trust | Live authority, caches, persistence, cold replay, residual trust, and consumers |
| Extension | Closed semantic profiles, open producers, versioning, unknowns, and reversal conditions |
| Peer boundaries | Stage 4B, Evidence, reliance, and current-to-target gaps |

No favored candidate may omit an axis that makes a control appear less
complete.

## 10. Research-stage conclusion

The evidence motivates a high-priority test of a family-indexed native Analysis
calculus with federated checked bases, followed by a capability-checked hybrid
Compiler with open producers and exact finite-domain decisions. This is one
well-supported research hypothesis, not a comparative ranking or the Stage 4A
decision. Its total trusted base, correspondence burden, failure containment,
and authority-laundering risk remain unresolved until candidates are
instantiated and validated at equal resolution.

The candidate portfolio must still compare it at equal resolution with:

- preservation of the current Soundness-centered checked-search model;
- completion and alignment of that model without structural redesign;
- a universal proof/certificate-centered architecture; and
- a capability-expanding architecture that admits incomplete search and
  symbolic coverage without weakening semantic claims.

Selection follows only after integrated scenarios, matrices, producer and
consumer reviews, and reversal-trigger analysis.
