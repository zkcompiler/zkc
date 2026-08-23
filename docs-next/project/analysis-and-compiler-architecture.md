# Analysis and Compiler architecture

> **Document kind:** Architecture decision
> **Document state:** Active
> **Target decision status:** Selected Stage 4A target
> **Provisional owner:** `project`
> **Authority:** Non-normative target architecture for `docs-next/`. The
> current specifications under [`docs/`](../../docs/README.md) remain
> authoritative until normative consolidation, review, and explicit cutover.
> This decision does not establish a property, compiler result, implementation,
> migration, or Stage 4B activation.
> **Frozen research basis:** integrated target SHA-256
> `7729b1043e6f3ca1e77ce617327e3e9a959b8442f54da61a9e21ab9cb4fbabf3`;
> equal-resolution candidate portfolio SHA-256
> `a65bb0a9bbe49962377a28571874ba6f86a52e3f8c66a9ce766f36fa5a25cc61`.

## 1. Decision

Select a **federated typed Analysis architecture followed by a validated-
decision Protocol Compiler**.

Analysis shares a small lifecycle, identity, dependency, authority, outcome,
and replay discipline across semantic families. It does not force equality,
trace refinement, probabilistic distance, cryptographic security, cost, and
property transport into one universal proposition payload. Each family owns
its exact subjects, model, experiment, observer, proposition, negative meaning,
quantitative algebra, admissible bases, and inference rules.

Compiler consumes those exact results through five authority-separated planes:

```text
problem
  exact transition meaning + exact comparison policy

production
  replaceable, mutable, heuristic, parallel, or proof-producing search

proposal resolution
  one frozen pre-admission scope + one total alternative-resolution ledger

qualification and assessment
  PIR admission + exact transition checks + policy-local legality
  + exact Analysis/peer inputs + typed constraints and objectives

decision
  closed candidate and comparison domains + complete ledgers
    -> bounded best, complete Pareto frontier, or no-eligible result
  checked DecisionPolicy + any exact reached qualified subset
    + exact reached closure results actually read + audit-relative accounting
    -> explicitly open report
  preparation or checking failure -> outer outcome
```

These planes partition semantic ownership; they are not a temporal pipeline.
In particular, the scope freezes first, each declared alternative then reaches
its PIR admission and transition-qualification terminal, and only then is the
total alternative-resolution ledger finalized.

The resulting end-to-end topology is:

```text
admitted Stage 3 subjects and owner-created views
  + family semantic profile and exact model
  + typed hypotheses
  + direct, internal, external, certificate, or Evidence-derived basis
  -> independently checked family proposition
  -> qualified Analysis judgment

admitted predecessor + TransformProblem + DecisionPolicy
  -> unauthoritative search and proposals
  -> frozen ProposalScope
  -> per-alternative PIR-owned target authentication/admission
     + independently owned transition qualification
  -> total resolution of every declared alternative
  -> semantic CandidateDomain
  -> total qualification resolution
  -> policy-derived ComparisonAlternativeDomain
  -> total assessment accounting
  -> checked decision-sufficiency closure
  -> branchwise decision derivation:
       deterministic comparison for CompleteAssessment, or
       exact certified-payload extraction and permitted representative/
       totalization for ExternalCertificate
  -> QualifiedCompilerDecision

independent open-report side exit after checked DecisionPolicy
  + any exact reached qualified subset
  + every exact reached closure result the report actually reads
  + audit/not-attempted/blocker accounting for every claimed slot
  -> NonDecisionReport

preparation or checking failure at any reached operation
  -> OuterCompilerOutcome
```

The open-report side exit does not require `CandidateDomain`,
`ComparisonAlternativeDomain`, total qualification resolution, a total
`AssessmentLedger`, or decision sufficiency. It establishes only its exact
reached subset and audit-record-relative accounting statement. Those closure
objects are mandatory only for the closed-decision branch.

MLIR remains a first-class implementation and transformation substrate, but it
is not Analysis logic or Compiler decision authority. MLIR passes, transform
dialects, e-graphs, solvers, superoptimizers, learned systems, and manual edits
may all propose targets. The same target admission, relation, assessment, and
decision contracts apply to each producer.

## 2. Analysis semantic structure

### 2.1 Question, goal, proposition, and request

The target separates four identities that are easy to conflate:

| Identity | Meaning | Excludes |
|---|---|---|
| `AnalysisQuestionId` | One stable family experiment over exact subjects, model, observer, occurrences, maps, parameters, and semantic reads | Particular answer, residual hypotheses, theorem, proof, checker, or search limits |
| `AnalysisGoalId` | One exact hypothesis-free family conclusion for that question | Truth authority and residual hypotheses |
| `AnalysisPropositionId` | One truth-apt conclusion under one canonical typed hypothesis context | Proof technology, checker, producer, or replay occurrence |
| `AnalysisRequestId` | One operational attempt or derive-within request | Semantic truth and live authority |

A different bound or residual hypothesis is a different proposition. Several
proofs, checkers, or assurance classes may establish the same proposition.
Failure to find a proof establishes nothing unless an exact complete procedure
returns the family's exact semantic negative.

Request realization is deliberately two-phase. Before execution, Analysis
closes every input association and either reserves the exact admitted
proposition or only a `DeriveWithin` result schema; the latter cannot depend on
its future output. After execution, Analysis admits any produced proposition,
checks target/schema realization, achieved assurance, and total resource
accounting, then seals that completed realization into the checked-result
origin. Operational request and counter data do not change proposition or
semantic judgment identity. The request itself contains only inert values,
bindings, view contracts/references, and read-closure coordinates; all live
authority and concrete view occurrences are supplied and matched separately. A
capability-neutral outer attempt envelope also makes missing or malformed
request and invocation slots representable. Only successful preparation of the
complete typed invocation can enter semantic checking or return `Completed`.

The total-ingress rule is owner-wide at this seam. Analysis, Compiler, and
Relations checked operations first receive a capability-neutral partial input
whose owner-selected entry point fixes the complete slot schema. Missing,
candidate, prohibited, and opaque-malformed slots therefore have exact
nonauthoritative U/C/R/M/F branches before a fully typed call exists; only
`Ready` may execute the semantic signature. Fresh authority is supplied
separately. Attempt records establish only their bounded record-relative
accounting, default owner-local whenever the governing consumer, purpose,
policy, or disclosure permission is unavailable, and never authenticate an
operation or history occurrence.

### 2.2 Four independently versioned family profiles

Each Analysis family closes four different surfaces:

```text
FamilySemanticProfile
  subjects, views-as-fact-contracts, model, experiment, observer,
  proposition/result/refutation meaning, quantities, semantic reads

FamilyBasisRegistry
  native rules, theorem schemas, correspondences, transports,
  composition ports, certificate semantic languages

FamilyValidationProfile
  checker contracts, decoders, translations, proof rules,
  validation trust-root policy

FamilyOperationPolicy
  capability, disclosure, unknown-question, persistence, and replay rules
```

Only the semantic profile enters question identity. Adding a proof producer,
checker implementation, theorem instance, replay consumer, or adequate adapter
does not silently change an existing proposition. A change to model,
experiment, observer, conclusion, refutation, or semantic read does.

### 2.3 Capability-neutral source bindings

Every semantic-owner capability consumed across the Analysis or Compiler
boundary is accompanied by one exact inert source binding:

```text
OwnerCapabilityRequirement {
  exact owner capability-contract identity,
  exact capability ABI,
  exact operand/result binding schema,
  freshness and authority-lifetime requirements
}

ExactSourceAuthorityBinding<Owner, CapabilityFamily> {
  exact owner domain and capability family,
  semantic_coordinate:
      Portable(exact owner-defined canonical subject/admission coordinate
               or domain-separated result-record identity)
    | OwnerLocal(exact owner-defined subject/view or premise/result-record
                 reference),
  complete owner result-origin coordinates required by the capability ABI,
  exact admitted-subject facts or completed qualified outcome, polarity when
    applicable, and semantic facts,
  exact qualification, assurance, and residual-trust coordinates,
  exact authenticated OwnerOperationPolicyDisposition,
  exact transitive source-operation-policy dependency closure,
  exact OwnerCapabilityRequirement
}

ExactAdmittedSubjectAuthorityBinding<Owner, SubjectFamily> =
  ExactSourceAuthorityBinding whose semantic coordinate is an exact admitted
  subject/regime coordinate

ExactCheckedResultAuthorityBinding<Owner, ResultFamily> =
  ExactSourceAuthorityBinding whose semantic coordinate is an exact checked-
  result record identity or owner-local premise/result-record reference
```

`OwnerCapabilityRequirement` contains no capability token, occurrence identity,
or authority. It describes what a separately supplied fresh capability must
match. The source owner constructs the binding as part of the same completed
operation that mints the capability, and the capability retains that exact
binding. A consumer cannot manufacture, weaken, or reinterpret it.

The portable coordinate may be an owner's canonical admitted-subject/regime
coordinate; admission does not need a portable receipt. A checked result uses
a domain-separated owner result-record identity when its complete preimage is
portable and policy permits the intended use. Its family may define A/N or
another closed qualified outcome algebra. A confidential, nonserializable,
or otherwise owner-local result uses a collision-free owner-local record
reference instead. Any identity preimage that names the local branch becomes
local; the portable branch remains inert and grants no authority. In either
case, omission of owner policy is illegal: the binding contains either
`BoundTo(exact authenticated policy contract)` or
`OwnerDefinesNoOperationPolicy(exact owner capability contract and ABI that
declare that fact)`.

Checking receives the binding and actual fresh capability separately, requires
complete field equality, and freshly validates the bound-policy or explicit
no-policy branch for the named consumer and purpose. This shared envelope lets
Analysis and Compiler consume PIR admission, structural checks, Relations
results, Analysis judgments, and later peer-owner facts without treating live
authority as identity or inventing consumer-owned semantic receipts.

### 2.4 Basis, support, validation, and trust

`SemanticBasisId` identifies inference meaning: exact rules or theorems,
correspondence propositions, encodings, premise proposition schemas,
substitutions, quantitative transformers, and a total dependency-disposition
ledger. Every imported truth-apt dependency is one of:

- an exact established premise;
- an exact residual hypothesis inherited by the conclusion; or
- an exact definitional or logic-adequacy trust root.

There is no generic import or axiom bucket. In the portable lane, concrete
exact `ExactSourceAuthorityBinding` values and their inert
`OwnerCapabilityRequirement` values belong to `SupportInstantiationId`, not
semantic-basis or proposition identity. When a support preimage names an
owner-local source coordinate, Analysis instead uses
`LocalSupportInstantiationHandle` and
every later value whose own preimage names that handle is local. Taint propagates
only forward: an independent public question, proposition, semantic basis, or
validation basis remains portable. No affected local chain has a public digest,
persistence, or exact cold replay. Fresh matching capabilities remain
occurrence-local checking inputs and never enter either identity form. Checker
contracts, exact `CheckerAbiId` values, stable implementations, and checked
implementation-to-contract correspondence identities belong to
`ValidationBasisId`; fresh checker execution authority remains occurrence
local. Consumer-visible assurance and residual trust remain explicit in the
basis qualification and completed judgment.

This separation permits native derivations, complete direct checks, checked
external proofs, checked certificates, and carefully defined Evidence-derived
inferences to establish one semantic proposition without pretending that their
trusted computing bases are equal.

### 2.5 Qualified outcomes and authority

Only a successful current check mints a process-local capability for one exact
proposition, polarity, family result, assurance class, trust closure,
`FamilyOperationPolicyId`, complete transitive source-operation-policy
dependency closure, and completed `ExactJudgmentBinding` down to record or local
reference, derivation, support, semantic-basis, and validation-basis
coordinates, together with the exact
`ExactCheckedResultAuthorityBinding<Analysis, F>`. That result binding carries
the owner-defined result record or local reference, complete origin and
completed-outcome facts, qualification and trust, owner-policy disposition and
transitive source-policy closure, and inert `OwnerCapabilityRequirement`. It is
constructed atomically with the live capability, which retains the complete
binding. The target family policy and every bound source policy must permit the
exact named consumer and purpose. Records, theorem names, proof files, solver
responses, certificates, signatures, and replay bundles carry no authority.

Every operation preserves:

```text
Completed(FamilyAffirmative | FamilyNegative)
Unsupported
CannotAnswer
Refused
Malformed
CheckerFailure
```

A family negative exists only when that family defines an exact refutation or
complete decision relation. It binds the proposition answered, exact counter-
proposition, refutation relation, scope, and retained facts. An invalid proof
is normally negative only for `ProofValid`; it is not the negation of the
proposition the proof attempted to establish.

## 3. Analysis family boundaries

### 3.1 Structural and behavioral families

Core equality, Protocol equality, observer-indexed trace equality, directed
trace refinement, intentional change, distributional relations, and cost
relations remain separate families. Their exact maps, directions, observers,
models, occurrences, schedulers, abort/termination rules, and quantitative
coordinates enter the corresponding question rather than ambient metadata.

An admitted intentional-change contract is not proof that a change conforms.
`ChangeConforms` is a separate checked proposition. A structural relation does
not imply property preservation without an exact family rule.

### 3.2 Cryptographic families

Soundness, knowledge, completeness, zero knowledge, and any later property are
not tags on one scalar result. Each family states its experiment, adversary or
simulator/extractor interface, occurrence and oracle model, query and resource
bounds, abort/retry/termination semantics, assumptions, conclusion, and
quantitative loss algebra.

Fiat--Shamir is factored into:

1. Stage 3 structural Fresh-to-Fiat--Shamir construction;
2. an Analysis-owned theorem/model applicability result over exact source,
   target, construction, correspondences, assumptions, and loss;
3. property-specific transport from exact source premises to one exact target
   property; and
4. direct target analysis as an independent basis when available.

No generic `FSCompile` or structural map transports all properties.

Composition follows the same rule. Structural Core composition is an input,
not a property theorem. Every property family supplies operator-specific rules
for sequential, parallel, interleaved, concurrent, shared-challenge, batched,
repeated, failure-capturing, or other exact compositions it supports.

### 3.3 Relation satisfaction

`RelationSatisfies` belongs to Relations because predicate truth for one exact
definition, instance, and witness is base relation semantics. Analysis may
consume its exact qualified result in completeness, knowledge, or other
questions, but cannot redefine satisfaction.

The witness remains an occurrence-local confidential capability. A public
record excludes witness bytes. A negative satisfaction result says only that
this exact witness occurrence fails this exact instance under the exact model;
it does not establish instance unsatisfiability or witness nonexistence.

## 4. Compiler semantic structure

### 4.1 Problem, policy, and operational search

`TransformProblemId` identifies transition meaning: admitted predecessors,
target admission regime, transform intent, requested relations and polarities,
permitted intentional changes, semantic-path policy, and map families.

`DecisionPolicyId` identifies comparison meaning: domain-formation schemas,
named Compiler consumer and typed purposes, accepted bases, authenticated owner-
policy-disposition acceptance schemas, transitive source-operation-policy-
closure acceptance rules, exact source-authority-binding and inert
`OwnerCapabilityRequirement` schemas, and trust acceptance; required owner
fact/value schemas;
qualification resolution; typed constraints and objectives;
comparator, Pareto/tie/representative rules; and requested closed-decision or
open-report strength. It contains no future candidate-specific fact; concrete
dispositions, closures, origins, and capability requirements enter only through
a candidate's qualification projection or assessment portfolio after
`CandidateId` exists. Policy absence is legal only when an exact authenticated
owner capability contract
declares it. Acceptance of a source operation policy does not rewrite that
policy or authorize a use it forbids.

`CompileRunRequestId`, `SearchJobId`, producer, recipe, seeds, workers,
timeouts, solver bounds, heuristics, and discovery order are operational. They
do not enter `CandidateId` or alter comparison or decision semantics. A
request-relative bounded decision or open report may nevertheless retain them
transitively through its exact frozen scope, provenance, and total-accounting
records. That retention authenticates only the bounded claim's exact inputs
and accounting--not that a search, failure, or run-history occurrence happened.
Actual execution history requires a separate owner-authenticated occurrence or
log result, which Stage 4A does not define.

All Compiler `*Id` spellings in the remainder of Section 4 describe the
portable lane. At every typed edge the durable Compiler model instead carries
an exact value with a disjoint coordinate:
`Portable(Id(value)) | OwnerLocal(LocalCompilerHandle<value, owner
generation>)`. If a value's identity-bearing preimage names any owner-local
child, no portable ID exists and the owner-local coordinate propagates through
every later scope, alternative, path, candidate, domain, ledger, assessment,
report, or decision whose own preimage names it. Canonical local collections
use only the same-owner, same-generation order. Portable closed claims, replay
bundles, persistent cache entries, and public disclosure require every such
coordinate to be portable; neither branch grants live authority.

### 4.2 Frozen proposal scope and total resolution

A producer emits unauthoritative material. One `ProposalScopeId` freezes a
canonical finite descriptor sequence or exact finite grammar before admission,
relation, constraint, or score outcomes are observed. Every
`DeclaredAlternativeId` is reconstructed cycle-free from that scope and its
canonical coordinate.

`AlternativeResolutionLedgerId` has exactly one entry for every declared
alternative:

```text
resolved to admitted relation-qualified CandidateIds
checked duplicate of an earlier alternative
conclusively excluded by an exact completed fact
unsupported | cannot answer | refused | malformed | checker failure
search or resolution incomplete
```

Unresolved outcomes cannot disappear from a closed originating-scope claim.
Total scope resolution also does not prove that a producer found every legal
transform unless an independent exact grammar or exploration coverage result
says so.

### 4.3 Admission, transition, and legality

Every proposed Protocol and every semantically asserted intermediate is
independently authenticated and admitted by PIR. Compiler cannot mint or
serialize `AdmittedProtocol` authority.

Each semantic path names admitted subjects, exact adjacent relation
propositions, maps, intentional-change contracts, and any requested end-to-end
relation. The owning Analysis, Relations, PIR, or bridge family defines and
checks each predicate. A lineage map is a witness to a relation, not the
relation itself.

`CompilerLegality` checks only exact `TransformProblem`-local restrictions,
such as permitted transform families, path shapes, multiplicity, and closed
parameter ranges. Basis, assurance, assumption, and trust acceptance belong to
policy assessment, not transition legality.

### 4.4 Semantic candidate and comparison domains

`CandidateId = TransformProblemId + TransitionCaseId`. It excludes producer,
recipe, search order, proposal ordinal, proof basis, assessment, and score. Two
semantically different paths remain different candidates unless an exact
checked quotient proves irrelevance to every declared consumer.

`CandidateDomainId` identifies only a canonical finite set of independently
admitted, relation-qualified candidates under one exact policy. Supported
forms include submitted sets, resolved submitted scopes, exact enumerated
closed domains, and certified symbolic domains. In v0, symbolic certificates
range only over an already materialized, PIR-admitted, transition-qualified
canonical `CandidateId` image. Certificates may compress closure, assessment,
infeasibility, or optimality checking; they cannot manufacture candidates or
replace admission.

For every candidate, Compiler first freezes an exact qualification-only input
projection containing every and only qualification record, complete owner
created typed source-authority-binding ledger for every admitted subject/view
and checked result read, source-policy closure, assurance/trust coordinate, and
inert `OwnerCapabilityRequirement` read by the
qualification policy. An occurrence-
local check establishes its candidate association, completeness, current
authority, and conjunctive policy permission. Qualification resolution then
derives a separate `ComparisonAlternativeDomainId`. Normally each candidate
maps to one exact accepted qualification or corroborating set. If basis trust is
explicitly an optimization dimension, it maps to every and only policy-accepted
candidate/qualification alternative. A total ledger accounts for every
candidate. An unrelated local assessment fact does not affect this projection,
resolution, or comparison domain; a local qualification input localizes only
the values whose preimages name its projection. The selected comparison
alternative projects back to exactly one semantic `CandidateId`.

### 4.5 Assessment and decision

`DecisionPolicy` declares required schemas. An immutable candidate-indexed
`AssessmentInputPortfolio` retains the exact candidate reference, including
its transition case and admitted target, and may later contain foreign admitted
subject or view values, foreign checked Analysis, Relations, Stage 4B, or
Evidence results, and Compiler-owned structural values or declared
preferences. It therefore retains one complete typed source ledger whose
entries distinguish admitted-subject
bindings from checked-result bindings, plus a separate exact ledger of every
complete Compiler-owned structural-value `CompilerCheckedResult`: its record
body, portable ID or owner-local coordinate, and exact owner-created output
binding. A declared preference instead retains the complete validated
`DecisionPolicy` result plus its exact policy coordinate; it is not a fabricated
preference-result family. Matching
fresh foreign capabilities are supplied separately. Every Compiler-owned input
is supplied through `CompilerResultUseAuthority`, which pairs its complete inert
result with a separately fresh matching capability and freshly authorizes the
new consumer and purpose; no capability is serialized into the portfolio.
In the fully portable lane the portfolio content ID excludes its own
completeness result; a portfolio whose own preimage names a local input uses a
nonpersistable `LocalCompilerHandle`. A separate check proves schema coverage,
uniqueness, candidate association, polarity, assurance, exact source-binding
equality, immediate and transitive source-operation-policy acceptance, inert
`OwnerCapabilityRequirement` values, complete Compiler result/output-binding
equality, and trust acceptance. Compiler-owned input-use edges bind independent
owner facts to one canonical typed slot in the exact portfolio and policy,
checking unique body membership plus candidate, target, and policy association
without ambient lookup or making those facts depend on a future assessment.

Constraints consume exact qualified facts. An affirmative premise requires an
affirmative capability; a negative may satisfy only an explicitly negative
constraint. Every complete owner-created checked-result authority binding,
matching inert `OwnerCapabilityRequirement`, authenticated immediate owner-
policy disposition, and transitive
source-policy closure is preserved. The Compiler policy and every bound owner
policy must permit this consumer and use. Unsupportedness, cannot-answer,
refusal, malformation, and checker failure satisfy neither polarity.

Objectives retain provenance and epistemic shape. Exact structural values,
model- or Evidence-derived Analysis values, Evidence-qualified estimates,
later Stage 4B values, and
declared policy preferences are not interchangeable. Exact values, one-sided
bounds, intervals, symbolic values, statistical estimates, and categorical
values compare only through an explicit typed rule. Missing is not infinity.

A closed decision binds both the semantic candidate domain and derived
comparison domain, their closure bases, complete resolution and total
assessment-accounting ledgers, an exact checked assessment-sufficiency basis
(policy-approved complete assessment or independently checked certificate),
comparator, tie policy, selected support, complete decisive owner
source-authority binding and transitive source-policy closures, and residual
trust. It may
establish only:

- bounded best in the exact closed domains;
- the complete Pareto frontier in those domains; or
- no eligible candidate in those domains, with a complete exact exclusion or
  infeasibility basis.

Feasible candidates, subset frontiers, best among completed assessments, and
incomplete progress are explicit non-decision reports. `Unsupported`,
`CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure` are outer outcomes
with exact nonauthoritative attempt audits but no checked result or capability.
An empty heuristic result is never no-eligible authority.

## 5. Authority and ownership map

| Concern | Semantic owner | Compiler role |
|---|---|---|
| Protocol target authentication and admission | PIR | Orchestrates, consumes the exact inert admitted-subject authority binding, and separately supplies the fresh admission capability |
| Equality, refinement, intentional change, property transport | Exact Analysis or bridge family | Requests and consumes; never defines or widens |
| Relation predicate satisfaction | Relations | Consumes exact qualified result when requested |
| Compiler-local transform restrictions | Compiler `TransformProblem` | Defines and checks |
| Basis/source-operation-policy/trust acceptance, constraints, objectives, comparison | Compiler `DecisionPolicy` | Defines and checks over exact owner inputs without rewriting owner policy |
| OIR, projection, realization, endpoint facts | Stage 4B owners | Consumes only exact named later-owned fact/value schemas |
| Raw measurements and observations | Exact producing semantic or operational domain | Never treats raw material as an Evidence record or qualified semantic input |
| Evidence records, `EvidenceQualifiedEstimate` values, and appraisals | Evidence | Consumes only an exact qualified record/value whose provenance, uncertainty, and epistemic shape remain explicit |
| Reliance for a release or use | Named later consumer | Not a Compiler decision |

No generic `verified` or `valid candidate` capability crosses these rows.

## 6. Alternative disposition

The selection compared five complete integrated models at the same semantic
resolution.

| Candidate | Disposition | Mechanism retained |
|---|---|---|
| Extended closed kernel and enumerated Compiler | Not selected as the center; a growing universal sum couples unrelated families and makes extension/replay global | Closed native rule bodies, exact arithmetic, explicit derivation DAGs, and no-search checking |
| Federated typed Analysis and validated-decision Compiler | **Selected** | Whole architecture |
| Universal Claim IR/proof graph | Not selected as semantic center; one global logic risks changing owner meanings and identity locality | Typed dependency/support DAG and replay visibility |
| External-proof-system-centered obligations | Not selected as primary authority; statement/model correspondence and external environment trust remain family-specific | Checked external statement, model, proof, and checker adapters |
| Certified relational synthesis and symbolic optimization | Not selected as a universal requirement; certificate languages do not cover every family and cannot bypass admission | Optional proof-carrying proposals, checked symbolic compression, synthesis, and anytime-report lanes |

The selected result is not a compromise average. It takes mechanisms only
where their authority and identity fit the federated model.

## 7. Why this architecture is preferred

The decision has five primary benefits.

1. **Semantic fidelity.** Family-specific models and negatives remain exact;
   shared infrastructure cannot erase observer, oracle, occurrence, abort,
   assumption, or quantitative meaning.
2. **Replaceable production.** New proof systems and optimizers can improve
   search without acquiring semantic authority or changing candidate identity.
3. **Auditable trust.** Proposition assumptions, semantic inference,
   validation machinery, concrete support, and consumer trust acceptance are
   independently visible.
4. **Honest partial progress.** Useful feasible candidates, partial frontiers,
   and incomplete proofs can be returned without laundering them into
   completeness, optimality, or semantic negatives.
5. **Composable downstream use.** Compiler can consume exact cryptographic,
   Evidence, and later endpoint facts while leaving their owner meaning and
   replay contracts intact.

This enables independent proof/checker lanes for one proposition, validation-
backed untrusted optimization, trust-sensitive comparison without changing
Protocol identity, property-specific Fiat--Shamir and composition reasoning,
and, in the fully portable lane, cold replay without rerunning nondeterministic
discovery. Cold replay re-admits the Compiler capability contract and result
operation policy, reconstructs a fresh result-minting authority for every
checked operation and a fresh result-use authority for every Compiler-owned
input, and accepts each recreated capability only after complete checked-result
and output-binding equality. A local confidential lane permits only a new owner-authorized same-
process rerun with fresh handles; it has no persistent identity or exact replay.

## 8. Costs and deliberate deferrals

The architecture deliberately accepts:

- more explicit identities, profiles, ledgers, and checked association edges;
- family-by-family semantic and negative-result design instead of a one-record
  calculus;
- explicit trust accounting for external proof environments and certificate
  checkers;
- two closed Compiler domains where qualification choice affects comparison;
- bounded rather than global optimality claims; and
- recomputation or, for fully portable values, complete cold replay rather than
  serialized authority; local values require a fresh confidential rerun.

It defers concrete proof languages, checker implementations, certificate
formats, solver choices, optimizer algorithms, transform families, canonical
wire encodings, implementation organization, and migration. A stronger lazy
symbolic domain over unnamed or unadmitted Protocols is also deferred because
it would reopen the Stage 3 admission boundary.

## 9. Stage 4B, Evidence, and reliance firewall

Stage 4B remains unactivated. OIR validity, projection correctness,
realization, supplier binding, endpoint feasibility, deployment, invocation,
and runtime results are not inferred from Analysis or Compiler output.

A later-owned fact enters Stage 4A only through an exact subject tuple,
qualified result and polarity, model/checker basis, maps and reads, and complete
`ExactCheckedResultAuthorityBinding`, including its owner origin coordinates,
inert `OwnerCapabilityRequirement`, authenticated owner-policy disposition,
total transitive source-policy dependency closure, and residual trust. Policy
absence requires an exact
owner capability contract that declares it. The independent fact never names a
future Compiler assessment; Compiler checks a separate association edge and the
conjunction of every bound source policy. If a policy does not name such a fact,
Compiler behavior is invariant under it. If the policy requires it and it is
unavailable, the assessment is undetermined, unsupported, or refused rather
than silently rejected.

Projection and Realization semantics are invariant under producer, proposal,
search path, domain, score, or selection history when their own explicit inputs
are unchanged. A same-process Compiler result may return a separately PIR-
owned admitted target capability alongside the decision, but neither authority
casts to the other.

A portable Compiler decision transitively identifies its selected candidate but
contains no target carrier or PIR reconstruction manifest. Cold selected-target
handoff therefore requires a separate portable
`CompilerSelectedTargetHandoffBundle<D,Q>` authorized for the exact Stage 4B consumer
and typed handoff purpose. It retains the canonical target carrier and complete
PIR reconstruction material plus the exact decision-to-candidate equality path;
decision replay permission does not imply handoff permission. Stage 4B must
still reauthenticate and independently readmit the Protocol, and a local
dependency or policy denial means no cold handoff exists.

The producing domain owns what a raw observation or measurement means and its
completeness frontier. Evidence owns the bridge that turns that exact material,
with procedure, environment, samples, uncertainty, and receipts, into an
attributable record and optionally a policy-qualified appraisal or
`EvidenceQualifiedEstimate`. Analysis owns any exact inference from Evidence to
a semantic proposition, including `AnalysisEvidenceDerivedEstimate`. These two
estimate types are not interchangeable. Compiler owns only an explicit
comparison policy over qualified facts or values. A relying
consumer separately decides sufficiency for use.

## 10. Current correspondence and limits

The current Soundness Kernel contributes strong closed rules, explicit
assumptions, exact bound arithmetic, checked derivation plans, and refusal
discipline. The target generalizes those mechanisms without claiming that the
current kernel implements the federated family profiles, proposition/basis
split, external correspondence lanes, or complete replay model.

The current Compiler contributes proposal-versus-decision separation,
canonical finite provider domains, exact plan realization, independent
decision recomputation, typed soundness-derived constraints, deterministic
selection, and explicit bounded-optimality language. The target does not claim
that the current implementation realizes frozen proposal scopes, total
alternative resolution, independent target admission after proposal,
qualified relation cases, persistent identities, comparison-alternative
domains, full outcome separation, or cold replay.

This page establishes no theorem, property, checker correctness, compiler
correctness, domain completeness, implementation correspondence, migration
feasibility, compatibility, performance, endpoint support, or release result.

## 11. Evolution and reversal conditions

The semantic surface is closed by exact family and Compiler policy profiles;
production is replaceable. Unknown meaning-bearing tags are `Unsupported`.
Dynamic registration cannot create semantic authority.

Reconsider the selected center only if independently reviewed evidence shows:

1. a genuinely small universal logic covers every selected family without
   hiding model, observer, adversary, oracle, occurrence, abort, quantitative,
   negative, or trust semantics;
2. one external environment supplies every required native question with
   fully checked correspondence and stable replay;
3. certificate systems cover the complete required surface more simply while
   retaining honest unsupported families and direct checks;
4. cross-family inference dominates family-local semantics enough that
   federation creates more ambiguity than it removes;
5. a real transform cannot fit the five Compiler planes without restoring
   producer authority or an uncheckable domain;
6. a required consumer cannot separate semantic candidate identity from proof
   basis even with an explicit qualified comparison domain; or
7. Stage 4B exposes a concrete shared read-set or identity contradiction that
   cannot be represented as an exact later-owned input.

An implementation inconvenience, optional checker absence, or slow search is
not by itself a semantic reversal trigger.

## 12. Durable semantic owners and next boundary

The exact target is split by meaning:

- [Canonical PIR](../pir/canonical-pir.md), [Protocol semantic
  model](../pir/protocol-model.md), [Interfaces and Prover
  Plans](../pir/interfaces-and-plans.md), and [Fiat--Shamir construction and
  semantic Core composition](../pir/fiat-shamir-and-composition.md) own the
  PIR-specific admitted-subject/checked-result binding, qualified-outcome, and
  total source-policy-closure specializations consumed by Stage 4A;
- [Analysis model](../analysis/analysis-model.md) owns the common semantic and
  authority envelope;
- [semantic relations](../analysis/semantic-relations.md) owns equality,
  refinement, change, distribution, cost, and the satisfaction seam;
- [cryptographic properties](../analysis/cryptographic-properties.md) owns
  notion-specific property and Fiat--Shamir reasoning;
- [transport, composition, and replay](../analysis/transport-composition-and-replay.md)
  owns cross-family derivation, persistence, and extension rules;
- [Compiler model](../compiler/compiler-model.md) owns the five-plane frame;
- [proposals, relations, and domains](../compiler/proposals-relations-and-domains.md)
  owns scope, admission, transition, candidate, and closure semantics;
- [assessment, selection, and replay](../compiler/assessment-selection-and-replay.md)
  owns policy inputs, comparison domains, decisions, and persistence;
- [Relation model](../relations/relation-model.md) owns exact relation
  satisfaction; and
- [Protocol correspondence](../relations/protocol-correspondence.md) owns the
  reconciled structural/instance result bindings and preserves the boundary to
  Analysis property transport.

The next unactivated branch remains Stage 4B: OIR, then Realization. A later
cross-branch checkpoint must reconcile shared observations, occurrence maps,
failure and terminal semantics, Plan reads, property versus projection claims,
and explicit endpoint facts without merging the two authority graphs.
