# Compiler proposals, relations, and candidate domains

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Selected Stage 4A Compiler target; durable promotion
> **Provisional owner:** `compiler`
> **Authority:** This document specifies the selected Compiler target for
> `docs-next/`. It is non-normative until explicit consolidation, review, and
> cutover. The current specifications under
> [`docs/`](../../docs/README.md), including the current
> [Compiler Core specification](../../docs/spec/compiler.md), remain
> authoritative. This document makes no implementation, migration,
> compatibility, cryptographic-security, endpoint-feasibility, or global-
> optimality claim.
> **Frozen target basis:** SHA-256
> `7729b1043e6f3ca1e77ce617327e3e9a959b8442f54da61a9e21ab9cb4fbabf3`

## 1. Scope

This document defines the target boundary from replaceable search through one
exact semantic `CandidateDomain`:

~~~text
TransformProblem
  -> ExplorationSpace and unauthoritative production
  -> cycle-free frozen ProposalScope
  -> PIR-owned target and intermediate admission
  -> exact transition and lineage qualification
  -> CandidateIds and total AlternativeResolution ledger
  -> exact CandidateDomain closure
~~~

For each `CandidateId`, problem-local `CompilerLegality` is a separate
assessment input; it does not change proposal resolution or domain membership.

The overall owner and authority model is specified in
[Compiler model](compiler-model.md). Qualification-use, comparison-alternative,
assessment, selection, and replay semantics are specified in
[Assessment, selection, and replay](assessment-selection-and-replay.md).

This page never treats a plan, recipe, proposal, raw carrier, lineage claim,
certificate, score, or provider result as a semantic candidate.

## 2. Exploration and production

### 2.1 `ExplorationSpace`

`ExplorationSpace` describes possible operational work:

~~~text
ExplorationSpace {
  transform_problem_coordinate: CompilerValueCoordinate<TransformProblem>,
  exact plan or recipe grammar when declared,
  exact numeric and structural bounds when declared,
  producer and search configuration,
  heuristic and pruning configuration,
  resource and interruption policy,
  exact operational read set
}
~~~

It may be finite or open. Its operational state may change as search proceeds.
Unless a separately checked exact coverage result says otherwise, it makes no
claim that every legal transform, target, path, or candidate was explored.

MLIR transforms, e-graphs, superoptimizers, solvers, verified rewriters,
learned systems, and manual authoring are all possible producers. Their output
enters the same unauthoritative proposal boundary. A verified producer may
offer a stronger proof basis, but producer execution itself does not mint PIR
admission or transition authority.

### 2.2 Recipes and materialized proposals

`ProposalRecipe` is an operational method. It may describe matching,
rewriting, synthesis, derivation, or construction. A recipe must materialize
exact carrier data before semantic processing; cold semantic replay never
depends on reproducing mutable producer behavior.

~~~text
ProposalOccurrence {
  compile_run_request_coordinate: CompilerValueCoordinate<CompileRunRequest>,
  exact SearchJobOccurrenceRef,
  exact proposed final carrier material,
  exact proposed semantic-intermediate carrier material,
  unauthoritative typed lineage and occurrence maps,
  unauthoritative relation, proof, and certificate material,
  exact producer and recipe provenance
}

ProposalOccurrenceRef = ExactCompilerValueRef<ProposalOccurrence>
~~~

`ProposalOccurrenceId` is an operational and replay identity. Two producer
occurrences may resolve to the same semantic candidate. Equal proposal bytes
do not establish admission or relation truth.

A raw occurrence may be recorded without semantic authority, but a request-
derived occurrence cannot enter a frozen scope or request-relative report from
its `compile_run_request_coordinate` alone:

~~~text
CheckProposalOccurrenceUse(
  exact ProposalOccurrenceRef,
  exact ExactCompilerValueRef<CompileRunRequest> and exact CompilerResultUseAuthority<
    CheckedCompileRunRequest, CompileRunRequestValidationRecord>,
  exact ExactCompilerValueRef<TransformProblem> and exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact occurrence-to-request/job association and accepted operational limits,
  exact NamedConsumer and typed proposal-occurrence-use purpose,
  fresh reauthorization of every inherited source-policy disposition)
  -> CompilerValidationAttemptOutcome<
       CheckedProposalOccurrenceUse,
       exact inert ProposalOccurrenceUseRecord>

ProposalOccurrenceUseRecord {
  exact ProposalOccurrenceRef,
  exact ExactCompilerValueRef<CompileRunRequest> and
    CompileRunRequestValidationResult,
  exact ExactCompilerValueRef<TransformProblem> and
    TransformProblemValidationResult,
  exact occurrence-to-request/job association and accepted operational limits,
  exact capability-neutral request/problem input-use authorization coordinates,
  exact NamedConsumer and typed proposal-occurrence-use purpose,
  exact inherited source-policy closure and freshly checked policy/contract
    authorization records,
  exact validation contract, output-minting contract/result-policy coordinates,
    and residual trust
}
~~~

`ProposalOccurrenceUseResult` is the complete
`CompilerCheckedResult<CheckedProposalOccurrenceUse,
ProposalOccurrenceUseRecord>` returned by `Completed`.

The record binds the exact occurrence, request, job occurrence, problem, full
`CompileRunRequestValidationResult` and `TransformProblemValidationResult`,
their capability-neutral input-use authorization coordinates, and accepted
purpose; it contains no capability. Only `Completed` supplies the fresh use
capability. A scope-freezing operation that includes an
`ExactProposalOccurrence` descriptor receives the matching complete checked
result through `CompilerResultUseAuthority`. A directly submitted transition
or finite grammar scope may omit a run request, but scope freezing still
receives the exact `TransformProblem` and its complete result-use authority.
Thus an unauthenticated producer may propose bytes, while an invalid request
cannot authorize scope membership.

The job-occurrence coordinate is the exact capability-neutral
`SearchJobOccurrenceRef` from the Compiler model. The use checker verifies only
its descriptor, request/job association, producer namespace, and any explicitly
claimed bounded-progress scope. It never establishes that an execution or
emission occurred; that would require a separately owner-authenticated
occurrence/log result outside Stage 4A.

## 3. Frozen proposal scope and declared alternatives

### 3.1 Cycle-free `ProposalScope`

A proposal scope used by a scoped resolution or decision claim is finite,
canonical, immutable, and cycle-free:

~~~text
ProposalMemberDescriptor =
    ExactProposalOccurrence(exact ProposalOccurrenceRef,
                            exact ProposalOccurrenceUseRecord)
  | ExactSubmittedTransitionMaterial(exact source, target, path, and maps)
  | ExactFiniteGrammarMember(exact grammar coordinate and materialization input)

ProposalScope {
  transform_problem_coordinate: CompilerValueCoordinate<TransformProblem>,
  scope_kind,
  exact canonical finite member-descriptor sequence
    or exact finite grammar with canonical bounds and member order,
  exact multiplicity and pre-admission duplicate policy,
  exact freeze rule
}
~~~

Its identity is constructed without any identity that is derived from it:

~~~text
ProposalScopeId = Id(exact ProposalScope)
~~~

The descriptor sequence or finite grammar is frozen before target admission,
transition checking, qualification use, constraints, or objectives are
observed. A finite grammar expands deterministically to the same ordered
descriptor sequence before any semantic result is read. A heuristic discovery
stream that cannot supply such a frozen finite sequence or grammar is
`OpenExploration`, not a closed proposal scope.

### 3.2 `DeclaredAlternativeId`

~~~text
DeclaredAlternative {
  proposal_scope_coordinate: CompilerValueCoordinate<ProposalScope>,
  canonical member coordinate,
  exact ProposalMemberDescriptor
}

DeclaredAlternativeId = Id(exact DeclaredAlternative)
~~~

`DeclaredAlternativeId` is domain-separated from proposal, target,
transition, and candidate identities. An alternative is an obligation to
resolve one exact frozen entry; it is not evidence that a candidate exists.

The scope preimage contains descriptors, not `DeclaredAlternativeId` values,
while each alternative identity contains the already fixed `ProposalScopeId`.
This orientation has no identity cycle. Result fields are absent from both
preimages and appear only in the later resolution ledger; membership cannot be
enlarged, removed, or reordered after semantic checking begins.

## 4. Total alternative resolution

Every declared alternative receives exactly one resolution result:

~~~text
AlternativeResolutionBlocker =
    CompilerOuterAttempt(
      exists exact T and R: exact CompilerAttemptAudit<T,R> whose operation
        association names this CompilerValueCoordinate<DeclaredAlternative>)
  | ForeignOwnerAttempt(
      exists exact Owner and AttemptFamily: exact typed capability-neutral
        owner attempt/non-result record, every available authenticated owner
        contract/policy disposition or exact missing/malformed requirement,
        and exact CompilerValueCoordinate<DeclaredAlternative> association;
        no checked-result binding or live capability)
  | NotAttempted(exact CompilerValueCoordinate<DeclaredAlternative> and exact
                 request- or policy-defined nonsemantic scheduling reason)
  | SearchIncomplete(exact CompilerValueCoordinate<DeclaredAlternative>,
                     frozen run/request progress,
                     interruption or unproved-pruning reason)

AlternativeResolution =
    ResolvedTo(CanonicalNonEmptySet<CompilerValueCoordinate<Candidate>>)
  | DuplicateOf(exact CompilerValueCoordinate<DeclaredAlternative> for the
                earlier alternative,
                exact CompilerValueCoordinate<CandidateQuotient> and
                CandidateQuotientCheckResult,
                CanonicalNonEmptySet<CompilerValueCoordinate<Candidate>>)
  | ConclusivelyExcluded(exact owner-completed admission or transition fact
      records and complete CanonicalTypedLedger<
        exists exact Owner and ResultFamily:
          ExactOwnerResultBinding<Owner, ResultFamily>>)
  | Unresolved(exact AlternativeResolutionBlocker)

AlternativeResolutionEntry {
  exact declared_alternative_coordinate:
    CompilerValueCoordinate<DeclaredAlternative>,
  outcome: AlternativeResolution,
  exact inert owner fact records actually read by that outcome,
  exact CandidateQualificationResult values for every resolved
    CompilerValueCoordinate<Candidate>,
  exact nonauthoritative blocker and attempt association for Unresolved,
  exact complete ExactSourceAuthorityBindingLedger for every authority-bearing
    source actually read,
  exact source-to-outcome association and total transitive source-policy closure
}

AlternativeResolutionLedger {
  exact proposal_scope_coordinate: CompilerValueCoordinate<ProposalScope>,
  exactly one complete AlternativeResolutionEntry for every and only
    CompilerValueCoordinate<DeclaredAlternative> in canonical scope order,
  exact complete source-to-entry association and canonical transitive source-
    policy closure,
  no live capability
}

AlternativeResolutionLedgerId = Id(exact AlternativeResolutionLedger)
~~~

`AlternativeResolutionLedgerId` binds every and only
`DeclaredAlternativeId` to one complete `AlternativeResolutionEntry` in
canonical order and content-identifies the complete entries, not only their
outcome tags. The result ledger is
total as a record even when some entries are unresolved semantically. Every
owner-fact-backed resolved, duplicate, or excluded entry retains its exact inert
owner result records and complete `ExactSourceAuthorityBindingLedger`, including
every admitted-subject coordinate, checked-result coordinate, authenticated
`OwnerOperationPolicyDisposition`, transitive source-policy dependency closure,
complete owner origin binding, and inert `OwnerCapabilityRequirement`. The
ledger contains no live capability.

`ResolvedTo` is available only after every named target and semantic
intermediate is admitted, every required transition is affirmative, and the
resulting candidate identities are authenticated. `DuplicateOf` requires an
exact checked quotient; target-ID equality or provider assertion is
insufficient.

`ConclusivelyExcluded` is permitted only when exact owner-completed facts and
the frozen scope semantics establish that the alternative maps to no candidate,
every exact authenticated owner-policy disposition remains valid, and each
bound immediate or transitive owner operation policy permits this resolution
and scope-closure use. A mismatched, unaccepted, or prohibiting policy yields
`Unresolved` with the exact typed refusal or other blocker; it never becomes
conclusive exclusion. Compiler or foreign-owner unsupportedness, cannot-answer,
refusal, malformation, checker failure, nonattempt, and interruption remain
nonauthoritative blocker branches and do not become conclusive exclusion merely
because no candidate was produced.

`AlternativeResolutionCoverage` establishes:

- exact ledger totality over its frozen `ProposalScopeId`;
- exact authentication of every resolution entry;
- exact canonical image in semantic `CandidateId` values;
- exact duplicate and quotient treatment; and
- every unresolved entry that prevents a closed originating-scope claim.

The check has an explicit inert result rather than minting an unnamed
capability:

~~~text
AlternativeResolutionCoverageRecord {
  exact ProposalScopeId and AlternativeResolutionLedgerId,
  exact CandidateDomainPolicy and CandidateDomainPolicyId,
  exact CandidateDomainPolicyValidationResult,
  exact total declared-alternative coverage and canonical CandidateId image,
  exact duplicate-to-quotient associations, CandidateQuotientIds, and
    CandidateQuotientCheckResults,
  exact unresolved blockers,
  exact ProposalOccurrenceUseResults and scope-member associations for every
    request-derived descriptor,
  exact inert owner fact and exclusion records plus complete
    CandidateQualificationResult and CandidateQuotientCheckResult values
    actually read,
  exact AlternativeResolutionBlocker and association for every Unresolved
    entry, with no result-use authority or semantic polarity inferred from it,
  exact complete ExactSourceAuthorityBindingLedger and source-to-entry map,
  exact named consumer and typed alternative-resolution-coverage purpose,
  exact total transitive source-policy closure and freshly checked
    policy/contract authorization set,
  exact Compiler semantic regime, validation contract, and residual trust
}

AlternativeResolutionCoverageRecordId =
  Id(exact AlternativeResolutionCoverageRecord)

AlternativeResolutionCoverageRecordResult =
  CompilerCheckedResult<
    AlternativeResolutionCoverage, AlternativeResolutionCoverageRecord>

CheckAlternativeResolutionCoverage(
  exact ProposalScope and ProposalScopeId,
  exact AlternativeResolutionLedger and AlternativeResolutionLedgerId,
  exact CandidateDomainPolicy and CandidateDomainPolicyId,
  exact CompilerResultUseAuthority<
    CheckedCandidateDomainPolicy, CandidateDomainPolicyValidationRecord>,
  one exact CompilerResultUseAuthority<
    CheckedProposalOccurrenceUse, ProposalOccurrenceUseRecord> for every
    request-derived scope descriptor,
  exact inert owner fact and exclusion records named by the ledger,
  one exact CompilerResultUseAuthority<
    QualifiedCandidate, CandidateQualificationRecord> for every resolved
    CandidateId,
  every separately supplied fresh matching foreign owner-result and exclusion
    capability required by resolved, duplicate, or excluded entries,
  every exact CandidateQuotient named by a duplicate or quotient-backed entry
    and one exact CompilerResultUseAuthority<
      CheckedCandidateQuotient<CandidateQuotientId>,
      CandidateQuotientCheckRecord> for each,
  exact AlternativeResolutionBlocker for every Unresolved entry; a Compiler
    attempt audit is checked only for canonical integrity and exact operation/
    alternative association, a foreign attempt is checked only under its exact
    owner audit contract, and `NotAttempted`/`SearchIncomplete` is checked only
    as scope-bound nonsemantic bookkeeping,
  exact complete ExactSourceAuthorityBindingLedger and source-to-entry map,
  exact NamedConsumer and typed alternative-resolution-coverage purpose,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose,
  exact Compiler semantic regime and coverage-validation contract)
  -> CompilerValidationAttemptOutcome<
       AlternativeResolutionCoverage,
       exact inert AlternativeResolutionCoverageRecord>
~~~

The occurrence-local check reconstructs every declared alternative from the
frozen scope, requires exactly one matching ledger entry, recomputes the
canonical candidate image, requires exact validated domain-policy and request-
derived occurrence-use record/capability equality, and checks every retained
fact and source-to-entry association. For every duplicate or quotient-fact-
backed entry it requires
exact quotient body, ID, complete checked-result envelope, and fresh-capability
equality. It
freshly validates every authenticated owner-policy disposition under the
Compiler-wide rule: each bound policy must authorize this consumer and
resolution/closure purpose, while each explicit no-policy contract must match
its owner capability ABI and fresh owner admission or mediated confirmation.

The record is constructed before the fresh capability. A portable completion
returns the exact record body and its matching content ID; a local completion
returns the exact local record body and its value-derived nonpersistable handle
under the Compiler-wide owner-local identity rule. The capability retains that exact
result, the validated domain-policy dependency, every occurrence-use
dependency, complete source-policy closure, and capability-dependency closure.
The inert record, ID, and handle grant no authority. An outer `Unsupported`,
`CannotAnswer`, `Refused`, `Malformed`, or `CheckerFailure` returns only its
exact Compiler attempt audit and creates neither a coverage-record coordinate
nor a coverage capability. A missing, mismatched, or policy-
prohibited capability therefore leaves coverage unresolved.

It does not prove that search found every legal transform. That stronger claim
requires a separately checked exact grammar or exploration coverage result.

## 5. PIR-owned admission

Every final target and every semantic intermediate follows the PIR-owned path:

~~~text
exact raw carrier
  -> canonical-carrier authentication
  -> whole-Protocol admission under exact regime and dependency closure
  -> process-local AdmittedProtocol capability
~~~

Compiler supplies exact material and orchestrates calls. It cannot mint,
serialize, copy, or infer `AdmittedProtocol`. A proposal containing a prior
Protocol ID, seal marker, signature, admission receipt, or matching digest has
no admission authority.

Admission establishes only that the target has valid Protocol meaning under
the exact PIR regime. It establishes neither:

- relation to the predecessor;
- conformance to `TransformIntent`;
- lineage correctness;
- property preservation or transport;
- Compiler legality or eligibility; nor
- membership, completeness, scoring, or selection.

An exact owner-completed non-admission may support one conclusive alternative
exclusion when the scope contract permits it. Malformed carrier material,
unsupported regime, missing authority, and checker failure retain their own
outcomes and cannot be relabeled as a negative transition.

## 6. Semantic paths, lineage, and transition qualification

### 6.1 Semantic versus operational paths

Producer-internal steps that make no semantic claim remain operational. They
do not become admitted Protocol intermediates or enter candidate identity.

A semantic path is exact:

~~~text
SemanticPath {
  ordered exact admitted Protocol identities,
  ordered exact adjacent transition proposition identities,
  exact typed lineage and occurrence maps,
  exact intentional-change contracts,
  exact requested adjacent and end-to-end relation coordinates
}
~~~

Every semantic intermediate is independently authenticated and admitted.
Every adjacent edge is independently checked. An end-to-end relation is an
additional exact result and replaces adjacent checks only if a named rule
proves that the omitted path facts are irrelevant to every stated consumer.

### 6.2 Exact `TransitionCase`

~~~text
TransitionCase {
  transform_problem_coordinate: CompilerValueCoordinate<TransformProblem>,
  exact admitted predecessor,
  exact admitted target,
  semantic_path: ExactCompilerValueRef<SemanticPath>,
  exact required transition propositions, polarities, and family-specific
    semantic facts,
  exact models, maps, and intentional deltas read by those propositions,
  exact checked lineage meanings,
  exact admitted semantic intermediates when read
}
~~~

The exact Analysis, Relations, PIR, or other bridge owner defines and checks
each predicate. Compiler cannot redefine its direction, observer, model,
hypotheses, polarity, assurance, owner-defined operation policy, or negative
meaning.

One transform intent may require a typed conjunction such as exact structural
correspondence, directed trace refinement, and `ChangeConforms`. Each result
record retains its complete `ExactOwnerResultBinding`, including exact owner
origin coordinates, authenticated `OwnerOperationPolicyDisposition`,
transitive source-policy dependency closure, and inert
`OwnerCapabilityRequirement`. The
occurrence-local checked
result separately retains the actual live capability for its authority
lifetime. Adjacency, relation lineage, equal bytes, or a producer preservation
annotation transports no property by default.

### 6.3 Checked lineage

Lineage is a family of typed checked witnesses, not one generic map. Separate
schemas may cover claims, events, challenge occurrences, randomness,
committed objects, ports, failures, terminals, and other semantic occurrences.

Retain, remove, introduce, rename, split, merge, and fold operations have
family-specific domain, codomain, totality, multiplicity, and compatibility
rules. A producer supplies proposed maps; the exact transition owner checks
them. A composed lineage requires a named typed composition rule.

## 7. Problem-local Compiler legality

`CompilerLegality` is separate from admission, transition meaning, and
decision constraints:

~~~text
CheckCompilerLegality(
  exact ExactCompilerValueRef<TransformProblem>,
  exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact ExactCompilerValueRef<TransitionCase>,
  exact problem-local legality profile,
  exact NamedConsumer and typed CompilerLegality purpose,
  fresh reauthorization of every inherited source-policy disposition)
  -> CompilerLegalityAttemptOutcome
~~~

The exact transition-case reference contains the exact semantic-path reference;
the legality checker therefore inspects path form and length from that exact
body rather than resolving an inert coordinate through an ambient registry. It
may check only explicitly Compiler-owned problem rules such as:

- allowed transform family and semantic path form;
- maximum path length or application multiplicity;
- closed transform parameter ranges;
- exact conformance to target-shape restrictions; and
- other finite rules identified in `TransformProblem`.

Its outcomes are:

~~~text
CompilerLegalityCompletedOutcome =
    Legal
  | Illegal(exact completed problem-local fact)

CompilerLegalityRecord {
  exact TransformProblemId and TransformProblemValidationResult,
  exact TransitionCaseId and problem-local legality profile,
  exact completed Legal or Illegal outcome and retained facts,
  exact inherited source-authority-binding and source-policy closure,
  exact named consumer, typed purpose, and freshly checked policy/contract
    authorization set,
  exact validation contract and residual trust
}

CompilerLegalityRecordId = Id(exact CompilerLegalityRecord)

CompilerLegalityResult =
  CompilerCheckedResult<
    CheckedCompilerLegality<CompilerLegalityCompletedOutcome>,
    CompilerLegalityRecord>

CompilerLegalityAttemptOutcome =
  CompilerValidationAttemptOutcome<
    CheckedCompilerLegality<CompilerLegalityCompletedOutcome>,
    CompilerLegalityRecord>
~~~

The record is constructed before the fresh capability. A portable completion
returns the exact record body and its matching content ID. A local completion
returns the exact local record body and its value-derived nonpersistable handle
under the Compiler-wide owner-local identity rule. The fresh capability retains the
exact result coordinate, output binding, and outcome. No inert result or
binding contains live authority;
U/C/R/M/F create only the exact nonauthoritative attempt audit, neither a
legality record result nor a legality capability.

`Illegal` makes one transition case unusable for this transform problem. It is
not a negative Protocol relation, property result, or admission outcome.
Qualification-trust acceptance, assessment constraints, and objectives belong
to the later decision policy, not this legality check.

## 8. Candidate identity and quotient

The relevant identity layers are:

~~~text
TargetAlternativeId
  = exact admitted target Protocol identity

SemanticPathId = Id(exact SemanticPath)

TransitionCaseId = Id(exact TransitionCase)

Candidate {
  transform_problem_coordinate: CompilerValueCoordinate<TransformProblem>,
  transition_case: ExactCompilerValueRef<TransitionCase>
}

CandidateId = Id(exact Candidate)

CandidateRef = ExactCompilerValueRef<Candidate>
~~~

These are portable IDs only when their own exact preimages contain only
portable children. If a required transition proposition, semantic fact,
lineage meaning, map, or another field actually named in `SemanticPath` or
`TransitionCase` is an owner-local reference or local Analysis/peer-owner
handle, the [Compiler owner-local rule](compiler-model.md#41-transitive-owner-local-dependency-rule)
applies forward from that field through the path, case, candidate, and any
domain or ledger whose own preimage names the affected child. Such a local
proposition or fact never enters a public `TransitionCaseId`, `CandidateId`, or
derived `CandidateDomainId`, even through a digest.

A local proof support, checked-result occurrence, or `Qualification` does not
retroactively taint a `SemanticPathId`, `TransitionCaseId`, `CandidateId`, or
domain policy whose own preimage excludes it. Instead, taint propagates forward
from that local qualification into the qualification-only projection,
resolution, `Q`, and any later assessment, ledger, report, or decision value
whose own preimage names that local child. An unrelated local assessment input
affects only the full assessment portfolio and its downstream assessment chain;
it does not affect the qualification projection, resolution, or `Q`. A
`CandidateDomain<D>` becomes local only when its own domain form, identity-
bearing originating-scope/resolution ledger, quotient partition, or member
identity is local. A local closure proof or capability makes the closure result
and its downstream binding local, but does not retroactively change a domain ID
whose declared preimage excludes that proof. Merely consuming a live capability
never changes an inert identity. Every actually affected value remains same-
process, nonpersistable, non-public, and restricted to the exact named consumer
and conjunction of source-owner policies.

`CandidateId` excludes producer, recipe, search order, proposal ordinal,
proof bytes, checker occurrence, constraints, objectives, and score.

The same admitted target reached through different semantic paths denotes
different transition cases and candidates by default. An operational producer
plan does not distinguish candidates. Multiple proofs of one identical
transition proposition create different qualifications, not different
semantic paths.

`QualifiedCandidate` is occurrence-local authority, not `CandidateId`. Its
formation consumes every exact live admission, transition, and lineage
capability required by the transition case. Every admission capability matches
its complete `ExactOwnerAdmittedSubjectBinding`; every transition or lineage
checked-result capability matches its complete `ExactOwnerResultBinding`.
Compiler freshly validates every authenticated owner-policy disposition under
the Compiler-wide rule for this candidate-qualification use. It
preserves the complete policy, assurance, trust, origin-binding, and capability-
dependency closure. A missing,
mismatched, or prohibiting policy yields an unresolved or refused qualification,
never a different candidate identity or conclusive exclusion. Durable candidate
and qualification records contain only exact identities and the complete
`ExactSourceAuthorityBindingLedger`. `CandidateId` itself remains binding-free;
the qualification and replay records retain the ledger.

~~~text
FormQualifiedCandidate(
  exact ExactCompilerValueRef<TransformProblem> and exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact ExactCompilerValueRef<TransitionCase>,
  exact ExactCompilerValueRef<Qualification> canonically derived only from
    the offered upstream admission, transition, and lineage support,
  exact complete ExactSourceAuthorityBindingLedger for every admitted subject
    and checked transition/lineage result read,
  separately supplied fresh matching admission, transition, and lineage
    capabilities,
  exact candidate-qualification consumer and purpose,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose)
  -> CompilerValidationAttemptOutcome<
       QualifiedCandidate,
       exact inert CandidateQualificationRecord>

CandidateQualificationRecord {
  exact ExactCompilerValueRef<TransformProblem> and
    TransformProblemValidationResult,
  exact ExactCompilerValueRef<TransitionCase>,
  exact CandidateRef,
  exact ExactCompilerValueRef<Qualification> canonically derived from this
    exact transition proposition and support DAG,
  exact complete ExactSourceAuthorityBindingLedger for every admitted subject
    and checked transition/lineage result read,
  exact affirmative candidate-qualification facts and retained assurance/trust,
  exact capability-neutral problem input-use authorization coordinate,
  exact candidate-qualification consumer and purpose,
  exact freshly checked Compiler and foreign policy/contract authorization
    records and total source-policy closure,
  exact validation contract and output-minting contract/result-policy
    coordinates
}

CandidateQualificationRecordId = Id(exact CandidateQualificationRecord)
~~~

`CandidateQualificationResult` is the complete
`CompilerCheckedResult<QualifiedCandidate, CandidateQualificationRecord>`
returned by `Completed`. Downstream checks receive that inert result and the
fresh capability separately.

One completed `CandidateQualificationResult` embeds exactly one
`Qualification` and `QualificationId`; one qualification cannot be shared
across several result envelopes. A corroborating support set is a canonical set
of these one-to-one bindings, not one result retroactively interpreted as many
qualifications. The qualification body may name only upstream admission,
transition, and lineage results. It cannot name its future
`CandidateQualificationResult`, so record identity remains acyclic.

The operation totally matches the transition case to every required predicate,
path, model, map, protected observation, and intentional delta in the validated
problem. Its record retains the complete `TransformProblemValidationResult`,
its capability-neutral input-use authorization coordinate, source-binding
ledger, policy closure, named consumer, typed purpose, freshly checked policy/
contract authorization set, assurance/trust, exact `CandidateId`, and exact
one-to-one `QualificationId`. Thus a case keyed by a raw
`transform_problem_coordinate` cannot bypass problem authority.

`CandidateQuotient` is an inert semantic partition, not a producer assertion or
live capability:

~~~text
CandidateQuotient {
  candidate_domain_policy_coordinate:
    CompilerValueCoordinate<CandidateDomainPolicy>,
  exact canonical finite CompilerValueCoordinate<Candidate> carrier,
  exact canonical nonempty partition of that carrier,
  exact equivalence proposition for every non-singleton class,
  exact irrelevance read closure covering every declared constraint, objective,
    property dependency, replay obligation, selected consumer, and later-owned
    input schema
}

CandidateQuotientId = Id(exact CandidateQuotient)

CandidateQuotientCheckRecord {
  exact ExactCompilerValueRef<CandidateQuotient>,
  exact CandidateDomainPolicyValidationResult,
  exact DecisionPolicyId and DecisionPolicyValidationResult retained by that
    policy-validation result,
  exact CandidateQualificationResult for every carrier member,
  exact proposition results and qualifications,
  exact complete ExactSourceAuthorityBindingLedger,
  exact policy/trust closure, named consumer, typed purpose, freshly checked
    policy/contract authorization set, and validation contract
}

CheckCandidateQuotient(
  exact CandidateDomainPolicy,
  exact CompilerResultUseAuthority<
    CheckedCandidateDomainPolicy, CandidateDomainPolicyValidationRecord>,
  exact ExactCompilerValueRef<CandidateQuotient>,
  exact qualified CompilerValueCoordinate<Candidate> values and one exact
    CompilerResultUseAuthority<
    QualifiedCandidate, CandidateQualificationRecord> for every member,
  exact complete source-binding ledger and separately supplied fresh matching
    equivalence/irrelevance capabilities,
  exact NamedConsumer and typed CandidateQuotient purpose,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedCandidateQuotient<CandidateQuotientId>,
       exact inert CandidateQuotientCheckRecord>

CandidateDomainPolicyValidationResult =
  CompilerCheckedResult<
    CheckedCandidateDomainPolicy, CandidateDomainPolicyValidationRecord>

CandidateQuotientCheckResult =
  CompilerCheckedResult<
    CheckedCandidateQuotient<CandidateQuotientId>,
    CandidateQuotientCheckRecord>

CandidateQuotientClass {
  exact candidate_quotient_coordinate:
    CompilerValueCoordinate<CandidateQuotient>,
  exact canonical class coordinate and canonical member sequence
}

CandidateQuotientClassId = Id(exact CandidateQuotientClass)
~~~

The checker may merge paths, lineage maps, or transition cases only after exact
results prove irrelevance over the complete declared read closure. Equal target
IDs, equal scores, or provider deduplication are insufficient. The canonical
singleton partition is the default and needs no non-reflexive equivalence fact.
A completed quotient check creates an exact partition under one validated
`CandidateDomainPolicy`; it does not rewrite, merge, or re-identify the
underlying `CandidateId` values. U/C/R/M/F return only the exact attempt audit
and mint no quotient capability.

## 9. Candidate domains

### 9.1 Three scopes

~~~text
ExplorationSpace
  operational plans, grammar, bounds, heuristics, and search limits

ProposalScope
  one exact frozen descriptor sequence or exact finite descriptor grammar from
  which every DeclaredAlternativeId is reconstructed without semantic results

CandidateDomain
  one canonical finite set of admitted, relation-qualified CandidateIds
~~~

The authoritative semantic domain ranges only over `CandidateId`. A plan,
recipe, proposal, unresolved alternative, raw carrier, or merely admitted
target is never a member.

Every closed domain uses a Compiler-validated immutable policy and an independently
checked closure proposition:

~~~text
CandidateDomainPolicy {
  transform_problem_coordinate: CompilerValueCoordinate<TransformProblem>,
  domain_form,
  exact originating-scope association rule,
  exact member or canonical-image rule,
  exact CompilerValueCoordinate<Candidate> order,
  exact semantic quotient and multiplicity rule,
  exact closure-proposition schema
}

CandidateDomainPolicyId = Id(exact CandidateDomainPolicy)

CandidateDomainPolicyValidationRecord {
  exact CandidateDomainPolicy and CandidateDomainPolicyId,
  exact TransformProblem and TransformProblemValidationResult,
  exact DecisionPolicy and DecisionPolicyValidationResult,
  exact capability-neutral problem/policy input-use authorization coordinates,
  exact affirmative domain-policy validation facts,
  exact NamedConsumer and typed CandidateDomainPolicyValidation purpose,
  exact source-policy closure and freshly checked policy/contract authorization
    records,
  exact Compiler semantic regime, validation contract, output-minting contract
    and result-policy coordinates, and residual trust
}

ValidateCandidateDomainPolicy(
  exact CandidateDomainPolicy and CandidateDomainPolicyId,
  exact TransformProblem and one exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact DecisionPolicy and one exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact NamedConsumer and typed CandidateDomainPolicyValidation purpose,
  fresh reauthorization of every inherited source-policy disposition,
  exact Compiler semantic regime and domain-policy validation contract)
  -> CompilerValidationAttemptOutcome<
       CheckedCandidateDomainPolicy,
       exact inert CandidateDomainPolicyValidationRecord>

The `CandidateDomainPolicyValidationRecord` retains the exact
`TransformProblemValidationResult`, `DecisionPolicyValidationResult`, their
freshly authorized input-use coordinates, the complete validated policy body,
named consumer, typed purpose, source-policy closure, output-minting contract
and policy coordinates, validation contract, and residual trust. Those inert fields
are only the exact admitted capability-contract and result-policy bindings,
IDs/ABIs, purpose-authorization record, and `OwnerCapabilityRequirement`; no
fresh admission, purpose, or result capability enters the record.

CandidateDomain<D> {
  candidate_domain_policy_coordinate:
    CompilerValueCoordinate<CandidateDomainPolicy>,
  exact originating CompilerValueCoordinate<ProposalScope> and
    CompilerValueCoordinate<AlternativeResolutionLedger>
    when the form reads them,
  canonical finite nonduplicated CompilerValueCoordinate<Candidate> sequence,
  exact CompilerValueCoordinate<CandidateQuotient> and quotient-class
    partition when quotienting is enabled
}

CandidateDomainId = Id(exact CandidateDomain<D>)

CandidateDomainClosureProposition {
  candidate_domain_coordinate: CompilerValueCoordinate<CandidateDomain<D>>,
  exact membership, admission, relation-qualification, uniqueness,
    canonical-order, originating-scope image, quotient, finiteness,
    and coverage claims required by its domain form
}

CandidateDomainClosureRecord<D> {
  exact CandidateDomainPolicy and CandidateDomain<D>,
  exact CandidateDomainClosureProposition,
  exact CandidateDomainPolicyValidationResult,
  exact TransformProblemValidationResult and DecisionPolicyValidationResult,
  exact AlternativeResolutionCoverageRecordResult when read,
  exact CandidateQualificationResult for every member,
  exact CandidateQuotientCheckResult for every quotient fact read,
  exact complete foreign source-binding ledger,
  exact affirmative candidate-domain closure fact,
  exact named consumer, typed closure purpose, freshly checked Compiler and
    foreign policy/contract authorization sets, validation contract, and
    residual trust
}

CheckCandidateDomainClosure<D>(
  exact CandidateDomainPolicy and CandidateDomain<D>,
  exact CompilerResultUseAuthority<
    CheckedCandidateDomainPolicy, CandidateDomainPolicyValidationRecord>,
  exact TransformProblem and exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact CandidateDomainClosureProposition,
  exact CompilerResultUseAuthority<
    AlternativeResolutionCoverage, AlternativeResolutionCoverageRecord> when
    the domain form reads an originating scope,
  exact CompilerResultUseAuthority<
    QualifiedCandidate, CandidateQualificationRecord> for every member,
  exact CompilerResultUseAuthority<
    CheckedCandidateQuotient<CandidateQuotientId>,
    CandidateQuotientCheckRecord> for every quotient fact read,
  live admission, transition, and owner qualification capabilities for every
    exact member or closure fact read,
  every complete `ExactOwnerAdmittedSubjectBinding<Owner, SubjectFamily>` with
    exact Owner and SubjectFamily witnesses for foreign admitted subjects,
  every complete `ExactOwnerResultBinding<Owner, ResultFamily>` with exact
    Owner and ResultFamily witnesses for foreign checked results,
  every exact authenticated OwnerOperationPolicyDisposition and transitive
    source-policy closure freshly validated under the Compiler-wide rule for
    the named closure purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedCandidateDomain<D>, exact inert CandidateDomainClosureRecord<D>>
~~~

`CandidateDomainClosureResult<D>` is the complete
`CompilerCheckedResult<CheckedCandidateDomain<D>,
CandidateDomainClosureRecord<D>>` returned by `Completed`.

Only an affirmative check of this exact proposition mints the process-local
`CheckedCandidateDomain<D>` capability. A domain object, member list, digest,
solver status, or persisted prior capability does not.

The closure check verifies that every foreign source capability matches its
exact admitted-subject or checked-result binding, while every Compiler-owned
input arrives through `CompilerResultUseAuthority` and matches its complete
`CompilerCheckedResult`, including record body/coordinate, output binding,
fresh capability, and downstream-use authorization. It verifies candidate,
polarity, assurance, trust, authenticated owner-policy disposition, complete
owner-created source-authority binding, and transitive source-policy closure,
and that
every bound policy permits domain-closure use. A mismatch, prohibition, or
refusal leaves the domain check unresolved or refused; it cannot remove a
member, prove closure, or become a negative qualification. The live
`CheckedCandidateDomain<D>` capability preserves the complete source-policy and
capability-dependency closure. In the fully portable lane the durable domain and
closure records contain only identities and the complete
`ExactSourceAuthorityBindingLedger`; a local form uses a nonpersistable handle.

### 9.2 Exact domain forms

The target supports:

~~~text
SubmittedCandidateSet
  exact canonical finite set of already admitted and transition-qualified
  CandidateIds; closure checks membership, uniqueness, ordering, and every
  stated qualification

ResolvedSubmittedProposalScope
  exact frozen ProposalScopeId + total inert AlternativeResolutionLedgerId
  + exact live AlternativeResolutionCoverage requirement for closure checking
  + the checked canonical nonempty-or-empty CandidateId image

EnumeratedClosedCandidateDomain
  exact finite pre-admission grammar and bounds + canonical enumeration
  + frozen ProposalScopeId + checked total resolution, membership,
  uniqueness, pruning, quotient, image, and grammar coverage

CertifiedSymbolicCandidateDomain
  exact finite symbolic encoding of a canonical, already materialized,
  PIR-admitted, and transition-qualified CandidateId image
  + checked denotation, membership, uniqueness, and closure certificate

OpenExploration
  no closed CandidateDomain claim
~~~

Every domain fixes canonical member order, duplicate/quotient policy, and an
exact meaning of completeness. Completeness is always scope-qualified:
submitted-set closure, resolved-scope closure, enumerated-grammar closure, and
certified-symbolic closure are different claims.

### 9.3 Symbolic-domain v0 restriction

Symbolic domain denotation and closure are separate from candidate
infeasibility and optimality:

1. a denotation certificate establishes the exact finite symbolic encoding;
2. a closure certificate establishes its exact canonical image in semantic
   `CandidateId` values and its required membership and uniqueness facts;
3. an infeasibility certificate may establish constraint failure over that
   already closed domain; and
4. an optimality certificate may establish one exact comparison claim over an
   already closed, decision-sufficiently accounted comparison domain.

One solver status or proof log cannot silently stand for all four.

In v0, every member of the symbolic denotation is already named by
`CandidateId`, and its target material has already been independently
materialized, authenticated, admitted by PIR, and transition-qualified. A
symbolic certificate may compress canonical-image reconstruction, domain
closure, repeated assessment, or an exact optimality proof; it cannot replace
target materialization, admission, or relation qualification.

Under the selected Stage 3 authority model, symbolic compression cannot grant
ordinary candidate-domain authority over unnamed or unadmitted alternatives.
A lazy or universally quantified rule denoting candidates without independent
materialization and admission would require a separately reviewed future
Stage 3 reopening.

### 9.4 Domain capabilities and qualified outcomes

Representative live capabilities are:

~~~text
AlternativeResolutionCoverage
CheckedTransition<F>
CheckedCompilerLegality<CompilerLegalityCompletedOutcome>
QualifiedCandidate
CheckedCandidateQuotient<CandidateQuotientId>
CheckedCandidateDomain<D>
~~~

Unresolved proposal or domain work retains exact `Unsupported`,
`CannotAnswer`, `Refused`, `Malformed`, `CheckerFailure`, or incomplete status.
None becomes conclusive exclusion or domain closure by omission.

## 10. Reversal triggers

This target must be reopened if an exact counterexample shows that:

1. a closed proposal scope must depend cyclically on later assessment or
   decision outcomes;
2. a semantic candidate cannot be identified independently of a producer or
   proposal occurrence;
3. two distinct semantic paths are always interchangeable without an exact
   consumer-relative quotient check;
4. a valid transition family cannot expose exact source, target, direction,
   model, maps, assumptions, outcome, and capability;
5. exact domain closure requires trusting mutable producer discovery state;
6. the v0 symbolic restriction prevents a necessary closed decision for which
   an equally exact smaller checker exists; or
7. problem-local legality cannot remain distinct from semantic transition or
   decision constraints.

Current implementation shape, provider convenience, search performance, and
migration cost are not reopening reasons by themselves.

## 11. Exact nonclaims

This specification does not establish:

- that any proposal is well formed, admitted, related, legal, or a candidate;
- truth, completeness, or adequacy of any transition checker, map, lineage,
  quotient, grammar, enumeration, pruning rule, or certificate;
- completeness of any concrete proposal scope or candidate domain;
- relation satisfaction, property preservation, property transport, or
  cryptographic security;
- feasibility, eligibility, cost, Pareto membership, selection, or
  `NoEligible`;
- global coverage or optimality beyond one exact declared scope;
- OIR projection, endpoint realization, runtime behavior, implementation
  correspondence, compatibility, migration, or normative authority; or
- persistence of `AdmittedProtocol`, checked-transition, legality, candidate,
  or domain capabilities.
