# Compiler assessment, selection, and replay

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

> **K1 transition notice — 2026-08-26:** The identity, value, algorithm,
> dependency, and replay forms below predate
> [Executable Semantic Foundations](../foundation/executable-foundations.md).
> K1 does not ratify these assessment and selection carriers. Their exact
> reconciliation remains a post-kernel integration obligation under the
> Compiler-owned judgments.

## 1. Scope

This document defines two distinct paths: how one exact semantic
`CandidateDomain<D>` becomes a closed decision over an exact
`ComparisonAlternativeDomain<Q>`, and how an independently checked open report
can describe any exact reached qualified subset and audit-relative accounting
without requiring those domains to close:

~~~text
closed semantic CandidateDomain<D>
  -> immutable candidate-indexed QualificationInputProjections
  -> separate qualification-input checks
  -> total QualificationResolutionLedger<D>
  -> exact ComparisonAlternativeDomain<Q>
  -> immutable candidate-indexed AssessmentInputPortfolios
  -> separate portfolio-completeness and input-use checks
  -> total AssessmentLedger<D,Q>
  -> checked AssessmentSufficiencyBasis and AssessmentClosureResult<D,Q>
  -> CompleteAssessment: exact comparison, Pareto, tie, and representative
     recomputation
     | ExternalCertificate: exact certified-payload extraction and only
       payload-supported representative/optional totalization
  -> decision binding both D and Q

checked DecisionPolicy
  + any exact reached qualified subset
  + every exact reached closure result the report actually reads
  + audit/not-attempted/blocker accounting for every claimed slot
  -> separately checked explicitly open report

preparation/check failure at any reached operation
  -> outer U/C/R/M/F outcome
~~~

Only the closed-decision path requires closed `D` and `Q`, total qualification
resolution, total assessment accounting, and decision sufficiency.

The overall owner and authority model is specified in
[Compiler model](compiler-model.md). Search, proposal resolution, target
admission, transition qualification, legality, candidate identity, and
candidate-domain closure are specified in
[Proposals, relations, and candidate domains](proposals-relations-and-domains.md).

Semantic candidates, qualification alternatives, input portfolios,
assessments, and decisions remain different identities. No assessment process
may silently alter `D` or reinterpret an upstream result.

## 2. Qualification identity and resolution

### 2.1 `QualificationId`

One semantic candidate may have several independently valid support bases:

~~~text
Qualification {
  candidate_coordinate: CompilerValueCoordinate<Candidate>,
  exact admission and transition support DAG,
  exact transition proposition and upstream admission, transition, and lineage
    result identities; never the future CandidateQualificationResult,
  exact complete ExactSourceAuthorityBindingLedger for every admitted subject,
    transition result, and judgment,
  exact semantic-basis identities,
  exact validation-basis and checker-contract identities,
  exact authenticated OwnerOperationPolicyDisposition for every source,
  exact transitive source-operation-policy dependency closures,
  exact hypotheses and assurance coordinates,
  exact residual-trust closure
}

QualificationId = Id(exact Qualification)

CanonicalQualificationSet {
  exact candidate_coordinate: CompilerValueCoordinate<Candidate>,
  exact decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy>
    and qualification-order coordinate,
  exact canonical nonempty sequence of
    CompilerValueCoordinate<Qualification> values under that order
}

CanonicalQualificationSetId = Id(exact CanonicalQualificationSet)

QualificationSupportBinding {
  exact ExactCompilerValueRef<Qualification>,
  exact CandidateQualificationResult whose CandidateQualificationRecord embeds
    that same Qualification and QualificationId,
  exact equality of candidate coordinate, transition case/proposition, support DAG,
    source-binding ledger, hypotheses, assurance, source-policy closure, and
    residual trust
}

CanonicalQualificationSupportBindingLedger {
  exact candidate_coordinate: CompilerValueCoordinate<Candidate>,
  exact canonical one-to-one map from every present
    CompilerValueCoordinate<Qualification> to one QualificationSupportBinding,
  no qualification coordinate or CandidateQualificationResult occurs more
    than once
}
~~~

`QualificationId` does not change `CandidateId`. Two proofs of the identical
transition proposition, result, hypotheses, model, maps, operation-policy
coordinates, and assurance coordinates are different qualifications of one
semantic candidate. A change to an assumption, observer, model, map, result
bound, polarity, operation policy, or assurance coordinate changes the semantic
proposition or accepted qualification rather than merely its proof bytes. An
operation-policy change alone does not change proposition meaning.

### 2.2 Total `QualificationResolutionLedger<D>`

`DecisionPolicy` states schemas and rules, not candidate facts. It fixes one
exact qualification policy:

~~~text
QualificationResolutionPolicy =
    RequireSpecifiedSupport(exact qualification schema)
  | RequireSpecifiedCorroboratingSet(exact set schema)
  | ChooseCanonicalSupport(exact total order and admissibility predicate)
  | CompareQualifiedAlternatives
~~~

Concrete `QualificationId` values enter only after a candidate exists. Each is
embedded one-to-one in the exact complete `CandidateQualificationResult` that
establishes its candidate/support association, and projection checking verifies
the canonical `QualificationSupportBinding`; equal qualification bytes or IDs
without that checked-result binding grant no authority. Compiler
freezes a qualification-only projection independently from assessment-only
facts:

~~~text
QualificationInputProjection {
  candidate_coordinate: CompilerValueCoordinate<Candidate>,
  decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy> and
    exact QualificationResolutionPolicy,
  exact CanonicalQualificationSupportBindingLedger,
  exact complete ExactSourceAuthorityBindingLedger for those qualifications,
  exact authenticated OwnerOperationPolicyDisposition for every source and
    complete transitive source-operation-policy dependency closures,
  exact hypotheses, assurance, residual trust, and OwnerCapabilityRequirement
    values,
  exact candidate-association and qualification-input completeness declaration
}

QualificationInputProjectionDisposition =
    Complete(exact coverage, uniqueness, association, and policy-schema facts)
  | Incomplete(exact missing, extra, ambiguous, mismatched-association, or
               open-enumeration blockers)

QualificationInputProjectionCheckRecord {
  exact QualificationInputProjection and its portable ID or local handle,
  exact DecisionPolicyValidationResult and
    CanonicalQualificationSupportBindingLedger,
  exact complete foreign source-binding ledger and accepted QualificationId
    values,
  exact QualificationInputProjectionDisposition,
  exact named consumer, typed qualification-resolution purpose, freshly checked
    Compiler and foreign policy/contract authorization sets, validation
    contract, and residual trust
}

CheckQualificationInputProjection(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact immutable QualificationInputProjection,
  exact CanonicalQualificationSupportBindingLedger,
  one exact CompilerResultUseAuthority<
    QualifiedCandidate, CandidateQualificationRecord> for every present
    QualificationSupportBinding,
  exact matching admitted subjects and checked-result records with separately
    supplied live capabilities,
  every exact authenticated OwnerOperationPolicyDisposition and transitive
    source-policy closure,
  exact NamedConsumer and typed qualification-resolution purpose,
  for BoundTo, the complete policy preimage and fresh policy authority for the
    named qualification-resolution purpose,
  for OwnerDefinesNoOperationPolicy, the exact owner capability-contract and
    ABI preimage plus fresh owner admission or mediated confirmation)
  -> CompilerValidationAttemptOutcome<
       CheckedQualificationInputProjection,
       exact inert QualificationInputProjectionCheckRecord>
~~~

`QualificationInputProjectionCheckResult` is the complete
`CompilerCheckedResult<CheckedQualificationInputProjection,
QualificationInputProjectionCheckRecord>` returned by `Completed`.

The `Complete` projection contains every and only input read by the qualification policy;
an Analysis, peer-owner, Stage 4B, Evidence, constraint, or objective fact that
qualification does not read is absent. The check establishes exact candidate
association, accepted qualification schema, total qualification-input
enumeration under the policy only for `Complete`; a completed `Incomplete`
result retains the exact structural blockers without treating them as
qualification ineligibility. Missing authority, policy refusal, unsupported
checking, malformed invocation, or checker failure remains an outer attempt
audit and creates no projection result. In the portable lane the projection has
`QualificationInputProjectionId`:

~~~text
QualificationInputProjectionId = Id(exact QualificationInputProjection)
~~~

If its own preimage names any local input it
has `LocalCompilerHandle<QualificationInputProjection>`. An unrelated local
assessment fact cannot taint this projection, resolution, or `Q`. Only an
explicitly pre-bound submitted-input variant may name qualifications in advance,
and it must also bind their exact submitted-candidate association.

Every candidate in exact `CandidateDomain<D>` receives one total resolution
entry:

~~~text
QualificationProjectionEvaluationEntry =
  CompilerRequirementEvaluationEntry<
    CheckedQualificationInputProjection,
    QualificationInputProjectionCheckRecord>

QualificationProjectionEvaluationLedger<D> {
  exactly one candidate-indexed QualificationProjectionEvaluationEntry for
    every CompilerValueCoordinate<Candidate> in D,
  every Checked entry contains its complete projection check result,
  every Unresolved or NotAttempted entry contains only its exact nonauthoritative
    resolution-scoped blocker material
}

QualificationResolutionEntry =
    ResolvedTo(CanonicalNonEmptySeq<
      CompilerValueCoordinate<ComparisonAlternative>>)
  | DefinitivelyQualificationIneligible(exact completed policy fact)
  | Undetermined(exact completed Incomplete projection disposition or exact
                 unresolved/not-attempted projection blocker)

QualificationResolutionLedger<D> {
  exact ExactCompilerValueRef<CandidateDomain<D>> and
    CandidateDomainClosureResult<D>,
  exact ExactCompilerValueRef<DecisionPolicy> and
    DecisionPolicyValidationResult,
  exact candidate-indexed
    CompilerValueCoordinate<QualificationInputProjection> values,
  exact QualificationProjectionEvaluationLedger<D>,
  exact QualificationSupportBinding and CandidateQualificationResult for every
    qualification actually read by a Checked entry or terminal policy
    disposition,
  exactly one entry for every CompilerValueCoordinate<Candidate> in canonical
    D order,
  exact complete source-binding and transitive source-policy closure,
  exact named consumer, typed qualification-resolution/comparison purposes,
    freshly checked Compiler and foreign policy/contract authorization sets,
    validation contract, and residual trust
}

QualificationResolutionLedgerId = Id(exact QualificationResolutionLedger<D>)

QualificationResolutionLedgerResult<D> =
  CompilerCheckedResult<
    CheckedQualificationResolution<D>, QualificationResolutionLedger<D>>
~~~

The ledger is total even when a semantic result is unresolved. A candidate
cannot disappear because its proof basis is inconvenient.
`DefinitivelyQualificationIneligible` requires a completed exact policy fact
whose authenticated owner-policy disposition is valid and whose every bound
policy permits this qualification-resolution and comparison use. An incomplete
or open support set, unsupported basis, refusal,
malformed support, missing or mismatched live authority, source-policy
mismatch or prohibition, or checker failure is recorded as `Undetermined` when
it is carried by an exact projection evaluation blocker; a failure of the
resolution operation itself remains an outer non-result. Either case
blocks a closed decision. None of those outcomes is evidence of qualification
ineligibility.

Authority for the total resolution is created only by an occurrence-local
operation:

~~~text
CheckQualificationResolution<D>(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact CandidateDomain<D> and exact CompilerResultUseAuthority<
    CheckedCandidateDomain<D>, CandidateDomainClosureRecord<D>>,
  exact immutable QualificationInputProjection for every member of D,
  exact QualificationProjectionEvaluationLedger<D>,
  one exact CompilerResultUseAuthority<
    CheckedQualificationInputProjection,
    QualificationInputProjectionCheckRecord> for every Checked projection
    entry in the evaluation ledger,
  exact QualificationSupportBinding values and one exact CompilerResultUseAuthority<
    QualifiedCandidate, CandidateQualificationRecord> for every qualification
    actually read by a Checked entry or terminal resolution disposition,
  exact matching live foreign source-owner capabilities for every checked
    foreign source actually read,
  every exact authenticated OwnerOperationPolicyDisposition and transitive
    source-policy closure,
  exact NamedConsumer and typed qualification-resolution and comparison
    purposes,
  for BoundTo, the complete policy preimage and fresh policy authority for the
    named qualification-resolution and comparison purposes,
  for OwnerDefinesNoOperationPolicy, the exact owner capability-contract and
    ABI preimage plus fresh owner admission or mediated confirmation)
  -> CompilerValidationAttemptOutcome<
       CheckedQualificationResolution<D>,
       exact inert QualificationResolutionLedger<D>>
~~~

Every capability, record, projection, policy, candidate, and purpose must match
the exact inert dependency named by the resolution. A portable completion
returns the exact ledger body and matching content ID before minting the fresh
capability. A local completion returns the exact local ledger body and its
value-derived nonpersistable handle under the Compiler-wide owner-local
identity rule. The live result retains that exact result plus the complete source-
policy and dependency closure needed by downstream checks. A `ResolvedTo` or
`DefinitivelyQualificationIneligible` entry requires a `Checked(Complete(...))`
projection and every exact result-use authority it reads. `Checked(Incomplete)`,
`Unresolved`, and `NotAttempted` can produce only `Undetermined`; their attempt
or bookkeeping material grants no semantic authority. U/C/R/M/F from the
resolution operation itself return only an attempt audit, no ledger result, and
mint no qualification-resolution capability. The result
identity is separate from the candidate, qualification projection, assessment
portfolio, assessment, and decision.

## 3. `ComparisonAlternativeDomain<Q>`

`ComparisonAlternativeDomain<Q>` is derived from `D` and the total
qualification-resolution ledger. It never replaces or redefines the semantic
candidate domain.

~~~text
ComparisonAlternative {
  decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy>,
  candidate_coordinate: CompilerValueCoordinate<Candidate>,
  exact canonical_qualification_set_coordinate:
    CompilerValueCoordinate<CanonicalQualificationSet> accepted by policy
}

ComparisonAlternativeId = Id(exact ComparisonAlternative)
~~~

For specified support, a corroborating set, or canonical support, each resolved
candidate maps to exactly one comparison alternative. Under
`CompareQualifiedAlternatives`, it maps to every and only accepted exact
qualification alternative allowed by the policy's closed enumeration rule.
The final form may therefore expose `(CandidateId, QualificationId)` or an
explicit canonical qualification set as the comparison operand without
duplicating or changing the semantic candidate.

~~~text
ComparisonAlternativeDomain<Q> {
  candidate_domain_coordinate: CompilerValueCoordinate<CandidateDomain<D>>,
  decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy>,
  qualification_resolution_ledger_coordinate:
    CompilerValueCoordinate<QualificationResolutionLedger<D>>,
  canonical finite nonduplicated
    CompilerValueCoordinate<ComparisonAlternative> sequence
}

ComparisonAlternativeDomainId = Id(exact ComparisonAlternativeDomain<Q>)

ComparisonAlternativeDomainClosureProposition {
  comparison_alternative_domain_coordinate:
    CompilerValueCoordinate<ComparisonAlternativeDomain<Q>>,
  exact total candidate coverage, qualification-policy conformance,
    canonical expansion, membership, uniqueness, and projection claims
}

ComparisonAlternativeDomainClosureRecord<D,Q> {
  exact ComparisonAlternativeDomain<Q> and closure proposition,
  exact DecisionPolicyValidationResult,
  exact CandidateDomainClosureResult<D>,
  exact QualificationResolutionLedgerResult<D>,
  exact affirmative comparison-alternative-domain closure fact,
  exact named consumer, typed comparison-domain-closure purpose, freshly
    checked Compiler policy authorization set, validation contract, and
    residual trust
}
~~~

Authority for the derived domain is created only by:

~~~text
CheckComparisonAlternativeDomainClosure<D,Q>(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact CandidateDomain<D> and exact CompilerResultUseAuthority<
    CheckedCandidateDomain<D>, CandidateDomainClosureRecord<D>>,
  exact QualificationResolutionLedger<D> and exact CompilerResultUseAuthority<
    CheckedQualificationResolution<D>, QualificationResolutionLedger<D>>,
  exact ComparisonAlternativeDomain<Q>,
  exact ComparisonAlternativeDomainClosureProposition,
  exact NamedConsumer and typed comparison-domain-closure purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedComparisonAlternativeDomain<Q>,
       exact inert ComparisonAlternativeDomainClosureRecord<D,Q>>
~~~

`ComparisonAlternativeDomainClosureResult<D,Q>` is the complete
`CompilerCheckedResult<CheckedComparisonAlternativeDomain<Q>,
ComparisonAlternativeDomainClosureRecord<D,Q>>` returned by `Completed`.

An affirmative occurrence of this check mints
`CheckedComparisonAlternativeDomain<Q>` and establishes:

- exact source `CandidateDomainId`;
- exact total `QualificationResolutionLedgerId`;
- exact qualification-policy conformance and canonical expansion;
- exact canonical `ComparisonAlternativeId` set and order;
- no missing, extra, or silently duplicated candidates or qualifications;
- total and unique projection from every member of `Q` to one `CandidateId`;
  and
- every candidate omitted from `Q` together with its exact terminal
  `DefinitivelyQualificationIneligible` basis.

This capability proves neither candidate-domain closure nor any assessment.
An unresolved qualification result prevents closed formation of `Q` for the
requested decision strength. `Q` contains assessment units, not plans,
proposals, raw targets, or unresolved qualifications. A selected member of
`Q` always projects to exactly one semantic candidate, and the decision reports
its exact qualification set separately.

Missing, stale, mismatched, or policy-prohibited authority prevents this live
capability. Neither the durable qualification ledger nor matching domain bytes
can substitute for the live `D` and qualification-resolution capabilities.

## 4. Immutable assessment input portfolios

### 4.1 Candidate-indexed portfolio body identity

After a semantic candidate exists and before any comparison alternative for it
is assessed, its concrete offered input body is frozen:

Compiler uses the typed `ExactOwnerAdmittedSubjectBinding`,
`ExactOwnerResultBinding`, and `ExactSourceAuthorityBindingLedger` defined by
the [Compiler-wide source-binding rule](compiler-model.md#2-ownership-boundary).

It contains an `OwnerCapabilityRequirement`, never a live capability or its
occurrence identity. For Analysis, its origin coordinates contain the complete
per-coordinate `ExactJudgmentBinding`; another owner supplies its equally exact
typed subject/admission or result coordinate, qualification, derivation,
support, semantic basis, validation basis, and checker coordinates.
The `OwnerOperationPolicyDisposition` is structurally mandatory: it is either
`BoundTo` with the exact authenticated policy contract or
`OwnerDefinesNoOperationPolicy` with the exact owner capability-contract
identity and capability ABI. Compiler never reduces this structure to
proposition plus an optional immediate policy.

~~~text
AssessmentInputPortfolio {
  decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy>,
  candidate: ExactCompilerValueRef<Candidate>,
  exact Analysis and peer-owner result records required by policy schemas,
  exact Stage4BOwnedFactOrValue records required by policy schemas,
  exact Evidence-owned qualified records, appraisals, or values required by
    policy schemas,
  exact authority-bearing admitted subject/view values required by direct
    structural objectives,
  exact complete CompilerCheckedResultLedger for every Compiler-owned
    structural value offered under the policy,
  exact DecisionPolicyValidationResult plus every declared-preference
    coordinate offered under that validated policy,
  exact `ExactSourceAuthorityBindingLedger` for every foreign input,
  exact association material from every input to this candidate and policy
}
~~~

`AssessmentInputPortfolioId` content-identifies only this immutable canonical
candidate-indexed body. It does not contain or identify:

- a completeness result;
- an input-use or read-set result;
- an assessment evaluation trace;
- `AssessmentId`;
- an eligibility outcome; or
- a decision.

This one-way identity rule breaks cycles. Additional or replacement input
material creates a new portfolio ID rather than mutating the old body.

This paragraph describes the portable lane only. If the candidate, a concrete
input record, or any transitive dependency is an owner-local reference or
handle, the [Compiler owner-local dependency rule](compiler-model.md#41-transitive-owner-local-dependency-rule)
replaces this ID and every affected completeness, input-use, constraint,
objective, assessment, closure, report, and decision ID with its
`LocalCompilerHandle<T>`. Qualification resolution and the comparison domain
remain portable unless their separate `QualificationInputProjection` preimages
are themselves local. The complete affected chain is
same-process, nonpersistable, non-public, and ineligible for exact cold replay;
a digest cannot remove that taint.

The body contains concrete inputs only after `CandidateId` exists. Every
portfolio therefore carries the exact candidate reference, including its exact
transition case and admitted target, rather than assuming an ambient lookup
from a candidate coordinate. Every foreign input retains the appropriate
complete `ExactOwnerResultBinding` or
`ExactOwnerAdmittedSubjectBinding`, including its owner, exact proposition or
value schema, subject, polarity when applicable, model, assurance, residual
trust, inert `OwnerCapabilityRequirement`, authenticated
`OwnerOperationPolicyDisposition`, and complete transitive source-operation-
policy dependency closure. Every Compiler-owned structural input
retains its complete inert `CompilerCheckedResult`, including the exact body,
portable ID or owner-local coordinate, output binding, and inherited source-
policy/origin closure. A declared preference is not a separate result family:
it retains the exact `DecisionPolicyValidationResult` already consumed by the
operation plus its coordinate inside that policy;
the portfolio cannot cast or merge them. Live capabilities are supplied
separately to checking operations and are never encoded into the portfolio.

### 4.2 Separate portfolio-completeness check

~~~text
AssessmentInputCompletenessProposition {
  assessment_input_portfolio_coordinate:
    CompilerValueCoordinate<AssessmentInputPortfolio>,
  decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy>,
  exact required-schema coverage, uniqueness, association, polarity,
    assurance, authenticated owner-policy disposition, transitive source-
    operation-policy, and residual-trust acceptance claims
}

AssessmentInputCompletenessRecord {
  exact ExactCompilerValueRef<AssessmentInputPortfolio>,
  exact AssessmentInputCompletenessProposition,
  exact ExactCompilerValueRef<DecisionPolicy>,
  exact DecisionPolicyValidationResult,
  exact completed coverage outcome and retained mismatches,
  exact complete ExactSourceAuthorityBindingLedger and exact Compiler-owned
    checked-result ledger,
  exact named consumer, typed portfolio-completeness purpose, freshly checked
    Compiler and foreign policy/contract authorization sets, validation
    contract, and residual trust
}

AssessmentInputCompletenessRecordId =
  Id(exact AssessmentInputCompletenessRecord)

CheckAssessmentInputCompleteness(
  exact ExactCompilerValueRef<DecisionPolicy>,
  exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact ExactCompilerValueRef<AssessmentInputPortfolio>,
  exact AssessmentInputCompletenessProposition,
  exact owner-created requirement views,
  exact complete ExactSourceAuthorityBindingLedger for every foreign input,
  exact CompilerResultUseAuthorityLedger for every
    Compiler-owned source,
  exact NamedConsumer and typed portfolio-completeness purpose,
  for every BoundTo disposition, the complete policy preimage and fresh policy
    authority for the named completeness purpose,
  for every OwnerDefinesNoOperationPolicy disposition, the exact owner
    capability-contract and ABI preimage plus fresh owner admission or mediated
    confirmation,
  exact matching live input capabilities)
  -> CompilerValidationAttemptOutcome<
       CheckedAssessmentInputCompleteness,
       exact inert AssessmentInputCompletenessRecord>
~~~

`AssessmentInputCompletenessResult` is the complete
`CompilerCheckedResult<CheckedAssessmentInputCompleteness,
AssessmentInputCompletenessRecord>` returned by `Completed`.

This check establishes whether the frozen body contains every required input
slot with the exact subject, model, polarity, hypotheses, assurance, source
operation policy, qualification, and target association. It may recognize
exact policy-permitted short-circuit structure, but it does not evaluate
constraints, objectives, or eligibility. Acceptance never overrides the
source policy's consumer, disclosure, persistence, replay, or other use rule.

Its completed negative retains missing, extra, mismatched, ambiguous, or
wrong-association slots. Unsupportedness, cannot-answer, refusal, malformation,
and checker failure remain distinct. The inert result record and matching
occurrence-local checked capability are separate inputs to assessment, never a
field in the portfolio it checks. Completeness is relative to this
exact policy schema, not a claim that every conceivable property was computed.

### 4.3 Separate input-use check

Each peer-owner fact or value remains independent of the assessment. A
separate Compiler-owned use check establishes how its exact subject tuple
satisfies one policy schema for this candidate:

~~~text
CheckAssessmentInputUse(
  exact independent owner fact or value,
  exists exact Owner and CapabilityFamily: exact complete typed
    ExactSourceAuthorityBinding<Owner, CapabilityFamily>,
  for BoundTo, the complete policy preimage and fresh policy authority for the
    named assessment-input-use purpose,
  for OwnerDefinesNoOperationPolicy, the exact owner capability-contract and
    ABI preimage plus fresh owner admission or mediated confirmation,
  exact matching live owner capability,
  exact ExactCompilerValueRef<DecisionPolicy>,
  exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact required fact/value schema,
  exact ExactCompilerValueRef<AssessmentInputPortfolio>,
  exact canonical typed portfolio-slot coordinate selecting one declared
    input in that exact portfolio body,
  exact NamedConsumer and typed assessment-input-use purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedAssessmentInputUse,
       exact inert AssessmentInputUseRecord>
~~~

The checker resolves the canonical typed slot coordinate against the supplied
exact portfolio body and requires exactly one declared member whose complete
fact or value, schema, source binding, candidate association, and policy
association equal the supplied operands. It checks the member's candidate and
target association against the portfolio's exact candidate reference, including
that candidate's embedded exact transition case and admitted target. A portable
coordinate is checked by recomputing the body identity; it is never treated as
ambient lookup authority. An owner-local coordinate is resolved only through
the same-owner, same-generation relation carried by the exact value reference.
The checker rejects a missing, duplicate, or mismatched slot, wrong-candidate or
wrong-target facts, mismatched later-owned subjects, incompatible owner
operation policies or policy schemas, missing or mismatched live authority,
and any candidate or policy association that does not close against the
portfolio's own coordinates. The inert `AssessmentInputUseRecord` binds the
independent fact identity, its exact
complete typed `ExactSourceAuthorityBinding`, including its authenticated policy
disposition, inert `OwnerCapabilityRequirement`, and complete transitive
source-policy closure, plus the schema, exact portfolio reference, canonical
typed slot coordinate, and completed unique membership and association result,
never a capability or future `AssessmentId`. The occurrence-local
`CheckedAssessmentInputUse` retains the exact fresh owner capability and inert
checked result for its authority lifetime. The result record additionally
retains the exact `DecisionPolicy` reference and validation result, named
consumer, typed purpose, freshly checked policy/contract authorization set,
validation contract, and residual trust. It cannot widen what the source owner
permits. Any assessment evaluation trace must also refer only to checked
entries in that same exact frozen portfolio; hidden ambient reads and
undeclared registry lookups are malformed.

~~~text
AssessmentInputUseRecord {
  exact independent owner fact or value and, for its exact Owner and
    CapabilityFamily, complete typed
    ExactSourceAuthorityBinding<Owner, CapabilityFamily>,
  exact ExactCompilerValueRef<DecisionPolicy> and
    DecisionPolicyValidationResult,
  exact required fact/value schema and
    ExactCompilerValueRef<AssessmentInputPortfolio>,
  exact canonical typed portfolio-slot coordinate,
  exact completed unique membership, portfolio-candidate/target association,
    policy-association, and accepted-use result,
  exact NamedConsumer and typed assessment-input-use purpose,
  exact freshly checked foreign and Compiler policy/contract authorization
    records and transitive source-policy closure,
  exact validation contract, output-minting contract/result-policy coordinates,
    and residual trust
}

AssessmentInputUseRecordId = Id(exact AssessmentInputUseRecord)
~~~

~~~text
AssessmentInputUseResult = CompilerCheckedResult<
  CheckedAssessmentInputUse, AssessmentInputUseRecord>

AssessmentInputUseResultLedger = CanonicalTypedLedger<
  exact AssessmentInputUseResult>
~~~

`AssessmentInputUseResult` is returned only by `Completed`.

The assessment layer uses a total candidate- and portfolio-indexed carrier:

~~~text
AssessmentInputUseEvaluationLedger<D,Q> {
  exact ComparisonAlternativeDomainId and ComparisonAlternativeId,
  exact ExactCompilerValueRef<AssessmentInputPortfolio> and
    ExactCompilerValueRef<DecisionPolicy>,
  for every exact input-use requirement in the policy schema, exactly one
    CompilerRequirementEvaluationEntry<
      CheckedAssessmentInputUse, AssessmentInputUseRecord>
}
~~~

A `Checked` entry retains the complete input-use result and is consumable only
with a separately fresh matching result-use authority. `Unresolved` retains the
exact outer attempt audit, and `NotAttempted` retains only an enclosing-assessment-scoped
bookkeeping reason. Neither non-checked branch establishes input acceptance,
absence, refusal as a semantic fact, or any candidate property.

This formula applies only to the portable untainted lane. A local input creates
the corresponding `LocalCompilerHandle<AssessmentInputUseRecord>` instead.

Portfolio-body identity, portfolio completeness, and exact input use are three
separate results. Neither check can be placed inside the portfolio preimage or
made true by the eventual assessment record.

## 5. Typed constraints

Each constraint fixes an exact input pattern, accepted polarity, hypothesis
and quantitative predicate, compatible models and dimensions, and acceptable
qualification, immediate and transitive source-operation-policy, and residual-
trust policy.

~~~text
ConstraintResult =
    Satisfied(exact accepted CanonicalTypedLedger<
      exists exact Owner and ResultFamily:
        complete ExactOwnerResultBinding<Owner, ResultFamily>>)
  | Violated(exact authorized accepted-policy completed contradictory
      CanonicalTypedLedger<exists exact Owner and ResultFamily:
        ExactOwnerResultBinding<Owner, ResultFamily>>)
  | Undetermined(exact authorized completed inputs whose accepted semantic
                 bounds do not decide the typed predicate)

ConstraintCheckRecord<D,Q,C> {
  exact DecisionPolicyValidationResult,
  exact ComparisonAlternativeDomainClosureResult<D,Q> and
    ComparisonAlternativeId,
  exact typed constraint C and accepted qualification set,
  exact AssessmentInputPortfolioId,
  exact AssessmentInputCompletenessResult and required
    AssessmentInputUseResultLedger,
  exact complete foreign source-binding ledger and Compiler-owned source
    checked-result ledger,
  exact ConstraintResult,
  exact named consumer, typed constraint-evaluation purpose, freshly checked
    Compiler and foreign policy/contract authorization sets, validation
    contract, and residual trust
}

CheckConstraintResult<D,Q,C>(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact ComparisonAlternativeDomain<Q> and exact
    CompilerResultUseAuthority<CheckedComparisonAlternativeDomain<Q>,
      ComparisonAlternativeDomainClosureRecord<D,Q>>,
  exact ComparisonAlternativeId and typed constraint C,
  exact immutable portfolio,
  exact CompilerResultUseAuthority<CheckedAssessmentInputCompleteness,
    AssessmentInputCompletenessRecord> whose record has an affirmative
    completeness outcome,
  exact CompilerResultUseAuthority<CheckedAssessmentInputUse,
    AssessmentInputUseRecord> for every required input-use result,
  complete canonical typed ledger of
    `ExactOwnerResultBinding<Owner, ResultFamily>` values with exact Owner and
    ResultFamily witnesses for every foreign fact read,
  exact CompilerResultUseAuthorityLedger for every
    Compiler-owned structural value read; a declared preference is authorized
    by the already supplied DecisionPolicy result-use authority and its exact
    policy coordinate,
  exact matching current source-owner capabilities,
  exact NamedConsumer and typed constraint-evaluation purpose,
  every authenticated OwnerOperationPolicyDisposition and transitive source-
    policy closure freshly validated under the Compiler-wide rule for the
    named constraint-evaluation purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedConstraintResult<C>, exact inert ConstraintCheckRecord<D,Q,C>>
~~~

~~~text
ConstraintCheckResult<D,Q,C> = CompilerCheckedResult<
  CheckedConstraintResult<C>, ConstraintCheckRecord<D,Q,C>>
~~~

This result is returned only by `Completed`.

An affirmative premise requires the exact affirmative capability. An exact
fact-retaining negative may satisfy only an explicitly negative constraint.
Compiler cannot coerce a different family, observer, direction, model,
hypothesis context, quantitative dimension, assurance class, owner-defined
source operation policy, or residual-trust root. It cannot discharge or
discard Analysis hypotheses or use any owner capability outside its exact
operation policy.

An unaccepted, mismatched, or use-prohibiting owner operation policy is an
outer authority/policy failure, not a completed `ConstraintResult` and not
evidence that the semantic constraint is false. It yields a typed `Refused` or
other exact attempt audit at its boundary and cannot establish
`Violated`, `DefinitivelyIneligible`, or a closed exclusion. `Violated` requires
an authorized completed contradictory fact whose exact authenticated owner-
policy disposition is valid, every bound policy permits the use, and whose
qualification is accepted by `DecisionPolicy`.

Every inert constraint result retains the complete `ExactOwnerResultBinding`
for every decisive fact. The occurrence-local
`CheckedConstraintResult<C>` separately retains the matching live capabilities.

Direct target re-analysis and property-specific transport may establish the
same exact proposition through different qualifications. Constraint matching
checks proposition meaning before applying the separate qualification policy.

`Violated` is the only ordinary constraint result that can conclusively make a
comparison alternative ineligible. Nonterminal or infrastructure outcomes do
not become violations.

## 6. Typed objectives

Every objective value has both a provenance class and a knowledge shape:

~~~text
ObjectiveProvenance =
    DirectStructural
  | AnalysisOwned
  | EvidenceQualified
  | Stage4BOwnedFactOrValue
  | DeclaredPolicyPreference

ObjectiveKnowledgeShape =
    ExactValue
  | ProvedLowerBound
  | ProvedUpperBound
  | CertifiedIntervalOrSet
  | SymbolicExpressionWithSideConditions
  | MeasuredOrStatisticalEstimate
  | CategoricalValue

ObjectiveValueCheckRecord<D,Q,O> {
  exact DecisionPolicyValidationResult,
  exact ComparisonAlternativeDomainClosureResult<D,Q> and
    ComparisonAlternativeId,
  exact typed objective O and accepted qualification set,
  exact AssessmentInputPortfolioId,
  exact AssessmentInputCompletenessResult and required
    AssessmentInputUseResultLedger,
  exact offered ObjectiveValue, provenance, and knowledge shape,
  exact accepted objective-schema, qualification, association, dimension, and
    comparability facts,
  exact complete foreign source-binding ledger and Compiler-owned source
    checked-result ledger,
  exact named consumer, typed objective-evaluation purpose, freshly checked
    Compiler and foreign policy/contract authorization sets, validation
    contract, and residual trust
}
~~~

Every Analysis judgment, including an
`AnalysisEvidenceDerivedEstimate`, uses `AnalysisOwned`. An Evidence-owned
`EvidenceQualifiedEstimate` uses `EvidenceQualified`. The two provenance tags
are disjoint: equal values, units, or source observations authorize no cast
between them. Each retains its exact owner binding, capability, epistemic shape,
and policy-declared candidate association.

Every value also retains:

- exact subject and candidate-target association;
- semantic, cost, measurement, or endpoint model;
- units and quantitative dimensions;
- environment and procedure when read;
- uncertainty or side conditions;
- hypotheses, availability conditions, and dependencies;
- comparison direction and law; and
- assurance and an exact typed source description: a foreign semantic result
  retains its complete `ExactOwnerResultBinding`; a foreign admitted subject or
  view retains its complete `ExactOwnerAdmittedSubjectBinding`; a Compiler-owned
  structural value retains its complete inert `CompilerCheckedResult`, including
  the body/coordinate, exact output binding, and inherited source-policy/origin
  closure; and a declared preference retains the exact
  `DecisionPolicyValidationResult` and preference coordinate. Every foreign branch includes its
  authenticated owner-policy disposition, transitive source-operation-policy
  dependency closure, inert `OwnerCapabilityRequirement`, and residual trust.

~~~text
CheckObjectiveValue<D,Q,O>(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact ComparisonAlternativeDomain<Q> and exact
    CompilerResultUseAuthority<CheckedComparisonAlternativeDomain<Q>,
      ComparisonAlternativeDomainClosureRecord<D,Q>>,
  exact ComparisonAlternativeId and typed objective O,
  exact immutable portfolio,
  exact CompilerResultUseAuthority<CheckedAssessmentInputCompleteness,
    AssessmentInputCompletenessRecord> whose record has an affirmative
    completeness outcome,
  exact CompilerResultUseAuthority<CheckedAssessmentInputUse,
    AssessmentInputUseRecord> for every required input-use result,
  exact offered ObjectiveValue with its provenance and knowledge shape,
  complete ExactSourceAuthorityBindingLedger for every foreign fact, admitted
    subject, or view read,
  exact CompilerResultUseAuthorityLedger for Compiler-owned
    direct structural values; declared policy preferences use the already
    supplied DecisionPolicy result-use authority and exact policy coordinate,
  exact matching current source-owner capabilities,
  exact NamedConsumer and typed objective-evaluation purpose,
  every authenticated OwnerOperationPolicyDisposition and transitive source-
    policy closure freshly validated under the Compiler-wide rule for the
    named objective-evaluation purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedObjectiveValue<O>, exact inert ObjectiveValueCheckRecord<D,Q,O>>
~~~

~~~text
ObjectiveValueCheckResult<D,Q,O> = CompilerCheckedResult<
  CheckedObjectiveValue<O>, ObjectiveValueCheckRecord<D,Q,O>>
~~~

This result is returned only by `Completed`.

~~~text
ConstraintEvaluationLedger<D,Q> = CanonicalTypedLedger<
  for each exact typed constraint C required by DecisionPolicy:
    exact CompilerRequirementEvaluationEntry<
      CheckedConstraintResult<C>, ConstraintCheckRecord<D,Q,C>>>

ObjectiveEvaluationLedger<D,Q> = CanonicalTypedLedger<
  for each exact typed objective O required by DecisionPolicy:
    exact CompilerRequirementEvaluationEntry<
      CheckedObjectiveValue<O>, ObjectiveValueCheckRecord<D,Q,O>>>
~~~

These are total over the policy's required slots, not merely over successful
checks. A `Checked` entry contains the complete checked result; `Unresolved`
contains the exact outer attempt audit; and `NotAttempted` contains an exact
enclosing-assessment-scoped reason. Only a `Checked` entry may be paired with a fresh
result-use authority. A validated short-circuit may mark a non-checked slot
irrelevant to one exact assessment outcome, but it does not convert that slot
into a checked result or semantic negative.

Both checking operations compare every foreign inert record with its appropriate exact
admitted-subject or checked-result binding, and consume every Compiler-owned
source through its exact `CompilerResultUseAuthority`, including full output-
binding equality and a separately fresh matching Compiler capability. They also check the
capability ABI, candidate and portfolio association, polarity or knowledge
shape, assurance, trust, and immediate plus transitive policy closure. Their
durable portable results contain requirements and bindings but no live
capability; a local input produces the corresponding nonpersistable
`LocalCompilerHandle<T>`.

Different provenance or knowledge shapes are incomparable without an explicit
typed rule that preserves both qualifications. Minimizing a proved upper bound
is not minimizing actual cost. A measured estimate is not an exact semantic
theorem. A missing value is not implicit infinity. An explicit availability
preference produces only a decision under that named policy.

Provider priority, user priority, or another declared preference can be an
exact `DeclaredPolicyPreference`; it must not enter through proposal order or
enumeration ordinal.

## 7. Assessment and completeness

### 7.1 Assessment identity

~~~text
CandidateAssessment<D,Q> {
  exact DecisionPolicy and DecisionPolicyValidationResult,
  exact ComparisonAlternativeDomain<Q> and
    ComparisonAlternativeDomainClosureResult<D,Q>,
  exact candidate_coordinate: CompilerValueCoordinate<Candidate> and
    comparison_alternative_coordinate:
      CompilerValueCoordinate<ComparisonAlternative>,
  exact ExactCompilerValueRef<AssessmentInputPortfolio>,
  exact AssessmentInputCompletenessResult,
  exact QualificationResolutionLedgerResult<D> and qualification set fixed by the
    comparison alternative,
  exact accepted QualificationSupportBinding and CandidateQualificationResult
    values plus admission/transition support ledger read through that resolution,
  exact AssessmentInputUseEvaluationLedger<D,Q>,
  exact CompilerLegalityResult,
  exact Analysis and peer-owner results actually read by Checked entries,
  exact complete ExactSourceAuthorityBindingLedger,
  exact ConstraintEvaluationLedger<D,Q>,
  exact ObjectiveEvaluationLedger<D,Q>,
  exact evaluation trace and decisive dependency closure,
  exact named consumer and typed candidate-assessment purpose,
  exact freshly checked policy/contract authorization set,
  exact transitive source-operation-policy dependency closure,
  exact residual-trust closure,
  assessment_outcome
}
~~~

`AssessmentId` is keyed by `ComparisonAlternativeId`, not merely by
`CandidateId`:

~~~text
AssessmentId = Id(exact CandidateAssessment<D,Q>)

CandidateAssessmentResult<D,Q> = CompilerCheckedResult<
  CheckedCandidateAssessment<D,Q>, CandidateAssessment<D,Q>>
~~~

In the portable untainted lane, the durable `CandidateAssessment` and
`AssessmentId` contain only inert exact results, identities, traces, and
dependency closures. A tainted assessment uses the corresponding
`LocalCompilerHandle<CandidateAssessment<D,Q>>` and every downstream local handle
required by the Compiler-wide rule; it is neither durable nor portable.
Assessment authority is
created only by an occurrence-local operation:

~~~text
CheckCandidateAssessment<D,Q>(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact ComparisonAlternativeDomain<Q> and exact CompilerResultUseAuthority<
    CheckedComparisonAlternativeDomain<Q>,
    ComparisonAlternativeDomainClosureRecord<D,Q>>,
  exact ComparisonAlternativeId,
  exact immutable AssessmentInputPortfolio,
  exact CompilerResultUseAuthority<CheckedAssessmentInputCompleteness,
    AssessmentInputCompletenessRecord>,
  exact QualificationResolutionLedger<D> and exact CompilerResultUseAuthority<
    CheckedQualificationResolution<D>, QualificationResolutionLedger<D>>,
  exact accepted QualificationSupportBinding values and one exact
    CompilerResultUseAuthority<QualifiedCandidate,
      CandidateQualificationRecord> for every accepted qualification support
    result read,
  exact CompilerResultUseAuthority<
    CheckedCompilerLegality<CompilerLegalityCompletedOutcome>,
    CompilerLegalityRecord>,
  exact AssessmentInputUseEvaluationLedger<D,Q>,
  exact ConstraintEvaluationLedger<D,Q>,
  exact ObjectiveEvaluationLedger<D,Q>,
  exact complete ExactSourceAuthorityBindingLedger for every foreign source
    retained by the ledgers, with separately supplied fresh foreign source
    capabilities only for sources actually read by Checked entries,
  one exact CompilerResultUseAuthority<
    CheckedAssessmentInputUse, AssessmentInputUseRecord> for every Checked
    input-use entry in the ledger, with matching upstream owner capabilities under their
    exact owner operation policies,
  for every Checked constraint entry in the ledger, one exact
    CompilerResultUseAuthority<CheckedConstraintResult<C>,
      ConstraintCheckRecord<D,Q,C>> for its exact typed C,
  for every Checked objective entry in the ledger, one exact
    CompilerResultUseAuthority<CheckedObjectiveValue<O>,
      ObjectiveValueCheckRecord<D,Q,O>> for its exact typed O,
  exact NamedConsumer and typed candidate-assessment purpose,
  every exact inherited OwnerOperationPolicyDisposition and transitive source-
    policy closure,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose,
  exact evaluation trace and decisive dependency closure, including an exact
    DecisionPolicy-approved irrelevance proof for every non-checked entry
    omitted by a terminal short-circuit)
  -> CompilerValidationAttemptOutcome<
       CheckedCandidateAssessment<D,Q>,
       exact inert CandidateAssessment<D,Q>>
~~~

Every supplied foreign source capability must match the corresponding typed
variant in the complete `ExactSourceAuthorityBindingLedger`, including its
polarity or admitted-subject facts, authenticated owner-policy disposition,
complete transitive source-policy closure, assurance, trust, candidate, and
portfolio association. Every Compiler-owned input must instead arrive through
its exact `CompilerResultUseAuthority`; the complete checked-result body,
portable ID or owner-local coordinate, output binding, fresh capability, named
consumer, typed purpose, and conjunctive immediate/transitive authorization
must all match. The resulting `CandidateAssessment` retains every complete
inert `CompilerCheckedResult` it read, the total evaluation ledgers, and every
exact attempt or not-attempted blocker, never only a record ID or capability.
The assessment operation freshly reauthorizes every inherited bound policy or
explicit no-policy contract for its own named consumer and assessment purpose;
authority granted for input use, constraint checking, or objective evaluation
does not widen to assessment.
These capabilities are live invocation inputs and live-result dependencies
only; the inert checked-result envelopes and authorization records enter the
assessment, but no capability enters `CandidateAssessment`, `AssessmentId`, a
portfolio, a replay bundle, or another content identity.

It is computed only after the candidate-indexed portfolio body, separate
completed completeness result, total per-requirement evaluation ledgers, and
decisive dependency trace exist. A portable completion returns the exact assessment body and matching
`AssessmentId` before minting the fresh capability. A local completion returns
the exact local assessment body and its value-derived nonpersistable handle
under the Compiler-wide owner-local identity rule. The live capability retains the
exact returned result, named consumer, typed purpose, freshly checked
policy/contract authorization set, and all source-policy dependencies. U/C/R/M/F return only
the exact attempt audit, no assessment result, and no assessment capability. No upstream result may
name this future ID. Multiple comparison alternatives for one candidate may
read the same immutable portfolio while binding different exact qualification
sets and therefore remain different assessments.

Assessment outcomes are:

~~~text
Eligible(exact satisfied constraint closure and sufficient objective facts)
DefinitivelyIneligible(nonempty exact violated-constraint or illegality facts)
Undetermined(exact non-checked evaluation entries, completed semantic
             indeterminacy, incomplete-portfolio facts, or other blockers)
~~~

One exact authorized violated constraint or problem-local illegality result may
conclusively exclude an alternative even if other unused values are
unavailable, but only when the exact validated `DecisionPolicy` short-circuit
rule and decisive dependency closure prove every non-checked entry irrelevant
to that exclusion. An owner-policy mismatch, outer failure audit, or
`NotAttempted` entry never supplies the excluding fact. An eligible alternative
requires affirmative portfolio completeness, every required input and
constraint check, and enough checked objective information for the requested
comparison. Otherwise the completed assessment is `Undetermined`, or the
candidate-assessment operation itself returns an outer attempt audit if its own
invocation cannot be checked.

### 7.2 Total `AssessmentLedger<D,Q>`

`AssessmentLedger<D,Q>` is a total canonical map over every and only
`ComparisonAlternativeId` in exact `Q`. Every completed assessment entry
contains the exact complete `CandidateAssessmentResult<D,Q>`, including an
`Undetermined` outcome, its portable record coordinate or owner-local handle,
and exact Compiler output binding. Only an outer U/C/R/M/F or absent checking
attempt uses a `NotAssessed` entry with exact blockers and audit references.
Its identity covers the complete map rather than only outcome tags:

~~~text
CandidateAssessmentBlocker<D,Q> =
    OuterAttempt(exact CompilerAttemptAudit<
      CheckedCandidateAssessment<D,Q>, CandidateAssessment<D,Q>>)
  | NotAttempted(exact CompilerNotAttemptedRecord<
      CheckedCandidateAssessment<D,Q>, CandidateAssessment<D,Q>> whose
      enclosing association names this exact
        CompilerValueCoordinate<ComparisonAlternative>)

AssessmentLedgerEntry<D,Q> =
    Assessed(exact CandidateAssessmentResult<D,Q>)
  | NotAssessed(exact CandidateAssessmentBlocker<D,Q>)

AssessmentLedger<D,Q> {
  exact comparison_alternative_domain_coordinate:
    CompilerValueCoordinate<ComparisonAlternativeDomain<Q>>,
  exactly one canonical AssessmentLedgerEntry<D,Q> for every
    CompilerValueCoordinate<ComparisonAlternative> in Q,
  every entry contains its exact blockers and retained source facts,
  exact complete source-policy and residual-trust closure
}

AssessmentLedgerId = Id(exact AssessmentLedger<D,Q>)
~~~

Decision-relative assessment completeness does not require unused objectives
for an already conclusively ineligible alternative. It does require enough
terminal facts to classify or compare every alternative that could affect the
requested optimum, Pareto frontier, representative, or `NoEligible` result.
The separate qualification-resolution ledger continues to cover every member
of semantic `D`, including candidates that cannot yet be mapped to an accepted
comparison alternative. Operational absence is never semantic ineligibility.

`CheckedAssessmentClosure<D,Q>` authenticates this exact sufficiency. A partial
ledger, wrong-domain assessment, portfolio mutation, or hidden input cannot
establish it.

The closure itself has an inert, fully bound result:

~~~text
CertificateDecisionPayload<D,Q> =
    CertifiedBest(
      exact DecisionPolicy-relative eligible optimal equivalence class in Q,
      exact eligibility support for every class member,
      exact policy-relative eligibility/exclusion/irrelevance and comparison
        coverage for every other member of Q, proving none is better)
  | CertifiedCompletePareto(
      exact canonical eligible complete frontier in Q,
      exact eligibility support for every frontier member,
      exact policy-relative eligibility/exclusion/irrelevance and dominance
        coverage for every other member of Q)
  | CertifiedNoEligible(exact infeasibility claim over Q and its projection to D)

AssessmentSufficiencyBasis<D,Q> =
    CompleteAssessment(
      exact terminal or policy-approved irrelevant disposition for every member
        of Q that could affect the requested decision)
  | ExternalCertificate(
      exact independently checked affirmative optimality, complete-Pareto, or
        infeasibility certificate proposition over exactly D and Q,
      exists exact CertificateOwner and CertificateResultFamily: exact foreign
        certificate result whose completed owner-defined qualified outcome
        affirmatively establishes that exact proposition, and its
        ExactOwnerResultBinding<CertificateOwner, CertificateResultFamily>,
      exact CertificateDecisionPayload<D,Q>, deterministic extraction coordinate,
      and certificate-to-policy/domain correspondence and coverage facts)

AssessmentClosureRecord<D,Q> {
  exact DecisionPolicy and DecisionPolicyValidationResult,
  exact ComparisonAlternativeDomain<Q> and
    ComparisonAlternativeDomainClosureResult<D,Q>,
  exact AssessmentLedger<D,Q>,
  exact CandidateAssessmentResult<D,Q> for every Assessed entry,
  exact AssessmentSufficiencyBasis<D,Q>,
  exact CompilerCheckedResultLedger for every Compiler-owned terminal or
    irrelevance fact read outside an Assessed entry,
  exact terminal-exclusion foreign results and complete source-binding ledger,
  exact affirmative totality and decision-sufficiency fact,
  exact named consumer, typed assessment-closure purpose, freshly checked
    Compiler and foreign policy/contract authorization sets, validation
    contract, source-policy closure, and residual trust
}

AssessmentClosureResult<D,Q> = CompilerCheckedResult<
  CheckedAssessmentClosure<D,Q>, AssessmentClosureRecord<D,Q>>
~~~

Authority for assessment closure is created only by:

~~~text
CheckAssessmentClosure<D,Q>(
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact ComparisonAlternativeDomain<Q> and exact CompilerResultUseAuthority<
    CheckedComparisonAlternativeDomain<Q>,
    ComparisonAlternativeDomainClosureRecord<D,Q>>,
  exact AssessmentLedger<D,Q>,
  exact AssessmentSufficiencyBasis<D,Q>,
  one exact CompilerResultUseAuthority<
    CheckedCandidateAssessment<D,Q>, CandidateAssessment<D,Q>> for every
    Assessed entry,
  exact CompilerResultUseAuthorityLedger for every Compiler-owned terminal or
    irrelevance fact used to short-circuit an Assessed or NotAssessed entry,
  exact owner-authorized terminal-exclusion records, complete
    ExactSourceAuthorityBindingLedger, and separately supplied fresh matching
    foreign capabilities required by the ledger,
  for ExternalCertificate only: the exact CertificateOwner and
    CertificateResultFamily, certificate record, and
    ExactOwnerResultBinding<CertificateOwner, CertificateResultFamily> whose
    completed qualified outcome is the owner-defined affirmative result for the
    exact retained certificate proposition, plus a separately supplied fresh
    matching affirmative owner capability, exact certificate-
    checker/correspondence material, exact CertificateDecisionPayload<D,Q> and
    deterministic extraction coordinate, and fresh
    authorization under every immediate/transitive source policy for the named
    closure purpose,
  exact NamedConsumer and typed assessment-closure purpose,
  every exact authenticated OwnerOperationPolicyDisposition and transitive
    source-policy closure freshly validated under the Compiler-wide rule for
    the named closure purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedAssessmentClosure<D,Q>, exact inert AssessmentClosureRecord<D,Q>>
~~~

The check verifies total exact coverage of `Q`, all candidate, portfolio,
policy, assessment, polarity, assurance, and trust coordinates, every terminal
exclusion authorization, every complete Compiler-owned result and fresh use
authority used by a short-circuit, and the decisive dependency closure. Missing or
mismatched authority and owner-policy prohibition remain unresolved or
refused; they cannot close the ledger or exclude an alternative. In the fully
portable lane the durable assessment ledger contains no live capabilities; a
local ledger and closure result use nonpersistable handles. The completed
closure record retains every complete inert checked-result envelope it read;
the occurrence-local closure capability separately preserves every exact
source-policy, origin, and dependency requirement used to establish it.
For `ExternalCertificate`, only the exact owner-defined affirmative completed
certificate outcome and its matching fresh affirmative capability can establish
the retained certificate proposition and payload. A negative certificate
outcome, invalid-certificate result, or U/C/R/M/F attempt cannot form an
`ExternalCertificate` basis, close assessment, or support a decision.
`Assessed(Undetermined(...))` and `NotAssessed(...)` remain unresolved unless
the `CompleteAssessment` branch applies an exact policy-defined
decision-sufficiency short-circuit proving that the entry cannot affect the
requested closed claim, or the `ExternalCertificate` branch independently
covers that exact entry and the requested D/Q claim. Neither branch silently
converts an unresolved entry to ineligibility. Certificate unsupportedness,
refusal, malformation, mismatch, incomplete coverage, or checker failure mints
no assessment-closure result.

## 8. Comparison, Pareto, ties, and representative choice

The exact `DecisionPolicy` selects one versioned comparison:

- lexicographic comparison over a typed objective vector;
- constrained single-objective minimization or maximization;
- dimension-checked weighted aggregation with exact normalization and weights;
- complete Pareto comparison under exact component orders; or
- another closed comparator with an exact order and completeness contract.

Provider order, proposal order, domain ordinal, scheduling, cache state, and
discovery time are never implicit objectives.

For a closed total comparison the result retains:

~~~text
OptimalEquivalenceClass<CompilerValueCoordinate<ComparisonAlternative>>
CanonicalRepresentative<CompilerValueCoordinate<ComparisonAlternative>>
SelectedCandidate(CompilerValueCoordinate<Candidate>)
SelectedQualification(CompilerValueCoordinate<Qualification>)
  or accepted CanonicalQualificationSet coordinate
~~~

The representative policy returns one exact comparison alternative and its
unique projected candidate only after objective comparison establishes the
optimal equivalence class. Its default canonical candidate choice is the
minimum `CompilerValueCoordinate<Candidate>` under the portable order or the
same-owner/generation local order; when several tied comparison alternatives
project to that candidate, the exact qualification-resolution and
representative order selects one member of `Q`. This does not erase the
equivalence class. If
priority matters, it is an explicit objective and therefore changes the
comparison rather than the tie mechanism.

For Pareto policy, the authoritative result is the complete canonical
nondominated set in `Q`. Choosing one frontier member requires a separate
explicit totalizing policy and creates a distinct decision claim. An
incomplete, uncertain, or partial order cannot silently become a closed single
winner.

## 9. Closed decisions and open reports

### 9.1 Decision identity binds both domains

~~~text
DecisionDerivationBasis<D,Q> =
    AssessmentDerived(
      exact AssessmentClosureResult<D,Q> whose
        AssessmentSufficiencyBasis is CompleteAssessment,
      exact deterministic comparator, Pareto, tie, and representative
        recomputation trace over every decision-relevant Checked assessment)
  | CertificateDerived(
      exact AssessmentClosureResult<D,Q> whose
        AssessmentSufficiencyBasis is ExternalCertificate,
      exact CertificateDecisionPayload<D,Q>, certificate proposition, foreign
        certificate result and, for some exact CertificateOwner and
        CertificateResultFamily, its complete
        ExactOwnerResultBinding<CertificateOwner, CertificateResultFamily>
        carrying the owner-defined affirmative completed outcome for that exact
        proposition and payload,
      exact certificate-to-D/Q/DecisionPolicy correspondence and coverage,
      exact extraction and representative/optional-totalization trace that uses
        only data established by the certified payload)

ComparisonAlternativeDecisionSupport<D,Q> =
    AssessmentSupported(
      exact ComparisonAlternativeId,
      exact CandidateAssessmentResult<D,Q> whose outcome is Eligible,
      exact AssessmentId and assessment-derived comparison-trace coordinate)
  | CertificateSupported(
      exact ComparisonAlternativeId,
      exact affirmative foreign certificate-result coordinate,
      exact CertificateDecisionPayload<D,Q> member-support coordinate,
      and exact correspondence coordinate)

CompilerDecision<D,Q> {
  exact TransformProblem and TransformProblemValidationResult,
  exact DecisionPolicy and DecisionPolicyValidationResult,
  exact AlternativeResolutionCoverageRecordResult when an alternative scope is
    read,
  exact CandidateDomain<D> and CandidateDomainClosureResult<D>,
  exact QualificationResolutionLedger<D> and
    QualificationResolutionLedgerResult<D>,
  exact ComparisonAlternativeDomain<Q> and
    ComparisonAlternativeDomainClosureResult<D,Q>,
  exact total AssessmentLedger<D,Q> and
    AssessmentClosureResult<D,Q>,
  exact DecisionDerivationBasis<D,Q>,
  exact CandidateAssessmentResult<D,Q> values for every Assessed entry and
    complete typed Compiler checked-result
    ledger for every decisive legality, qualification, constraint, objective,
    occurrence-use, resolution, and exclusion input,
  exact comparison, Pareto, tie, and representative policy coordinates inside
    the retained DecisionPolicyValidationResult,
  Best {
    optimal_equivalence_class,
    canonical_representative_comparison_alternative_coordinate:
      CompilerValueCoordinate<ComparisonAlternative>,
    canonical_representative_candidate_coordinate:
      CompilerValueCoordinate<Candidate>,
    exact selected_qualification_set_coordinate:
      CompilerValueCoordinate<CanonicalQualificationSet>,
    exact ComparisonAlternativeDecisionSupport<D,Q> for the selected member
  }
    | CompletePareto {
        canonical_frontier,
        exactly one ComparisonAlternativeDecisionSupport<D,Q> for every
          frontier member,
        exact optional totalization
      }
    | NoEligible { exact terminal exclusion or infeasibility basis },
  exact residual_trust_closure,
  exact complete decisive_source_authority_binding_ledger,
  exact transitive_source_operation_policy_dependency_closure
}
~~~

`DecisionId` binds both semantic `D` and assessment-unit `Q`. It never replaces
one with the other.

~~~text
DecisionId = Id(exact CompilerDecision<D,Q>)

CompilerDecisionResult<D,Q> = CompilerCheckedResult<
  QualifiedCompilerDecision<D,Q>, CompilerDecision<D,Q>>

CompilerDecisionAttemptOutcome<D,Q> = CompilerValidationAttemptOutcome<
  QualifiedCompilerDecision<D,Q>, CompilerDecision<D,Q>>
~~~

Decision authority is created only by an occurrence-local check:

~~~text
CheckCompilerDecision<D,Q>(
  exact TransformProblem and exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact CompilerResultUseAuthority<
    AlternativeResolutionCoverage, AlternativeResolutionCoverageRecord> when
    the claim reads an alternative scope,
  exact CandidateDomain<D> and exact CompilerResultUseAuthority<
    CheckedCandidateDomain<D>, CandidateDomainClosureRecord<D>>,
  exact QualificationResolutionLedger<D> and exact CompilerResultUseAuthority<
    CheckedQualificationResolution<D>, QualificationResolutionLedger<D>>,
  exact ComparisonAlternativeDomain<Q> and exact CompilerResultUseAuthority<
    CheckedComparisonAlternativeDomain<Q>,
    ComparisonAlternativeDomainClosureRecord<D,Q>>,
  exact AssessmentLedger<D,Q> and exact CompilerResultUseAuthority<
    CheckedAssessmentClosure<D,Q>, AssessmentClosureRecord<D,Q>>,
  one exact CompilerResultUseAuthority<
    CheckedCandidateAssessment<D,Q>, CandidateAssessment<D,Q>> for every
    Assessed entry,
  exact CompilerResultUseAuthorityLedger for every other
    decisive Compiler-owned resolution, occurrence-use, legality,
    qualification, constraint, objective, or exclusion result,
  exact separately supplied foreign admission, transition, relation, and
    exclusion capabilities matched to the decisive source-binding ledger,
  exact optional affirmative external optimality, complete-Pareto, or
    infeasibility certificate records, complete source bindings, and separately
    supplied fresh matching affirmative owner
    capabilities when CertificateDerived is used; the exact certificate
    proposition, payload, D/Q/policy correspondence, and coverage must equal
    those retained by the assessment closure and decision basis,
  exact DecisionDerivationBasis<D,Q>,
  exact CompilerDecision<D,Q>,
  every complete ExactSourceAuthorityBindingLedger entry used by the decision,
  exact NamedConsumer and typed compiler-decision purpose,
  every exact authenticated OwnerOperationPolicyDisposition and transitive
    source-policy closure freshly validated under the Compiler-wide rule for
    the named decision purpose)
  -> CompilerDecisionAttemptOutcome<D,Q>
~~~

Only `Completed` returns the exact portable decision body and matching
`DecisionId`, or the exact local decision body and its value-derived
nonpersistable handle under the Compiler-wide owner-local identity rule,
creates its exact Compiler-owned checked-result binding, and mints
`QualifiedCompilerDecision<D,Q>` bound to that exact result and binding. U/C/R/M/F
return only the exact attempt audit, no checked decision result, and no
capability. The check requires exact agreement among the
two domain identities, every closure and ledger, every result used by the
claim, its selected representative or complete set, and the entire residual-
trust and source-policy closure. It revalidates the exact `DecisionPolicy` basis,
polarity, assurance, residual-trust, and owner-operation-policy acceptance rules
and the complete decisive source-authority-binding ledger against every
decisive capability, including terminal alternative-resolution
and candidate- or qualification-exclusion facts that kept an item out of `D` or
`Q`; aggregate closure capabilities cannot hide or weaken those dependencies.
The decision check is branchwise. `AssessmentDerived` requires the closure's
exact `CompleteAssessment` basis and deterministically recomputes the declared
typed comparison, Pareto relation, tie class, and representative rule from
exact `Q`, the decision-relevant Checked assessments, and the validated policy.
Those recomputed Compiler values require no ambient or persisted live
capability. `CertificateDerived` instead requires the closure's exact
`ExternalCertificate` basis, rechecks the exact affirmative certificate
statement, complete foreign result binding and owner-defined affirmative
qualified outcome, D/Q/policy correspondence, and coverage under a freshly
matched affirmative owner capability and all source policies for the distinct decision
purpose, and extracts only the matching `CertificateDecisionPayload<D,Q>`. It
does not reconstruct missing objective values or turn an unresolved assessment
into eligibility or exclusion. A Best representative is selected only from the
certified optimal equivalence class; a Pareto totalization is applied only when
the certified frontier payload supplies every datum required by that exact
rule; `CertifiedNoEligible` yields only the matched infeasibility claim.
`AssessmentDerived` requires `AssessmentSupported` for every selected or
frontier member, bound to that member's exact completed `Eligible` assessment
and the recomputed comparison trace. `CertificateDerived` requires
`CertificateSupported` for every such member, bound to the exact certificate
result, certified-payload member-support coordinate, and correspondence; the
mere existence of an assessment, including an `Undetermined` assessment, can
never replace that support. Neither branch may widen the other.
Missing, stale, mismatched, or policy-denied
inputs yield an unresolved, refused, malformed, or checker-failure outcome as
appropriate; they never justify an exclusion, optimum, frontier, or
`NoEligible` claim. In the fully portable lane the durable decision contains
only inert identities and records and serializes no capability. Replay and
target-reconstruction material are separate policy-governed bundles; neither
is silently embedded in the decision. A local decision has only
`LocalCompilerHandle<CompilerDecision<D,Q>>` and is
nonpersistable.

Closed claims state their exact candidate-domain scope:

~~~text
BestInSubmittedCandidateSet<D,Q>
BestInResolvedSubmittedScope<S,D,Q>
BestInEnumeratedClosedDomain<D,Q>
BestInCertifiedSymbolicDomain<D,Q>
CompleteParetoFrontierIn<D,Q>
NoEligibleCandidateIn<D,Q>
~~~

`Best` requires closed `D`, total terminal qualification resolution over `D`,
closed derived `Q`, and either an `AssessmentDerived` basis with every
decision-relevant comparison fact checked or a `CertificateDerived` basis with
an exact `CertifiedBest` payload over every member of `Q`. `CompletePareto`
similarly requires either complete assessment-derived comparison or an exact
`CertifiedCompletePareto` payload; neither certificate branch implies missing
assessment identities.

`NoEligibleCandidateIn<D,Q>` requires closure of both `D` and `Q`. For every
candidate in `D`, it additionally requires one complete basis covering the
exact closed domains:

- a completed `DefinitivelyQualificationIneligible` result under the exact
  qualification policy; or
- every comparison alternative derived from that candidate in `Q`
  definitively ineligible through exact illegality or violated-constraint
  facts; or
- an independently checked infeasibility certificate over exactly those
  already closed `D,Q` domains.

No closed `NoEligible` is legal while any unresolved declared alternative,
candidate-domain membership, target admission or transition relation,
qualification resolution, or comparison-domain member prevents exact closure
of `D` or `Q`. Neither policy-approved irrelevance nor an assessment/infeasibility
certificate may replace that pre-`Q` closure or total terminal qualification
resolution. Once `D` and `Q` are closed, an exact policy-approved irrelevance
proof or independently checked infeasibility certificate may cover only a
nondecisive post-`Q` assessment/dependency slot--such as legality, a constraint,
portfolio input, objective, Analysis result, or peer-owner input--without
converting it into ineligibility. Unsupportedness, cannot-answer, refusal,
malformation, missing objective data, incomplete search, and checker failure
themselves can never be recast as ineligibility.

### 9.2 Open reports

Open or incomplete work may return:

~~~text
QualifiedFeasibleCandidate(
  exact inert CandidateId, ComparisonAlternativeId, AssessmentId,
    qualification records, and inert OwnerCapabilityRequirement values)

NondominatedInAssessedSubset(
  exact comparison-alternative subset and qualifications)

IncompleteSearchReport(
  exact frozen progress-accounting descriptor, which is not by itself an
    authenticated search- or run-occurrence history,
  retained inert CandidateIds, qualification records, AssessmentIds, and
    inert OwnerCapabilityRequirement values,
  unresolved alternatives, qualifications, portfolios, or assessments,
  exact blockers)
~~~

These reports mint no candidate-domain closure, comparison-domain closure,
complete Pareto, optimality, or `NoEligible` capability. An empty heuristic
result is an incomplete report or empty observed subset, never a negative over
an unstated universe. `BestAmongCompletedAssessments` may be an explicitly
subset-relative report; it is not `BestInDomain`.

Report payloads contain no live candidate, qualification, or assessment
capability. A same-process API may return independently owned matching live
capabilities alongside an inert report without putting them in its identity.
If any payload, retained attempt-audit, or alternative-blocker identity is owner-local, the report itself uses a
`LocalCompilerHandle<CompilerOpenReportRecord<R>>` and is nonpersistable and
non-public.

Report authority is checked explicitly:

~~~text
CompilerOpenReportRecord<R> {
  exact inert report body R and claimed subset/audit-record accounting scope,
  exact DecisionPolicy and DecisionPolicyValidationResult,
  exact CompileRunRequest and CompileRunRequestValidationResult when read,
  exact complete source-binding ledgers and CompilerCheckedResultLedger for
    every qualified subset or closure result read,
  exact CompilerAttemptAuditLedger and CompilerNotAttemptedRecordLedger, plus
    exact AlternativeResolutionBlocker values, for every recorded non-result
    or skipped slot claimed by R,
  exact named consumer and typed open-report purpose,
  exact total transitive source-policy closure and freshly checked
    policy/contract authorization set,
  exact validation contract and residual trust
}

CheckOpenCompilerReport<R>(
  exact inert report body R and claimed subset/audit-record accounting scope,
  exact DecisionPolicy and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact relevant foreign source-binding ledgers and separately supplied fresh
    matching foreign capabilities,
  exact CompilerResultUseAuthorityLedger for every
    Compiler-owned qualified subset or closure result read,
  exact CompilerAttemptAuditLedger and CompilerNotAttemptedRecordLedger, plus
    exact AlternativeResolutionBlocker values, for every recorded non-result
    or skipped slot claimed by R; these receive no result-use authority,
  when the claim reads a run request, job descriptor, progress-accounting
    scope, or bounded exploration declaration:
    exact CompileRunRequest and exact CompilerResultUseAuthority<
      CheckedCompileRunRequest, CompileRunRequestValidationRecord>,
  exact NamedConsumer and typed open-report purpose,
  every exact inherited OwnerOperationPolicyDisposition and transitive source-
    policy closure,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose)
  -> CompilerValidationAttemptOutcome<
       QualifiedCompilerOpenReport<R>,
       exact inert CompilerOpenReportRecord<R>>

CompilerOpenReportResult<R> = CompilerCheckedResult<
  QualifiedCompilerOpenReport<R>, CompilerOpenReportRecord<R>>
~~~

The check totally matches every report field to the exact qualified subset and
audit-record-relative accounting scope it claims. It validates each attempt
audit or alternative blocker under
its exact Compiler, foreign-owner, nonattempt, or search-progress branch,
including canonical integrity, operation/alternative association, and
nonauthoritative scope, without treating it as a checked result or reproducing
its failure. This establishes only what the exact supplied audit or blocker
record says and how the enclosing report accounts for its slot; it does not
authenticate that an attempt, failure, search step, or run-history occurrence
happened. Such an actual-history claim requires a separate owner-authenticated
occurrence or log result, which this Stage 4A target does not define. A request-relative report without a fresh matching
`CheckedCompileRunRequest` is `Refused` or `Malformed`; it is not an open-report
capability. Reports independent of a run-request or progress-accounting scope omit that conditional operand
but still require the exact policy and all source-owner authority they read.
Only `Completed` mints the scoped report capability, which remains strictly
weaker than any closed-domain decision capability. Its returned record result
and fresh capability retain the exact named consumer, typed purpose, complete
source-policy closure, and freshly checked authorization set; authority granted
for assessment, decision, persistence, or another report does not widen to this
operation.

### 9.3 Outer qualified outcomes

Compiler preserves:

~~~text
Unsupported(requested family, model, domain, certificate, or comparator)
CannotAnswer(missing named semantic input, resolution, or closure basis)
Refused(missing authority or prohibited policy)
Malformed(request, alternative scope, portfolio, domain, identity, cycle,
          or framing defect)
CheckerFailure(operational failure; no decision conclusion)
~~~

No outer non-result mints an affirmative, negative, eligibility, optimality, or
`NoEligible` capability.

## 10. Decision authority

Representative live capabilities are:

~~~text
CheckedQualificationResolution<D>
CheckedComparisonAlternativeDomain<Q>
CheckedAssessmentInputCompleteness
CheckedAssessmentInputUse
CheckedConstraintResult<C>
CheckedObjectiveValue<O>
CheckedCandidateAssessment<D,Q>
CheckedAssessmentClosure<D,Q>
QualifiedCompilerDecision<D,Q>
QualifiedCompilerOpenReport<R>
~~~

`QualifiedCompilerDecision<D,Q>` establishes only its exact scoped comparison
claim. It never mints, serializes, widens, or substitutes for:

- `AdmittedProtocol`;
- a checked transition or property judgment;
- property transport;
- a Stage 4B fact or value; or
- consumer reliance.

A same-process API may return independently owned live capabilities alongside
the decision. No capability conversion occurs. In the portable untainted lane,
a durable decision record contains only exact inert identities and records;
replay or target-reconstruction material is retained separately under its own
consumer, purpose, and policy authorization. The owner-local lane has only a nonpersistable
`LocalCompilerHandle<CompilerDecision<D,Q>>`.

## 11. Cold replay and persistence

Persistence is optional and requires a named independent consumer, expensive
reconstruction, real cross-process trust separation, or another exact
retention need.

No value or dependency carrying a `LocalCompilerHandle`, upstream owner-local
handle, or owner-private nonserializable reference is eligible for persistence,
a replay bundle, a persistent cache key, public disclosure, or exact cold
replay. An authorized confidential rerun creates a new upstream and Compiler
local-handle chain.

Creating, retaining, disclosing, or looking up a Compiler replay bundle or
persistent cache entry requires the exact admitted
`CompilerResultOperationPolicy` for every Compiler-owned result operation, the
exact `DecisionPolicy` when the material belongs to a decision or report, and a freshly
validated disposition for every immediate and transitive source of any result
or material that would enter it, even when that source's material is not
retained. Every bound policy must permit this named consumer and purpose; every
explicit no-policy disposition must match a freshly admitted owner capability-
contract and ABI preimage. A mismatch, prohibition, or refusal creates no
entry; when every bound source policy explicitly permits it, an exact redaction or
separately authorized confidential store may retain only the allowed fields.
If required reconstruction material cannot be retained, no replay bundle is
created. Merely recording a source policy in a bundle or key is not persistence
authorization, and Compiler never widens one.

The two replay products have complete canonical bodies rather than names with
implicit ambient state:

~~~text
CompilerDecisionReplayReconstructionMaterial<D,Q> =
  exact canonical closed typed product of every unconditional field and every
  explicitly tagged Present(exact value) | NotRead conditional field in the
  decision inventory below

CompilerReplayBundle<D,Q> {
  reconstruction_material:
    exact CompilerDecisionReplayReconstructionMaterial<D,Q>,
  expected_final_result: exact CompilerDecisionResult<D,Q>,
  exact NamedConsumer and typed compiler-decision-replay purpose,
  exact inert retention/disclosure policy coordinates and checked
    authorization records
}

CompilerReplayBundleId<D,Q> = H(
  "zkc/compiler-decision-replay-bundle",
  CompilerSemanticRegimeId,
  CanonicalEncode_regime(exact CompilerReplayBundle<D,Q>))

CompilerOpenReportReplayReconstructionMaterial<R> =
  exact canonical closed typed product of every unconditional field and every
  explicitly tagged Present(exact value) | NotRead conditional field in the
  open-report inventory below

CompilerOpenReportReplayBundle<R> {
  reconstruction_material:
    exact CompilerOpenReportReplayReconstructionMaterial<R>,
  expected_final_result: exact CompilerOpenReportResult<R>,
  exact NamedConsumer and typed compiler-open-report-replay purpose,
  exact inert retention/disclosure policy coordinates and checked
    authorization records
}

CompilerOpenReportReplayBundleId<R> = H(
  "zkc/compiler-open-report-replay-bundle",
  CompilerSemanticRegimeId,
  CanonicalEncode_regime(exact CompilerOpenReportReplayBundle<R>))
~~~

Both bodies are portable-only, contain no live capability or owner-local
handle, and contain exactly the fields enumerated by their inventories--no
ambient registry, default, policy, or reconstruction input is implicit. The
`expected_final_result` is the complete checked result: record body, portable
coordinate, and Compiler-created output binding, not only the semantic decision
or report body.

A `CompilerReplayBundle<D,Q>` is the decision-replay bundle. Its canonical
reconstruction material retains, when read
by the exact decision:

- the exact `CompilerAdmissionCapabilityContract` values, bootstrap admission
  contracts/manifests, `CompilerSemanticCapabilityContract`, and
  `CompilerResultOperationPolicy`, including their exact admitted-subject
  bindings, admission preimages, ABI/binding schemas, and reconstruction
  material;
- exact `TransformProblem` and `DecisionPolicy`, including every accepted
  owner-policy-disposition schema and exact transitive source-policy dependency
  closure;
- exact `TransformProblemValidationResult` and
  `DecisionPolicyValidationResult`, plus the optional
  `CompileRunRequestValidationResult`, with every Compiler semantic-regime,
  validation-contract, owner schema/capability-contract, source-binding,
  policy, trust, admission, and reconstruction preimage required to reproduce
  them;
- exact `CandidateDomainPolicyValidationResult` and its Compiler semantic-
  regime, validation-contract, problem/policy, and reconstruction preimages;
- for every concrete source disposition, the complete bound policy preimage or
  exact owner capability-contract and ABI preimage that explicitly declares no
  policy, together with its reconstruction/admission manifest;
- the run request, exploration space, proposal scope, and total alternative-
  resolution ledger only when needed by the exact scope claim, together with
  every required `ProposalOccurrenceUseRecord` and its exact validation/
  reconstruction material, plus the exact
  `AlternativeResolutionCoverageRecord`, record coordinate, and reconstruction
  material read by that claim, and every portable typed
  `AlternativeResolutionBlocker` with its checked association/non-use basis;
- exact semantic `D`, the qualification-resolution ledger body and portable
  coordinate, derived `Q`, its closure proposition, and the reconstruction
  material for its fresh closure capability;
- exact candidate-indexed qualification-input projections, their total
  `QualificationProjectionEvaluationLedger<D>`, every portable attempt audit or
  typed `CompilerNotAttemptedRecord`, and reconstruction material for every
  Checked entry;
- exact candidate-domain denotation, quotient, and closure bases;
- symbolic denotation and closure certificates separately from infeasibility
  or optimality certificates;
- exact target and intermediate carrier material and dependency bundles;
- transition, lineage, Analysis, and qualification replay material;
- for every problem-local legality result read, the exact legality profile,
  `CompilerLegalityRecord`, portable record ID, validation contract, complete
  source binding and policy closure, and every reconstruction preimage needed
  to rerun `CheckCompilerLegality`;
- immutable candidate-indexed assessment input portfolio bodies;
- their separate inert `AssessmentInputCompletenessRecord` records/IDs, total
  input-use, constraint, and objective evaluation ledgers, every portable
  attempt audit or typed `CompilerNotAttemptedRecord`, exact policy-approved
  short-circuit proof, resolved qualification sets, every Checked input-use/constraint/
  objective result, comparison material, complete
  `CandidateAssessmentResult<D,Q>` values, and `AssessmentId` replay bases;
- exact `Stage4BOwnedFactOrValue`,
  Evidence-owned `EvidenceQualifiedEstimate`, and Analysis-owned
  `AnalysisEvidenceDerivedEstimate` records read, plus each separate
  Compiler-owned candidate-target association;
- complete assessment ledger keyed by `Q`;
- exact `DecisionDerivationBasis<D,Q>`, certificate payload/correspondence when
  used, optimal equivalence class or Pareto frontier, every assessment- or
  certificate-backed member-support coordinate, representative policy, and
  decision; and
- every complete expected `CompilerCheckedResult` read or recreated by the
  decision, including its record body and portable ID,
  exact output binding, Compiler result-policy disposition, capability ABI,
  origin coordinates, source-policy closure, and residual trust; and
- every portable nonauthoritative typed `CompilerAttemptAudit<T,R>` or exact
  `CompilerNotAttemptedRecord<T,R>` retained by a qualification, assessment,
  closure, or report, together with its existential type witnesses, enclosing
  association, and checked non-use or irrelevance basis; and
- named consumer, exact residual-trust closure, complete source-authority
  binding ledgers, and complete transitive source-
  operation-policy dependency closure.

The bundle body separately retains the exact expected final
`CompilerDecisionResult<D,Q>` even when the preceding reconstruction inventory
also contains every prerequisite checked result. This makes the final equality
target constructible without inferring an output binding from the semantic
`CompilerDecision` body.

Any owner-local coordinate in one expected Compiler result, attempt audit, or any transitive
dependency makes the decision replay bundle unavailable under the rule above.

The bundle contains no live capability of any kind, including bootstrap,
Compiler-contract, result-policy, result-minting,
transition, owner-fact, Analysis, qualification, input-use, constraint,
objective, assessment, domain, or decision authority.

Cold replay does not rerun mutable search. It:

1. reconstructs the exact Compiler bootstrap admission contracts and manifests,
   reruns `AdmitCompilerSemanticCapabilityContract` and
   `AdmitCompilerResultOperationPolicy` in that order, and requires complete
   admitted-subject binding, contract, ABI, and no-policy-disposition equality
   before accepting either fresh Compiler-owned admission capability;
2. reconstructs every foreign admitted-subject binding, reauthenticates and
   re-admits every exact Protocol or peer-owner subject, and requires complete
   binding equality against the fresh admission capability;
3. reconstructs and reauthenticates every portable foreign checked-result binding,
   including its exact stable result record and owner-specific
   qualification, derivation, support, semantic-basis, validation-basis,
   assurance, trust, and `OwnerCapabilityRequirement` coordinates;
4. rechecks independent upstream admission, transition, lineage, Analysis
   bases, and every immediate
   and transitive owner-policy disposition; `BoundTo` reconstructs the complete
   policy and fresh purpose authority, while `OwnerDefinesNoOperationPolicy`
   reconstructs the exact owner capability-contract/ABI and obtains fresh owner
   admission or mediated confirmation; no fresh capability is accepted until
   its complete origin and disposition bindings match, and every bound policy
   permits the replay purpose;
5. before every Compiler checked-result operation below, reconstructs its exact
   `CompilerResultMintingAuthority<ResultFamily>` from the freshly admitted
   Compiler contract and result policy, and supplies every Compiler-owned input
   through a newly authorized `CompilerResultUseAuthority`; after `Completed`,
   it requires exact equality of the entire expected `CompilerCheckedResult`--
   record body, coordinate, output binding, origin closure, policy disposition,
   capability requirement, trust, and authorization record--before the fresh
   output capability may feed any later operation;
6. reruns `ValidateTransformProblem` and `ValidateDecisionPolicy`, requires
   complete validation-result equality under step 5, and obtains fresh
   `CheckedTransformProblem` and `CheckedDecisionPolicy` capabilities before any
   dependent operation; when the bundle retains a run request, it also reruns
   `ValidateCompileRunRequest` and obtains its fresh checked capability, then
   reruns `CheckProposalOccurrenceUse` for every request-derived occurrence read
   by the retained scope and requires complete occurrence-use-result equality;
7. reconstructs every exact cycle-free `Qualification` and `QualificationId`,
   reruns `FormQualifiedCandidate` for every candidate read, and requires full
   equality of the embedded qualification support binding; it then reruns
   `ValidateCandidateDomainPolicy` under the fresh checked problem and decision
   policy, recreates every required `CheckedCandidateQuotient` with exact body,
   complete checked-result equality, then reconstructs total alternative
   resolution. Resolved, duplicate, and conclusively excluded entries are
   rechecked from their exact authoritative bases; each Unresolved entry's
   Compiler/foreign attempt, not-attempted, or incomplete-search blocker is
   checked only for canonical integrity, exact alternative association, and
   nonauthoritative non-use, without requiring a failure to recur. It then reruns
   `CheckAlternativeResolutionCoverage` with complete coverage-result equality,
   consuming every fresh request-derived occurrence-use capability recreated in
   step 6; only after all required candidate,
   occurrence-use, coverage, policy, and quotient capabilities exist does it
   recheck exact candidate-domain closure and reconstruct semantic `D`;
8. reruns `CheckCompilerLegality` for every transition case whose result is
   read under the fresh checked problem, requiring exact legality profile,
   `CompilerLegalityRecord`, portable record ID, source binding, policy closure,
   and complete `CompilerLegalityResult` equality before accepting each fresh legality
   capability; it then reconstructs immutable candidate-indexed qualification
   projections and their total evaluation ledger. It reruns only each `Checked`
   projection entry and requires full result equality; for `Unresolved` or
   `NotAttempted`, it validates exact canonical association and
   nonauthoritative status without treating the entry as a result or requiring
   the operational failure to recur;
9. reruns total qualification resolution, requires complete
   `QualificationResolutionLedgerResult<D>` equality, reconstructs exact `Q`, and reruns
   `CheckComparisonAlternativeDomainClosure` with exact domain and closure-
   proposition equality to obtain a fresh
   `CheckedComparisonAlternativeDomain<Q>` before any assessment portfolio is
   accepted;
10. reconstructs every immutable assessment portfolio read by an `Assessed`
   entry and its total input-use, constraint, and objective evaluation ledgers.
   It separately reruns portfolio completeness and only the `Checked` entries,
   rechecks their peer-owner inputs, and requires complete checked-result
   equality. For every `Unresolved` or `NotAttempted` entry it validates exact
   canonical association and nonauthoritative status, does not require a prior
   failure to recur, and revalidates the exact policy-approved irrelevance proof
   before rerunning `CheckCandidateAssessment` with full
   `CandidateAssessmentResult<D,Q>` equality. It handles `NotAssessed` blockers
   by the same nonauthoritative rule, then reconstructs and fully rechecks every
   standalone Compiler-owned terminal or irrelevance result used by closure and
   supplies its fresh result-use authority before rerunning
   `CheckAssessmentClosure`. For `ExternalCertificate`, it also reconstructs and
   rechecks the exact affirmative certificate statement, D/Q correspondence,
   complete foreign result binding and affirmative qualified outcome, fresh
   matching affirmative owner capability, and conjunctive source-
   policy authorization. It then requires complete
   `AssessmentClosureResult<D,Q>` equality;
11. follows the retained `DecisionDerivationBasis`: `AssessmentDerived` repeats
   comparison, Pareto, tie, and representative selection from every required
   Checked assessment; `CertificateDerived` instead requires exact equality of
   the rechecked affirmative certificate result and qualified outcome, payload,
   D/Q/policy correspondence, and
   coverage, extracts only the certified optimum/frontier/infeasibility claim,
   and applies a representative or optional totalization rule only to data that
   payload establishes; and
12. before the final decision operation, requires exact equality with the retained semantic
   `D` and `Q`, alternative-resolution, qualification-resolution, and assessment
   ledgers, qualification projections, decisive source-authority-binding and
   transitive policy closures, `CompilerDecision`, `DecisionId`, residual-trust
   closure, and every complete checked result retained by the bundle, then
   reruns `CheckCompilerDecision` with that exact decision body, every inert
   result and ledger, and all freshly recreated prerequisite result-use authorities.
   For `CertificateDerived`, it separately reauthorizes the exact foreign
   affirmative certificate under its complete immediate/transitive source
   policies for the compiler-decision purpose and supplies the fresh matching
   affirmative owner capability;
   closure-purpose authorization cannot substitute. It then
   requires exact equality between its returned `CompilerDecisionResult` and
   the retained result, and accepts a fresh final decision capability only from
   that operation's `Completed` branch under the exact admitted
   `CompilerResultOperationPolicy`, exact `DecisionPolicy`, and all immediate
   and transitive source policies. Intermediate capabilities used by replay were already
   freshly recreated by their owning checks.

An open report uses a separate `CompilerOpenReportReplayBundle<R>`. Its
`expected_final_result` is the exact `CompilerOpenReportResult<R>`; its
canonical reconstruction material retains the exact Compiler bootstrap,
capability-contract, result-policy, and result-minting reconstruction preimages,
exact policy and foundational validation results, the exact run-request, job,
or progress-accounting descriptor when read, every qualified subset record and
source binding the report reads,
the exact portable `CompilerAttemptAuditLedger`, exact
`CompilerNotAttemptedRecordLedger`, and every `AlternativeResolutionBlocker`
claimed as audit-record-relative accounting, all
policy/trust closures, and every input needed to rerun
`CheckOpenCompilerReport<R>`. Report replay applies the same portable-only
source reconstruction and foundational validation rules above, reconstructs
only the report's exact claimed subset/accounting scope, validates nonauthoritative
audit association and canonical integrity without requiring a failure to recur,
and reruns
`CheckOpenCompilerReport<R>` with freshly reconstructed input-use and report-
family result-minting authority, and requires equality of the complete returned
`CompilerOpenReportResult<R>`, including its output binding, before accepting a
fresh `QualifiedCompilerOpenReport<R>`.
Owner-local input makes this report bundle unavailable. A decision bundle
cannot replay a report, and a report bundle cannot mint a closed decision.

Decision replay, report replay, producer rerun, and bit-for-bit proposal
reproduction are different claims.

## 12. Cache classes

~~~text
ProducerSearchCache
  unauthoritative plans, proposals, and discovery hints

SemanticReplayCache
  immutable basis and certificate material requiring exact revalidation

EvidenceInputCache
  exact Evidence-owned qualified records, appraisals, or values retaining
  producer observation meaning, environment, procedure, time, and uncertainty

ProcessLocalAuthorityMemo
  owner-internal reuse of one still-live capability under identical immutable
  dependencies and the same authority lifetime
~~~

A persistent key includes every semantic subject, regime, proposition, model,
assumption, semantic and validation basis, every authenticated owner-policy
disposition including exact bound-policy or explicit no-policy owner-contract/
ABI identity, every transitive source-policy dependency closure, checker contract,
candidate domain, qualification policy, comparison domain,
portfolio body, constraint, objective, Stage 4B or Evidence association,
every complete portable `ExactSourceAuthorityBindingLedger`, including each
portable subject/admission coordinate or checked-result record and its
owner-specific qualification, derivation, support, semantic-
basis, validation-basis, assurance, trust, owner-policy disposition, transitive
source-policy closure, and `OwnerCapabilityRequirement`,
every complete Compiler-owned `CompilerCheckedResult` and its exact output
binding, plus the admitted Compiler semantic-capability-contract and result-
operation-policy coordinates, ABIs, binding schemas, and admission preimages,
every retained portable typed `CompilerAttemptAudit<T,R>`,
`CompilerNotAttemptedRecord<T,R>`, `AlternativeResolutionBlocker`, enclosing
association, existential type witness, and checked non-use or irrelevance basis,
environment, named consumer and purpose, and every version coordinate that can
affect the material.

An owner may separately define an authenticated stable confidential identity
whose contract explicitly permits protected persistence and replay. Such an
identity is a portable owner contract, not the `OwnerLocal` branch of
`ExactSourceAuthorityBinding`; an owner-local coordinate remains categorically
ineligible for this key or cold replay.

A cache hit is a hint until exact key reconstruction and owner revalidation.
Basis drift makes an entry stale, not the underlying semantic claim false.
Cached bytes, signatures, old decision IDs, and matching digests cannot
rehydrate live authority. Only same-process owner memoization may reuse a
capability that has not crossed reset, serialization, dependency change, or
authority lifetime, and only when the exact admitted
`CompilerResultOperationPolicy`, exact `DecisionPolicy` when read, plus every
authenticated immediate owner-policy disposition and transitive source-policy
closure remain exact: every bound policy must freshly permit the named consumer
and memo-reuse purpose, while every explicit no-policy contract must be freshly
validated against its owner ABI and still-live capability. An unavailable or
prohibiting source policy prevents reuse even while the capability remains
live.
Every persistent cache class is subject to the same conjunctive source-policy
creation, retention, disclosure, lookup, redaction, and confidentiality gate as
the replay bundle.

## 13. Residual trust

Every completed qualification, assessment, closure, and decision retains one
exact finite acyclic `ResidualTrustClosure`. Each node states a correctness or
adequacy claim; every path terminates at an exact trust root. A project name,
institution, `trusted`, `machine checked`, or `verified` is not a root.

Representative roots include:

~~~text
NormativeSemanticDefinitionRoot
SourceAdmissionRoot
CheckerImplementationRoot
ExternalKernelRoot
CertificateDecoderOrTranslationRoot
TrustedDecisionOracleRoot
MeasurementProcedureRoot
~~~

Each root carries its exact regime, contract, implementation, platform,
translation, environment, and asserted claim coordinates as applicable.

A closed best or `NoEligible` result retains every root used decisively for
alternative resolution, target authentication and admission, transition
qualification, Compiler legality, candidate-domain closure, qualification
resolution, comparison-domain closure, portfolio completeness, input use,
constraint evaluation, exclusion, objective comparison, infeasibility or
optimality checking, and representative selection. It cannot retain only the
selected candidate's roots or compress the graph into one assurance rank.

Logical hypotheses and trust roots remain distinct. A hardness assumption,
unproved theorem, or assumed model correspondence stays in the proposition's
hypothesis closure. Checker, encoding, kernel, runtime, and normative-
definition adequacy stay in the residual-trust graph. A later consumer decides
whether those exact hypotheses and roots are acceptable.

## 14. Stage 4B and Evidence boundary

Compiler never treats a raw OIR, realization, target, supplier, endpoint,
deployment, invocation, measurement, or identifier as an objective value or
eligibility fact.

It may consume an exact `Stage4BOwnedFactOrValue` only when `DecisionPolicy`
names its required fact/value schema. The concrete later-owned result is
created independently after its own exact subjects exist and enters the
candidate-indexed portfolio only after `CandidateId` exists. That result
retains:

- the exact candidate target Protocol identity and admission regime;
- every exact OIR, Interface, Plan, projection, realization, target, supplier,
  endpoint, environment, and occurrence operand read;
- the exact Stage 4B question, model, qualified outcome, checker, basis,
  authenticated `OwnerOperationPolicyDisposition`, total transitive source-
  policy dependency closure, complete owner-created checked-result authority
  binding, matching
  inert `OwnerCapabilityRequirement`, and residual trust; and
- enough source-owned subject and map identity to check association to a
  candidate target without naming a future Compiler assessment.

The Stage 4B fact never names a future `AssessmentId`, assessment portfolio,
comparison alternative, or decision. The independent Stage 4B owner record may
enter the portfolio. The later Compiler-owned inert `AssessmentInputUseRecord`
binds that fact identity; the exact `DecisionPolicy` and policy schema; the
exact `AssessmentInputPortfolio`, whose body retains the exact candidate,
transition case, and admitted target; one canonical typed portfolio-slot
coordinate; the completed unique membership and candidate/target/policy
association result; the authenticated owner-policy disposition and total
transitive source-policy closure; the complete owner-created checked-result
authority binding; and the inert `OwnerCapabilityRequirement`.
The separate occurrence-local `CheckedAssessmentInputUse` validates that
disposition and closure and retains
the exact matching fresh owner capability for its authority lifetime, and the
assessment check consumes that live capability. The use record enters only
downstream assessment, replay, or other content identities; it never enters the
portfolio whose exact reference it names. This keeps
authority and identity acyclic and leaves Stage 4B meaning invariant under
`DecisionPolicy`.

If a required Stage 4B fact is absent, the exact result is undetermined,
unsupported, or refused according to its owner and policy; absence is not a
hidden candidate rejection. If the policy does not name its schema, assessment
must be invariant under substitution of that unrequested fact.

Projection, realization, and endpoint meaning are invariant under Compiler
history. Two decisions selecting the same exact admitted target cannot change
a Stage 4B result because they used different producers, proposals, paths,
domains, objectives, or selection histories. Stage 4B reconstructs its result
from its own exact admitted Protocol, Interface, Plan, OIR, target, supplier,
endpoint, and regime inputs. Compiler history may be Evidence or policy
metadata; it is never a hidden semantic operand.

If one Protocol candidate has several Stage 4B alternatives, Stage 4A either
consumes an exact later-owned fact under a declared aggregation or choice
policy, or a future higher-level owner defines an explicit product domain.
Stage 4A does not silently widen `CandidateId` or `Q` into an OIR,
realization, deployment, or endpoint alternative.

Each producing domain owns the meaning and completeness frontier of its raw
observations and measurements. Evidence owns the bridge from that exact
producer-owned material, provenance, experimental procedure, environment,
samples, and uncertainty to an attributable Evidence record or qualified
appraisal. Analysis owns any rule that turns Evidence into a semantic claim.
Compiler may consume an exact Evidence-owned `EvidenceQualifiedEstimate` or an
exact Analysis-owned `AnalysisEvidenceDerivedEstimate` only through the
corresponding owner's complete source binding and fresh capability. Their
declared epistemic shapes remain distinct, and neither may be relabeled as an
exact structural value.

In the fully portable lane, a durable decision identifies its exact Best
representative, complete Pareto set with any policy-permitted representative,
or no-eligible result. Only a decision branch that names or permits an exact
representative supports a selected-target handoff. The portable decision
transitively identifies that selected candidate and target through its exact
member support and qualification-resolution dependencies, but it contains no
target carrier or reconstruction manifest.

A cold selected-target handoff is therefore a separate portable-only product:

~~~text
CompilerSelectedTargetHandoffBundle<D,Q> {
  exact CompilerDecisionResult<D,Q> whose Best branch or policy-permitted
    CompletePareto totalization selects exactly one comparison alternative,
  exact selected ComparisonAlternativeDecisionSupport<D,Q>,
  exact ExactCompilerValueRef<Candidate> and complete qualification-resolution
    path proving equality with the decision's selected candidate coordinate,
  exact selected target Protocol identity, canonical PIR carrier, admission
    regime, and every target/dependency reconstruction input required for PIR
    authentication and whole-Protocol admission,
  exact NamedConsumer and typed compiler-selected-target-handoff purpose,
  exact CompilerResultOperationPolicy and every immediate or transitive source-
    policy/no-policy-contract coordinate governing retention and disclosure,
  exact checked authorization records permitting creation, retention, and
    disclosure of every retained field for that exact consumer and purpose,
  no live capability or owner-local handle
}

CompilerSelectedTargetHandoffBundleId<D,Q> = H(
  "zkc/compiler-selected-target-handoff-bundle",
  CompilerSemanticRegimeId,
  CanonicalEncode_regime(
    exact CompilerSelectedTargetHandoffBundle<D,Q>))
~~~

The equality path ends at the exact candidate reference retained by the
selected candidate-qualification result and its exact transition-case target;
an identifier is never dereferenced through an ambient registry. The bundle is
created only when its complete preimage is portable and the Compiler result
policy plus every governing source policy or explicit no-policy contract
freshly authorizes the exact Stage 4B consumer and handoff purpose. Permission
for compiler-decision replay, persistence, or another consumer does not widen
to handoff. Missing reconstruction material, a local dependency, unavailable
governance, policy denial, `NoEligible`, or a Pareto result without an exact
policy-permitted representative means that no cold handoff bundle exists.

The bundle grants neither decision nor Protocol authority. The receiving OIR
or Realization process must independently reauthenticate the canonical carrier
and readmit the target through PIR; relying on the decision claim additionally
requires separately reconstructed fresh Compiler decision authority for the
recipient's exact purpose. The decision and handoff bundle contain, mint,
serialize, and rehydrate no `AdmittedProtocol` capability. A local decision is
nonpersistable. A same-process result may instead return the independently
PIR-owned capability alongside the decision without conversion.

## 15. Reversal triggers

This target must be reopened if an exact counterexample shows that:

1. semantic `D` and comparison-alternative `Q` cannot remain separate without
   losing a necessary decision claim;
2. total qualification resolution cannot account for every candidate without
   changing candidate meaning;
3. portfolio body, portfolio completeness, input use, and assessment cannot be
   identified acyclically;
4. an assessment must be keyed only by target or candidate rather than its
   exact comparison alternative;
5. a required objective cannot preserve both provenance and epistemic shape;
6. a closed `NoEligible` result is needed while a decision-relevant
   qualification, alternative, input, or assessment remains unresolved;
7. cold replay necessarily depends on mutable producer behavior; or
8. Stage 4B or Evidence requires a fact to identify a future assessment or
   decision, creating an authority cycle.

Implementation convenience, current wire forms, performance, migration cost,
or provider order are not reopening reasons by themselves.

## 16. Exact nonclaims

This specification does not establish:

- acceptability or completeness of any qualification portfolio;
- truth, adequacy, or correctness of any Analysis, transition, Stage 4B,
  Evidence, checker, certificate, model, or trust root;
- satisfaction or violation of any concrete constraint;
- availability, exactness, or comparative order of any concrete objective;
- eligibility, ineligibility, assessment closure, Pareto completeness,
  selection, infeasibility, optimality, or `NoEligible` for any request;
- optimality beyond one exact closed `D` and derived `Q`;
- Protocol admission, relation truth, property transport, endpoint
  feasibility, realization, deployment, runtime success, or cryptographic
  security;
- implementation correspondence, compatibility, migration feasibility,
  release readiness, or normative cutover; or
- persistence of live authority.
