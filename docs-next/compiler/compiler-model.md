# Validated-decision Protocol compiler model

> **Document kind:** Target semantic architecture
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

## 1. Scope and selected architecture

The target Protocol Compiler is a **validated-decision system**. Replaceable
producers may search for possible successors, but only independently admitted
Protocols, exactly qualified predecessor/successor transitions, and exact
typed assessment inputs can enter a Compiler decision.

The architecture has five planes:

~~~text
Problem plane
  TransformProblem + DecisionPolicy

Production plane
  optional checked CompileRunRequest + SearchJob when request-relative
  + replaceable producer state; direct submission may omit the request

Proposal-resolution plane
  ExplorationSpace + frozen ProposalScope + DeclaredAlternatives
  + total AlternativeResolution ledger

Qualification and assessment plane
  PIR-owned target admission + exact transition qualification
  + CompilerLegality + typed constraints and objectives

Decision plane
  CandidateDomain + ComparisonAlternativeDomain + total accounting
    -> checked decision sufficiency + scoped closed decision
  checked DecisionPolicy + any exact reached qualified subset
    + exact reached closure results actually read + audit accounting
    -> explicitly open report
  preparation/check failure -> outer outcome
~~~

These planes are authority and responsibility partitions, not a temporal
pipeline. The exact order is fixed in Section 5: scope freezing precedes
per-alternative target admission and transition qualification, which precede
finalization of the total alternative-resolution ledger. The planes share exact
identities and dependency references, not authority. In particular:

- a production result is not a Protocol;
- Protocol admission is not a predecessor/successor relation;
- a checked transition is not property transport;
- a qualified Analysis result is not Compiler eligibility;
- a candidate is not its proof basis or assessment;
- a score is not a domain-closure result; and
- selection creates no upstream semantic fact.

The detailed proposal, transition, and domain rules are specified in
[Proposals, relations, and candidate domains](proposals-relations-and-domains.md).
The detailed qualification, assessment, selection, and replay rules are
specified in
[Assessment, selection, and replay](assessment-selection-and-replay.md).

## 2. Ownership boundary

`compiler` owns:

- `TransformProblem`, `DecisionPolicy`, and `CompileRunRequest` validation;
- orchestration of replaceable search and frozen proposal scopes;
- total alternative-resolution accounting;
- problem-local `CompilerLegality`;
- formation and exact scoped closure of semantic candidate domains;
- qualification-use policy without redefining the qualified facts;
- typed constraint evaluation;
- typed objective and comparison policy;
- comparison-alternative formation, assessment completeness, Pareto and tie
  handling, and deterministic representative selection;
- exact closed decisions, qualified open reports, and decision replay; and
- Compiler-specific residual-trust and persistence contracts.

`compiler` does not own:

- Protocol meaning, identity, authentication, or whole-Protocol admission;
- relation, trace, distribution, declared-change, cost, or cryptographic-
  property meaning;
- relation satisfaction or property transport;
- OIR projection, local OIR validity, realization, supplier binding, endpoint
  feasibility, deployment, invocation, or execution;
- Evidence observations, measurement procedure, or uncertainty; or
- a later consumer's reliance or release decision.

The semantic owner of each input mints its exact live capability. Compiler may
consume that capability and record its exact identity and basis; it cannot
mint, widen, serialize, or reinterpret it.

Every cross-owner capability is supplied with the exact capability-neutral
binding selected by the [project-wide source-binding
contract](../project/analysis-and-compiler-architecture.md#23-capability-neutral-source-bindings).
An admitted subject or view uses `ExactOwnerAdmittedSubjectBinding`; a completed
checked result uses `ExactOwnerResultBinding`. Compiler receives each binding
and its actual fresh capability separately and requires complete equality. A
Compiler-owned capability instead matches its complete owner-created
`CompilerCheckedResult`, including the result body/coordinate and exact output
binding, through the `CompilerResultUseAuthority` contract below. It does not
invent a cross-owner alias or inspect data out of a live capability.

~~~text
ExactOwnerAdmittedSubjectBinding<Owner, SubjectFamily> =
  ExactAdmittedSubjectAuthorityBinding<Owner, SubjectFamily>

ExactOwnerResultBinding<Owner, ResultFamily> =
  ExactCheckedResultAuthorityBinding<Owner, ResultFamily>

ExactSourceAuthorityBindingLedger = CanonicalTypedLedger<
    exists exact Owner and SubjectFamily:
      ExactOwnerAdmittedSubjectBinding<Owner, SubjectFamily>
  | exists exact Owner and ResultFamily:
      ExactOwnerResultBinding<Owner, ResultFamily>>
~~~

Operations pattern-match the two variants. Admission inputs can never be
silently treated as result records, and checked results can never be accepted
from subject identity alone. A record that depends on both retains the complete
canonical typed ledger; a structure that permits only checked facts may refine
it to the result-only subset.

Every source has exactly one authenticated owner-policy disposition:

~~~text
OwnerOperationPolicyDisposition =
    BoundTo(exact owner operation-policy identity and authenticated contract)
  | OwnerDefinesNoOperationPolicy(
      exact owner capability-contract identity, exact capability ABI)
~~~

The second variant is legal only when the exact owner capability contract and
ABI explicitly declare the absence of a separate operation policy. Unknown,
missing, or omitted policy information is never treated as “not applicable.”
Every Compiler use preserves this disposition, the complete exact source-
authority binding, the immediate policy when bound, the transitive source-
policy closure, and the matching inert `OwnerCapabilityRequirement`. A use proceeds only when the
Compiler policy and every bound immediate or transitive owner policy freshly
permit the exact named consumer and typed purpose.

### 2.1 Compiler result ABI and owner operation policy

Compiler output authority has an independently versioned owner contract; it is
not bootstrapped from the candidate-specific `DecisionPolicy`:

~~~text
CompilerAdmissionCapabilityContract<S> {
  compiler_semantic_regime_id,
  exact foundational admitted-subject family S,
  exact admission capability ABI and operand/result binding schema,
  exact freshness and authority-lifetime rules,
  exact foundational-attempt audit creation, stable-identity, and disclosure
    rules, including any required named consumer and typed audit purpose,
  explicit declaration that no separate admission operation policy exists
}

CompilerAdmissionCapabilityContractId<S> = H(
  "zkc/compiler-admission-capability-contract",
  CompilerSemanticRegimeId,
  CanonicalEncode_regime(exact CompilerAdmissionCapabilityContract<S>))

CompilerSemanticCapabilityContract {
  compiler_semantic_regime_id,
  exact result-family capability ABIs,
  exact operand/result binding schemas,
  exact freshness, authority-lifetime, and attenuation rules
}

CompilerResultOperationPolicy {
  compiler_semantic_capability_contract_id,
  exact result-family and completed-outcome coverage,
  exact result-family- and U/C/R/M/F-disposition-indexed attempt-audit
    creation, stable-identity, and disclosure rules,
  exact named-consumer and typed-purpose permission rules,
  exact capability-use, disclosure, persistence, replay, and attenuation rules
}

CompilerResultMintingAuthority<ResultFamily> {
  exact admitted CompilerSemanticCapabilityContract value and
    ExactAdmittedSubjectAuthorityBinding with separately supplied fresh
    matching Compiler-owned admission capability,
  exact admitted CompilerResultOperationPolicy value and
    ExactAdmittedSubjectAuthorityBinding with separately supplied fresh
    matching Compiler-owned admission capability,
  exact NamedConsumer and typed result-family operation purpose,
  fresh purpose authorization under that exact result operation policy
}

LocalCompilerOwnerAdmissionAttemptInputHandle =
  fresh owner-issued process-local nonserializable opaque input-material handle

CompilerOwnerAdmissionSlotStatus =
    Authenticated(exact capability-neutral typed value, identity, contract,
                  ABI, binding, or regime required by that slot)
  | OfferedCandidate(exact capability-neutral typed candidate and any claimed
                     identity or binding)
  | Missing
  | OpaqueMalformed(exact normalized defect class,
                    exact LocalCompilerOwnerAdmissionAttemptInputHandle)

CompilerOwnerAdmissionAttemptInput<S,C> {
  exact owner-selected foundational admission entry point,
  exact expected subject family S and admitted capability family C,
  exact statically declared operand-slot schema for that entry point,
  exactly one CompilerOwnerAdmissionSlotStatus for every and only declared
    input slot,
  exact slot-to-operation association,
  no admitted-subject output, live capability, or claim that an admission
    occurrence happened
}

PrepareCompilerOwnerAdmission<S,C>(
  exact CompilerOwnerAdmissionAttemptInput<S,C>,
  occurrence-local bootstrap or admitted-authority offers for the declared
    slots, which may be absent, stale, nonmatching, malformed, or prohibited
    and are never retained)
  ->
    Ready(exact typed complete operand tuple for the selected foundational
          admission signature)
  | Rejected(exact owner-admission disposition, failed requirement, and reached
             bootstrap/contract checks)

AttemptCompilerOwnerAdmission<S,C>(
  exact CompilerOwnerAdmissionAttemptInput<S,C>,
  occurrence-local bootstrap or admitted-authority offers)
  -> CompilerOwnerAdmissionAttemptOutcome<S,C>

CompilerOwnerAdmissionAttemptRecord<S,C> {
  exact CompilerOwnerAdmissionAttemptInput<S,C>,
  exact capability-neutral complete operand projection when preparation reached
    Ready, or exact rejected slot and preparation state otherwise,
  exact reached subject S, bootstrap admission contract, and Compiler semantic
    regime, or exact slot status showing why any coordinate was unavailable,
  exact reached audit-disclosure consumer and typed purpose when required by
    the bootstrap admission contract, or exact unavailable slot status,
  exact successful and failed foundational audit-disclosure checks that were
    reached,
  exact missing, mismatched, prohibited, or failed requirements,
  exact Unsupported, CannotAnswer, Refused, Malformed, or normalized
    CheckerFailure disposition,
  Reached(exact residual trust)
    | Unavailable(exact governing unavailable slot and dependency path),
  no admitted-subject binding or live capability
}

CompilerOwnerAdmissionAttemptRecordRef<S,C> =
    Portable(exact CompilerOwnerAdmissionAttemptRecord<S,C>,
             exact Id(exact CompilerOwnerAdmissionAttemptRecord<S,C>))
  | OwnerLocal(exact CompilerOwnerAdmissionAttemptRecord<S,C>,
               exact LocalCompilerHandle<
                 CompilerOwnerAdmissionAttemptRecord<S,C>,
                 exact CompilerOwnerInstanceGeneration>)

CompilerOwnerAdmissionAttemptOutcome<S,C> =
    Admitted(exact ExactAdmittedSubjectAuthorityBinding<Compiler,S>,
             fresh process-local C)
  | Unsupported(exact CompilerOwnerAdmissionAttemptRecordRef<S,C>)
  | CannotAnswer(exact CompilerOwnerAdmissionAttemptRecordRef<S,C>)
  | Refused(exact CompilerOwnerAdmissionAttemptRecordRef<S,C>)
  | Malformed(exact CompilerOwnerAdmissionAttemptRecordRef<S,C>)
  | CheckerFailure(exact CompilerOwnerAdmissionAttemptRecordRef<S,C>)

AdmitCompilerSemanticCapabilityContract(
  exact immutable CompilerSemanticCapabilityContract and content identity,
  exact CompilerAdmissionCapabilityContract<
    CompilerSemanticCapabilityContract> and matching ID/ABI,
  exact Compiler semantic regime and bootstrap admission contract,
  fresh CompilerOwnerBootstrapAdmissionCapability<
    CompilerSemanticCapabilityContract> for that exact contract)
  -> CompilerOwnerAdmissionAttemptOutcome<
       CompilerSemanticCapabilityContract,
       AdmittedCompilerSemanticCapabilityContract>

AdmitCompilerResultOperationPolicy(
  exact immutable CompilerResultOperationPolicy and content identity,
  exact admitted CompilerSemanticCapabilityContract value and binding,
  fresh matching AdmittedCompilerSemanticCapabilityContract,
  exact CompilerAdmissionCapabilityContract<
    CompilerResultOperationPolicy> and matching ID/ABI,
  exact Compiler semantic regime and result-policy admission contract,
  fresh CompilerOwnerBootstrapAdmissionCapability<
    CompilerResultOperationPolicy> for that exact contract)
  -> CompilerOwnerAdmissionAttemptOutcome<
       CompilerResultOperationPolicy,
       AdmittedCompilerResultOperationPolicy>
~~~

The two displayed admission signatures are the `Ready` forms of the shared
foundational ingress. `CompilerOwnerAdmissionAttemptInput<S,C>` fixes the
owner-selected static slot schema and represents missing or malformed subjects,
identities, regimes, contracts, ABIs, and bootstrap/admitted authority before a
complete signature exists. Fresh authority is offered separately and never
enters the carrier or record. Only `Ready` executes an admission signature and
may return `Admitted`. `Rejected` constructs the exact portable or owner-local
attempt-record reference. `Portable` is legal only when the complete record
preimage is portable and the exact authenticated bootstrap admission contract
expressly permits foundational-attempt audit creation, stable identity, and
disclosure for that entry point and every required reached consumer/purpose.
If that contract, its disclosure disposition, or any required consumer or
purpose is unavailable, or if an `OpaqueMalformed` slot is present, the record
is `OwnerLocal`. Neither branch, input-material handle, nor record establishes
an admission occurrence or grants authority.

The capability contract and result operation policy follow a foundational
Compiler-owned subject authentication/admission lifecycle under the exact
Compiler semantic regime. Each family-indexed admission contract is an exact
acyclic regime-root contract, not a subject admitted through itself. It fixes
the admission ABI before the subject exists and explicitly uses
`OwnerDefinesNoOperationPolicy(exact CompilerAdmissionCapabilityContractId<S>,
exact capability ABI)`.
Its `OwnerCapabilityRequirement` names that exact contract, ABI, binding schema,
freshness, and lifetime.

`CompilerOwnerBootstrapAdmissionCapability<S>` is minted only at process
initialization by the exact source-admission root named in the corresponding
bootstrap admission contract; it is process-local, nonserializable, and grants
only the typed admission operation for `S`. Each admitted-subject binding is
created atomically with the fresh admitted capability, retains the exact
admission requirement and no-policy disposition, and is checked against the
bootstrap capability. U/C/R/M/F return only the exact unauthoritative bootstrap
attempt record, never an admitted-subject binding or capability. These operations do not produce a checked Compiler result and therefore do not
recurse through the result-binding lifecycle below. A policy is admissible only
when it names the exact admitted capability contract and covers every result
family it authorizes. The bootstrap root, contract implementation, and
admission checker remain explicit residual-trust roots rather than semantic
claims.

Except for the two nonrecursive foundational subject-admission operations above
and process-initialization bootstrap, every operation in these Compiler pages
that can return a checked result or mint another Compiler capability has one mandatory final
`CompilerResultMintingAuthority<that exact result family>` operand. This common
operand is part of every displayed signature even when factored out rather than
repeated immediately before `->`. Each displayed signature specifies the
complete `Ready` operand tuple for its operation; all external calls first pass
through the generic `CompilerCheckingAttemptInput` and
`PrepareCompilerCheckedOperation` boundary below. A missing, mismatched, stale,
malformed, or prohibiting operand is therefore representable before the
complete tuple exists and yields the exact U/C/R/M/F audit branch with no result
binding or capability. Each completed
Compiler output binding uses `BoundTo` with the exact admitted
`CompilerResultOperationPolicy`, and its `OwnerCapabilityRequirement` names the
exact admitted `CompilerSemanticCapabilityContract`, ABI, binding schema,
freshness, and authority lifetime.

`DecisionPolicy` remains the consumer-side transform, qualification,
assessment, and choice policy. It must accept the owner result policy for each
use, but it cannot define, admit, widen, or replace that policy or the Compiler
capability ABI. This direction breaks the would-be bootstrap cycle.

## 3. Semantic problem and operational request

### 3.1 `TransformProblem`

~~~text
TransformProblem {
  exact admitted predecessor references,
  exact target-admission regime,
  permitted TransformIntent profiles,
  required transition proposition patterns and accepted polarities,
  permitted intentional-change contracts,
  semantic-path policy,
  required lineage-map families
}
~~~

`TransformProblem` states what kind of semantic successor would count. It does
not select a producer, propose a target, choose a proof basis, or compare
candidates.

`TransformIntent<F>` fixes the exact family, source subjects, target-shape
restrictions, relation direction, observers and models, protected
observations, permitted deltas, required maps, and direct, adjacent, composed,
or adjacent-plus-end-to-end checking policy. A transform family name cannot
stand in for these coordinates.

### 3.2 `DecisionPolicy`

~~~text
DecisionPolicy {
  alternative-scope and candidate-domain formation specification,
  exact named Compiler consumer and typed qualification-resolution,
    assessment, comparison, and decision purposes,
  exact basis, immediate owner-operation-policy, transitive source-operation-
    policy dependency-closure, and residual-trust acceptance policy,
  required Analysis claim patterns,
  required peer-owner and Stage4B-owned fact/value schemas,
  required Evidence-owned qualified record, appraisal, or value schemas,
  exact candidate-association and input-completeness rules,
  exact QualificationResolutionPolicy,
  exact typed constraints,
  exact typed objectives,
  comparison, Pareto, tie, and representative policy,
  requested closed-decision or open-report strength
}
~~~

`DecisionPolicy` states how already meaningful transition cases are assessed
and compared. It cannot change the meaning, observer, model, polarity,
hypotheses, assurance class, owner-defined source operation policy, or residual
trust of an input judgment. Accepting a source policy does not authorize a use
that policy forbids.
It contains schemas and association rules, not concrete future facts about a
candidate. Exact candidate-associated qualifications enter only after
`CandidateId` exists, through an independently frozen
`QualificationInputProjection`. Assessment-only Analysis, peer-owner, Stage 4B,
and Evidence facts enter later through an immutable
`AssessmentInputPortfolio`. This separation prevents an assessment-only input
from changing qualification resolution or the comparison domain.

### 3.3 `CompileRunRequest` and `SearchJob`

Compiler-owned values cross typed boundaries through one exact value/coordinate
sum. The owner-local branch is defined fully in Section 4.1:

~~~text
CompilerValueCoordinate<T> =
    Portable(exact Id(T))
  | OwnerLocal(exact LocalCompilerHandle<
      T, exact CompilerOwnerInstanceGeneration>)

ExactCompilerValueRef<T> {
  exact value: T,
  exact coordinate: CompilerValueCoordinate<T>,
  required coordinate/value equality invariant:
    Portable => the complete T preimage contains no local child and recomputes
                the exact Id(T),
    OwnerLocal => the current owner/generation handle resolves through the
                  exact owner-internal handle/value relation to this exact T,
  no auxiliary proof bytes or selectable proof identity,
  no live capability
}
~~~

The tags are disjoint. These references are inert and never substitute for a
checked-result binding, result-use authority, or fresh capability.

~~~text
CompileRunRequest {
  transform_problem_coordinate: CompilerValueCoordinate<TransformProblem>,
  decision_policy_coordinate: CompilerValueCoordinate<DecisionPolicy>,
  search_job: ExactCompilerValueRef<SearchJob>,
  optional named replay or audit consumer
}
~~~

`SearchJob` contains producer identities, recipes, seeds, heuristics, solver
and resource limits, worker configuration, and other operational discovery
inputs. Search may be mutable, nondeterministic, parallel, interrupted, or
empty. Those facts do not change `TransformProblemId` or `DecisionPolicyId`.
`SearchJobId` content-identifies this immutable operational job specification;
one execution is never inferred from that ID.

~~~text
LocalSearchJobOccurrenceHandle =
  fresh producer-scoped process-local nonserializable handle

SearchJobOccurrenceDescriptor {
  exact CompilerValueCoordinate<CompileRunRequest> and
    CompilerValueCoordinate<SearchJob>,
  exact producer identity,
  claimed_occurrence_coordinate:
      Portable(exact producer-scoped canonical occurrence label)
    | OwnerLocal(exact LocalSearchJobOccurrenceHandle),
  exact capability-neutral bounded-exploration/progress descriptor when
    intentionally claimed,
  no execution-history authority
}

SearchJobOccurrenceId = H(
  "zkc/search-job-occurrence-descriptor",
  exact portable SearchJobOccurrenceDescriptor)

SearchJobOccurrenceRef =
    Portable(exact SearchJobOccurrenceDescriptor,
             exact SearchJobOccurrenceId)
  | OwnerLocal(exact SearchJobOccurrenceDescriptor,
               exact LocalSearchJobOccurrenceHandle)
~~~

The `Portable` occurrence branch is legal only when both child coordinates,
the producer-scoped canonical label, and every other identity-bearing field are
portable. If either child coordinate is `OwnerLocal`, the occurrence reference
must use its `OwnerLocal` branch even when the claimed label is otherwise
portable.

The portable ID content-identifies only a producer-scoped claimed occurrence
descriptor; the local handle distinguishes only a same-process claimed
descriptor. Neither proves that execution happened, that the progress claim was
observed, or that a producer emitted anything. Actual run history requires a
separate owner-authenticated occurrence or log result, which Stage 4A does not
define. Neither reference is a semantic candidate or domain identity.

If a bounded exploration procedure is itself the scope of a requested weaker
report, its exact finite exploration profile is a separately identified
operand. Ambient timeout, cache state, or process scheduling never silently
becomes semantic domain meaning.

### 3.4 Owner validation of problem, policy, and run request

Compiler creates its foundational live authority through three explicit owner
operations:

~~~text
ValidateTransformProblem(
  exact ExactCompilerValueRef<TransformProblem>,
  complete ExactSourceAuthorityBindingLedger for every authority-bearing
    admitted predecessor, regime, map, or contract reference,
  separately supplied fresh matching source capabilities,
  exact NamedConsumer and typed ValidateTransformProblem purpose,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose,
  exact Compiler semantic regime and validation contract)
  -> CompilerValidationAttemptOutcome<
       CheckedTransformProblem,
       exact inert TransformProblemValidationRecord>

ValidateDecisionPolicy(
  exact ExactCompilerValueRef<DecisionPolicy>,
  exact authenticated/admitted owner schema, capability-contract, comparator,
    and policy preimages named by the policy, with any required source bindings
    and separately supplied fresh capabilities,
  exact NamedConsumer and typed ValidateDecisionPolicy purpose,
  every authenticated BoundTo/no-policy preimage with fresh policy/contract
    authority for that consumer and purpose,
  exact Compiler semantic regime and validation contract)
  -> CompilerValidationAttemptOutcome<
       CheckedDecisionPolicy,
       exact inert DecisionPolicyValidationRecord>

ValidateCompileRunRequest(
  exact ExactCompilerValueRef<CompileRunRequest>,
  exact ExactCompilerValueRef<TransformProblem> and exact CompilerResultUseAuthority<
    CheckedTransformProblem, TransformProblemValidationRecord>,
  exact ExactCompilerValueRef<DecisionPolicy> and exact CompilerResultUseAuthority<
    CheckedDecisionPolicy, DecisionPolicyValidationRecord>,
  exact authenticated ExactCompilerValueRef<SearchJob> and bounded-report
    profile when present,
  exact NamedConsumer and typed ValidateCompileRunRequest purpose,
  fresh reauthorization of every inherited bound/no-policy source disposition
    for that consumer and purpose)
  -> CompilerValidationAttemptOutcome<
       CheckedCompileRunRequest,
       exact inert CompileRunRequestValidationRecord>

TransformProblemValidationRecord {
  exact ExactCompilerValueRef<TransformProblem>,
  exact complete ExactSourceAuthorityBindingLedger and transitive source-policy
    closure read by validation,
  exact affirmative problem-validation facts,
  exact NamedConsumer and typed ValidateTransformProblem purpose,
  exact freshly checked policy/contract authorization records,
  exact Compiler semantic regime, validation contract, output-minting contract
    and result-policy coordinates, and residual trust
}

DecisionPolicyValidationRecord {
  exact ExactCompilerValueRef<DecisionPolicy>,
  exact authenticated/admitted owner schema, capability-contract, comparator,
    policy preimages, and source-binding ledger read by validation,
  exact affirmative policy-validation facts,
  exact NamedConsumer and typed ValidateDecisionPolicy purpose,
  exact freshly checked policy/contract authorization records,
  exact Compiler semantic regime, validation contract, output-minting contract
    and result-policy coordinates, and residual trust
}

CompileRunRequestValidationRecord {
  exact ExactCompilerValueRef<CompileRunRequest>,
  exact ExactCompilerValueRef<TransformProblem> and
    TransformProblemValidationResult,
  exact ExactCompilerValueRef<DecisionPolicy> and
    DecisionPolicyValidationResult,
  exact authenticated ExactCompilerValueRef<SearchJob> and bounded-report
    profile when present,
  exact capability-neutral problem/policy input-use authorization coordinates,
  exact NamedConsumer and typed ValidateCompileRunRequest purpose,
  exact inherited source-policy closure and freshly checked policy/contract
    authorization records,
  exact Compiler semantic regime, validation contract, output-minting contract
    and result-policy coordinates, and residual trust
}
~~~

~~~text
CompilerRecordResult<R> = ExactCompilerValueRef<R>

ExactCompilerCheckedResultBinding<ResultFamily,R> =
  ExactCheckedResultAuthorityBinding<Compiler, ResultFamily> whose
    semantic_coordinate is exactly the coordinate in CompilerRecordResult<R>,
    complete origin coordinates name every checked Compiler and foreign input,
    completed outcome and retained semantic facts equal exact R,
    exact producing NamedConsumer, typed producing purpose, and inert
      Compiler result-policy authorization coordinate,
    qualification, assurance, residual trust, authenticated Compiler
      operation-policy disposition, total transitive source-policy closure,
      and inert OwnerCapabilityRequirement are complete

CompilerCheckedResult<ResultFamily,R> {
  exact record_result: CompilerRecordResult<R>,
  exact owner_binding:
    ExactCompilerCheckedResultBinding<ResultFamily,R>
}

CompilerResultUseAuthority<ResultFamily,R> {
  exact checked_result: CompilerCheckedResult<ResultFamily,R>,
  separately supplied fresh matching ResultFamily capability,
  exact NamedConsumer and typed downstream-use purpose,
  fresh use authorization under the exact admitted
    CompilerResultOperationPolicy retained by checked_result.owner_binding,
  exact immediate and transitive source-policy closure retained by the checked
    result plus fresh conjunctive authorization under every bound policy, and
    fresh contract/ABI confirmation for every explicit no-policy disposition
}

CompilerCheckedResultLedger = CanonicalTypedLedger<
  exists exact ResultFamily and R:
    exact CompilerCheckedResult<ResultFamily,R>>

CompilerResultUseAuthorityLedger = CanonicalTypedLedger<
  exists exact ResultFamily and R:
    exact CompilerResultUseAuthority<ResultFamily,R>>

LocalCompilerAttemptInputHandle =
  fresh owner-issued process-local nonserializable opaque input-material handle

CompilerAttemptSlotStatus =
    Authenticated(exact capability-neutral typed value, binding, contract,
                  policy, or reference required by that slot)
  | OfferedCandidate(exact capability-neutral typed candidate and any claimed
                     reference or binding)
  | Missing
  | OpaqueMalformed(exact normalized defect class,
                    exact LocalCompilerAttemptInputHandle)

CompilerCheckingAttemptInput<T,R> {
  exact owner-selected Compiler operation entry point,
  exact expected result family T and completed-record schema R,
  exact statically declared operand-slot schema for that entry point,
  exactly one CompilerAttemptSlotStatus for every and only declared input slot,
  exact slot-to-operation association,
  no output slot, live capability, or claim that an operation occurrence
    happened
}

PrepareCompilerCheckedOperation<T,R>(
  exact CompilerCheckingAttemptInput<T,R>,
  occurrence-local capability offers for the declared authority slots, which
    may be absent, stale, nonmatching, malformed, or prohibited and are never
    retained)
  ->
    Ready(exact typed complete operand tuple for the selected operation,
          including its complete
            CompilerResultMintingAuthority<exact result family T>)
  | Rejected(exact CompilerAttemptDisposition,
             exact failed requirement and reached policy/contract checks)

AttemptCompilerCheckedOperation<T,R>(
  exact CompilerCheckingAttemptInput<T,R>,
  occurrence-local capability offers)
  -> CompilerValidationAttemptOutcome<T,R>

CompilerAttemptDisposition =
    Unsupported(exact unsupported family, model, operation, or boundary)
  | CannotAnswer(exact unavailable prerequisite or unresolved dependency)
  | Refused(exact missing authority or policy prohibition)
  | Malformed(exact offered-input, identity, association, or framing defect)
  | CheckerFailure(exact normalized operational-failure class)

CompilerAttemptRecord<T,R> {
  exact CompilerCheckingAttemptInput<T,R>,
  exact capability-neutral complete operand projection when preparation reached
    Ready, or exact rejected slot and preparation state otherwise,
  exact available ExactSourceAuthorityBindingLedger and
    CompilerCheckedResultLedger actually presented,
  exact missing, mismatched, stale, prohibited, or failed requirements without
    embedding any live capability,
  exact reached NamedConsumer and typed attempted-operation purpose, or exact
    slot status showing why either coordinate was unavailable,
  exact reached Compiler semantic regime, validation contract, admitted output-
    minting contract and result-policy coordinates, or exact slot status
    showing why any coordinate was unavailable,
  exact successful and failed policy/contract checks that were reached,
  exact CompilerAttemptDisposition and
    Reached(exact residual trust)
      | Unavailable(exact validation/trust slot status)
}

CompilerAttemptAudit<T,R> =
    Portable(exact CompilerAttemptRecord<T,R>,
             exact Id(exact CompilerAttemptRecord<T,R>))
  | OwnerLocal(exact CompilerAttemptRecord<T,R>,
               exact LocalCompilerHandle<
                 CompilerAttemptRecord<T,R>,
                 exact CompilerOwnerInstanceGeneration>)

CompilerAttemptAuditLedger = CanonicalTypedLedger<
  exists exact T and R: exact CompilerAttemptAudit<T,R>>

CompilerNotAttemptedRecord<T,R> {
  exact expected result family T and completed-record schema R,
  exact requirement coordinate and enclosing resolution, assessment, or report
    association,
  exact policy- or request-defined nonsemantic scheduling or short-circuit
    reason,
  no checked-result binding or live capability
}

CompilerNotAttemptedRecordLedger = CanonicalTypedLedger<
  exists exact T and R: exact CompilerNotAttemptedRecord<T,R>>

CompilerValidationAttemptOutcome<T,R> =
    Completed(exact inert CompilerCheckedResult<T,R>,
              fresh process-local T bound to that exact checked result)
  | Unsupported(exact CompilerAttemptAudit<T,R> whose disposition is
                Unsupported)
  | CannotAnswer(exact CompilerAttemptAudit<T,R> whose disposition is
                 CannotAnswer)
  | Refused(exact CompilerAttemptAudit<T,R> whose disposition is Refused)
  | Malformed(exact CompilerAttemptAudit<T,R> whose disposition is Malformed)
  | CheckerFailure(exact CompilerAttemptAudit<T,R> whose disposition is
                   CheckerFailure)

CompilerRequirementEvaluationEntry<T,R> =
    Checked(exact CompilerCheckedResult<T,R>)
  | Unresolved(exact CompilerAttemptAudit<T,R>)
  | NotAttempted(exact CompilerNotAttemptedRecord<T,R>)
~~~

Only `Completed` atomically returns a record body with its exact portable
content identity or value-derived owner-local handle, creates the Compiler-
owned checked-result binding, and mints the named capability. A portable
branch is legal only when the complete record preimage is portable; otherwise
the owner-local branch applies under the rule below. U/C/R/M/F return an exact
typed, capability-neutral attempt audit but no checked record result, checked-
result binding, or capability. An attempt audit is nonauthoritative: it can
support only an exact audit-record-relative statement or unresolved-slot
accounting inside an independently checked enclosing ledger. It cannot
authenticate that an operation occurred or failed, establish or negate a semantic proposition, discharge an input
requirement, justify exclusion, or substitute for a `CompilerCheckedResult`.

`CompilerCheckingAttemptInput<T,R>` is the total capability-neutral outer
carrier for every checked Compiler operation. The owner-selected entry point
fixes its operand schema, so missing or malformed framing, consumer, purpose,
validation, source, use-authority, mint-contract, result-policy, or mint-
authority slots remain representable without constructing a complete call.
Fresh capabilities are supplied separately and never enter the carrier or
audit. Only `Ready` executes the displayed operation signature; `Rejected`
constructs the matching `CompilerAttemptAudit<T,R>`. An
`OpaqueMalformed` slot names its noncanonical material only through
`LocalCompilerAttemptInputHandle` and forces the audit into the owner-local
lane. Neither that handle nor an audit establishes an operation occurrence or
history fact.

A `CompilerAttemptAudit<T,R>` is `Portable` only when its complete canonical
preimage is portable **and** every reached applicable Compiler result policy
and foreign-source owner policy expressly permits audit-record creation,
stable equality linkage, and disclosure for the exact reached
`NamedConsumer` and typed attempted-operation purpose. An authenticated
owner-contract no-policy disposition must itself state the corresponding
audit-disclosure rule; absence is not permission. If consumer, purpose, any
governing policy/disposition, or the permission check is unavailable or cannot
be authenticated, the audit defaults to `OwnerLocal`. A rejection caused by a
prohibited semantic use does not by itself authorize a portable record of that
rejection.

`NotAttempted` is likewise bookkeeping scoped by its enclosing resolution or
assessment body, not evidence
that a result is globally unavailable. Each validation record retains the exact body/ID,
Compiler semantic regime, validation contract, complete typed source-authority-
binding ledger and transitive policy closure actually read, exact named
consumer and typed validation purpose, every freshly checked policy/contract
authorization, and residual trust;
each fresh capability retains that exact `CompilerCheckedResult`. Compiler-owned capabilities
are consumed only through `CompilerResultUseAuthority`: the operation matches
the inert checked result and fresh capability exactly and freshly authorizes
the new consumer and purpose. The output-minting authority for the consuming
operation cannot substitute for this input-use authorization. Compiler-owned
results do not pretend to be foreign `ExactOwnerResultBinding` values.

Attempt-audit identity obeys the same portability and transitive owner-local
taint rule as checked records. Its canonical portable preimage contains no
process identity, timestamp, ambient exception text, live capability, or
unstable diagnostic string; an occurrence-dependent or confidential diagnostic
uses `OwnerLocal`. Replaying or checking an attempt audit can authenticate only
its exact association, canonical integrity, and submitted record shape--not an
actual attempt, failure, or run-history occurrence. Such an occurrence claim
would require a separate owner-authenticated occurrence or log binding, which
Stage 4A does not define. A
semantic replay must reconstruct every checked result on which its claim
depends; an attempt audit may be retained without reproducing the failure only
when an independently checked short-circuit, open-report scope, or external
certificate proves that no semantic conclusion depends on it.

~~~text
TransformProblemValidationResult = CompilerCheckedResult<
  CheckedTransformProblem, TransformProblemValidationRecord>

DecisionPolicyValidationResult = CompilerCheckedResult<
  CheckedDecisionPolicy, DecisionPolicyValidationRecord>

CompileRunRequestValidationResult = CompilerCheckedResult<
  CheckedCompileRunRequest, CompileRunRequestValidationRecord>
~~~

Problem validation checks all referenced predecessor and regime coordinates,
transform-intent typing, requested relation/map surfaces, and total semantic
read closure. Policy validation checks schema closure, absence of future
candidate-specific facts, qualification and assessment separation, typed
constraints/objectives, comparator domains and laws, deterministic tie/
representative rules, requested result strength, and every accepted source-
policy/capability-contract schema. Request validation checks exact problem and
policy equality, retains the complete `TransformProblemValidationResult` and
`DecisionPolicyValidationResult` plus their capability-neutral downstream-use
authorization coordinates, authenticates the operational job, and ensures that
a bounded exploration profile affects only the explicitly requested weaker
report.
Failure of any validation is an outer non-result with an exact nonauthoritative
attempt audit, never candidate exclusion or a Compiler decision.

## 4. Identity discipline

Every durable, portable Compiler identity is domain-separated and regime-
qualified:

~~~text
Id(T) = H(domain_tag, CompilerSemanticRegimeId,
          CanonicalEncode_regime(T))
~~~

The canonical preimage contains exact finite semantic values and typed content
references. It contains no live capability, pointer, dynamic callback, mutable
registry, producer session, checking-process identity, wall-clock value, or
incidental serialization spelling.

The principal identities are distinct:

~~~text
TransformProblemId
DecisionPolicyId
CompilerSemanticCapabilityContractId
CompilerResultOperationPolicyId
CompilerAdmissionCapabilityContractId<S>
CompileRunRequestId
SearchJobId
SearchJobOccurrenceId or LocalSearchJobOccurrenceHandle
ProposalOccurrenceId
ProposalOccurrenceUseRecordId
ProposalScopeId
DeclaredAlternativeId
AlternativeResolutionLedgerId
AlternativeResolutionCoverageRecordId
SemanticPathId
TransitionCaseId
QualificationId
CanonicalQualificationSetId
CandidateId
CandidateQualificationRecordId
CompilerLegalityRecordId
CandidateDomainPolicyId
CandidateDomainPolicyValidationRecordId
CandidateQuotientId
CandidateQuotientClassId
CandidateDomainId
AssessmentInputPortfolioId
QualificationInputProjectionId
AssessmentInputCompletenessRecordId
AssessmentInputUseRecordId
QualificationResolutionLedgerId
ComparisonAlternativeId
ComparisonAlternativeDomainId
AssessmentId
AssessmentLedgerId
DecisionId
CompilerReplayBundleId<D,Q>
CompilerSelectedTargetHandoffBundleId<D,Q>
CompilerOpenReportRecordId
CompilerOpenReportReplayBundleId<R>
~~~

Changing a producer, recipe, search order, proof derivation, or checking
occurrence does not by itself change transition meaning. Changing an exact
source or target, semantic path, relation proposition, observer, model,
hypothesis, intentional change, domain scope, constraint, objective,
comparator, or accepted qualification changes the corresponding semantic
identity.

IDs authenticate exact semantic coordinates after their owner checks them.
Possession of an ID or matching bytes grants no live authority.

### 4.1 Transitive owner-local dependency rule

The following is a normative typing and notation law for every type-exact prose
statement, schema, and code block under `docs-next/compiler/`. It closes the
local lane at the ABI rather than merely describing it in prose. Unless a
sentence explicitly defines or discusses the portable lane, a bare
localizable `TId` in prose denotes the same `CompilerValueCoordinate<T>`
category defined below, not an assertion that a public ID exists.

`LocalizableCompilerValueFamily` contains `TransformProblem`, `DecisionPolicy`,
`CompileRunRequest`, `SearchJob`, `ExplorationSpace`, `ProposalOccurrence`,
`ProposalOccurrenceUseRecord`, `ProposalScope`, `DeclaredAlternative`, every
alternative-resolution body, `SemanticPath`, `TransitionCase`, `Qualification`,
`CanonicalQualificationSet`, `CanonicalQualificationSupportBindingLedger`,
`Candidate`, every candidate-qualification, legality, domain-policy, quotient,
and domain body, every qualification projection/resolution and comparison-
alternative body, every portfolio, input-use, constraint, objective,
assessment, closure, report, and decision body, and every Compiler-owned
checked-result record that retains any of those coordinates.

For every such exact family `T`, all Compiler pages are desugared as follows:

1. a phrase `exact T and TId`, `exact T with matching TId`, or equivalent body-
   plus-ID operand means one `exact ExactCompilerValueRef<T>`;
2. a bare `TId`, `*_id`, `TId`-keyed map, or `TId`-member set that refers to an
   already formed `T` means `CompilerValueCoordinate<T>`; a field name ending
   in `_id` is a display label and never forces the `Portable` branch;
3. an equation `TId = Id(exact T)`, an explicitly written `Portable(...)` arm,
   or explicitly portable-only replay/cache text denotes the real public
   content ID and therefore requires a portable complete preimage;
4. if any identity-bearing child coordinate is `OwnerLocal`, `T` has no
   portable `TId`; its exact reference must use the `OwnerLocal` branch and
   every later value whose preimage names it propagates that branch; and
5. canonical sets, sequences, maps, quotient carriers, and ledger keys range
   over `CompilerValueCoordinate<T>`. A collection containing any local member
   is itself owner-local and uses the same-generation total order below.

This closed rule applies in particular at `ProposalScope`/declared-alternative/
alternative-resolution closure, `CandidateDomain`, qualification resolution,
`ComparisonAlternativeDomain`, and assessment-ledger boundaries. It does not
rewrite a foreign-owner ID, `CompilerSemanticRegimeId`, any foundational
Compiler admission/capability-contract or result-operation-policy ID, the
custom `SearchJobOccurrenceRef`, or a replay-bundle ID. Those types retain
their explicitly declared contracts; the portable-only selected-target
handoff-bundle ID likewise retains its dedicated contract. Cold replay and persistent cache lookup
require every applicable `CompilerValueCoordinate<T>` to be `Portable`.

Compiler may consume an owner-local confidential reference or an Analysis,
Relations, Stage 4B, Evidence, or other peer-owner local handle only in the
same process, for the exact named consumer and purpose authorized by its source
policy. Any Compiler value whose own canonical identity preimage directly
contains such a reference or handle, or contains another local handle through
an identity-bearing child field, receives no portable `*Id` from the list
above. From the first affected node along those forward identity edges Compiler
uses:

~~~text
LocalCompilerHandle<T, CompilerOwnerInstanceGeneration>
~~~

Within an operation whose exact Compiler owner instance and process generation
are already fixed, `LocalCompilerHandle<T>` is the shorthand for
`LocalCompilerHandle<T, that exact CompilerOwnerInstanceGeneration>`. The
generation parameter is never omitted from the actual value or equality rule.

The Compiler owner allocates this opaque handle in a collision-free domain from
an injective owner-internal canonical encoding of the complete typed local
value and every upstream local handle. Equality exists only inside that exact
Compiler owner instance and process generation. It is not a pointer, public
content hash, semantic-regime ID, serializable token, portable reference, or
authority. Handles from different owner instances or process generations never
compare equal.

The same complete injective owner-internal encoding defines one deterministic
total order for local maps, sets, deduplication, canonical `D` and `Q`
sequences, total ledgers, and representative selection. This order is valid
only inside the same Compiler owner instance and generation. Local handles from
different generations are incomparable, and neither their order nor a selected
minimum is portable.

`Portable` and `OwnerLocal` coordinates are never equal. An owner-local
coordinate resolves only through the exact owner/generation association in its
`ExactCompilerValueRef<T>`; that inert association grants no checking or use
authority. No owner-local reference or collection serializes, enters a public
digest, replay bundle, persistent cache key, or public disclosure channel.

Local dependency taint propagates forward across problems, policies, requests,
proposals, semantic paths, transition cases, qualifications, candidates,
domains, portfolios, completeness and use results, constraints, objectives,
assessments, closure and resolution ledgers, comparisons, reports, decisions,
replay material, and every derived identity exactly when the later value's own
identity preimage names the local input or an already local child. It does not
propagate backward into an otherwise independent earlier semantic value merely
because a later check used private support. No public record, digest, cache
key, replay bundle, or persistent identity may expose the local input, its
handle, or a value derived from it. The full derived chain remains process-
local, nonpersistable, non-public, and restricted by the conjunction of every
source owner's policy.

An authorized confidential rerun creates a fresh upstream local handle chain
and therefore a fresh affected Compiler handle chain; it is not exact replay.
A portable Compiler identity becomes possible only through a separately
specified source-owner protected stable confidential identity and replay
contract, or when the Compiler result is demonstrably independent of every
local input under an explicit checked rule. This target assumes neither.

## 5. End-to-end state discipline

The full order is:

~~~text
validate TransformProblem and DecisionPolicy
  -> validate the exact CompileRunRequest and bounded-report profile when a
     run/request-relative producer, scope, or report is used
  -> run or omit replaceable unauthoritative search
  -> freeze one cycle-free ProposalScope and DeclaredAlternative set
  -> for every declared alternative, ask PIR to authenticate and admit every
     semantic target and intermediate named by that alternative
  -> ask exact owners to check every required transition and lineage meaning
  -> form and qualify CandidateIds for affirmative transition cases
  -> validate the exact CandidateDomainPolicy under the checked problem and
     decision policy
  -> check every non-singleton CandidateQuotient needed by duplicate resolution
  -> finalize one total AlternativeResolutionLedger and independently check
     AlternativeResolutionCoverage, retaining every unresolved outcome and
     every complete quotient checked result and exact result-use authority it
     reads
  -> form one exact scoped CandidateDomain from the checked canonical image
  -> Compiler checks problem-local legality for candidate assessments
  -> freeze candidate-indexed qualification-only input projections
  -> check projection completeness and exact qualification-input use separately
  -> resolve every candidate through one total QualificationResolutionLedger
  -> derive one exact ComparisonAlternativeDomain
  -> freeze candidate-indexed assessment input portfolios
  -> check portfolio completeness and exact assessment-input use separately
  -> form total Checked/Unresolved/NotAttempted input-use, constraint, and
     objective evaluation accounting and the total assessment ledger
  -> check one decision-relative assessment-sufficiency basis
  -> for CompleteAssessment, deterministically recompute exact comparison,
     Pareto, tie, and representative policy; for ExternalCertificate, recheck
     and extract only the exact certified payload and apply only its supported
     representative or optional totalization rule
  -> emit a scoped closed decision
~~~

An independent side exit is available after `DecisionPolicy` has been checked:

~~~text
checked DecisionPolicy
  + any exact reached qualified subset
  + every exact reached closure result the report actually reads
  + audit/not-attempted/blocker accounting for every claimed slot
  -> independently check and emit an explicitly open report

preparation or checking failure at any reached operation
  -> exact outer U/C/R/M/F outcome
~~~

The report side exit does not require closed `D` or `Q`, total qualification
resolution, total assessment accounting, or an assessment-sufficiency basis.
Those objects are prerequisites only for a closed decision.

An operation may stop at any qualified non-result. Later stages cannot convert
that state into an earlier affirmative or negative fact.

## 6. Live capabilities

Only current owner checks mint process-local authority. Representative
capabilities are:

~~~text
CheckedTransformProblem
CheckedDecisionPolicy
CheckedCompileRunRequest
CheckedProposalOccurrenceUse
AlternativeResolutionCoverage
AdmittedProtocol<P>                 // PIR-owned
CheckedTransition<F>                // exact relation owner
CheckedCompilerLegality<CompilerLegalityCompletedOutcome>
QualifiedCandidate
CheckedCandidateDomainPolicy
CheckedCandidateQuotient<CandidateQuotientId>
CheckedCandidateDomain<D>
CheckedQualificationInputProjection
CheckedQualificationResolution<D>
CheckedComparisonAlternativeDomain<Q>
CheckedCandidateAssessment<D,Q>
CheckedAssessmentClosure<D,Q>
QualifiedCompilerDecision<D,Q>
QualifiedCompilerOpenReport<R>
~~~

There is no generic `Verified`, `Valid`, `Legal`, `Preserved`, or
`AcceptedCandidate` super-capability. An affirmative constraint requires the
exact affirmative input capability. A fact-retaining negative may satisfy only
an explicitly negative constraint. Capability conversion requires a named
checked rule.

A durable record, signature, theorem name, score, cache entry, proof file, or
prior decision cannot be deserialized into any capability. Process reset
requires owner-specific replay and fresh capabilities.

## 7. Qualified outcomes and decision strength

Every Compiler operation preserves the shared outer distinctions:

~~~text
Affirmative
Negative(retained exact facts, only where the operation defines a negative)
Unsupported
CannotAnswer
Refused
Malformed
CheckerFailure
~~~

Compiler-specific progress additionally distinguishes terminal classification
from unresolved work. A failed search, unavailable relation, unanswered
Analysis request, missing objective, invalid certificate, or interrupted
checker is not candidate ineligibility.

Closed decision claims are always scoped:

~~~text
BestInSubmittedCandidateSet<D,Q>
BestInResolvedSubmittedScope<S,D,Q>
BestInEnumeratedClosedDomain<D,Q>
BestInCertifiedSymbolicDomain<D,Q>
CompleteParetoFrontierIn<D,Q>
NoEligibleCandidateIn<D,Q>
~~~

Open work may return a qualified feasible candidate, a nondominated set in the
exact assessed subset, or an incomplete-search report. It mints no closed-
domain, optimality, global-frontier, or `NoEligible` capability.

`D` is the semantic candidate domain. A total qualification-resolution ledger
over `D` derives `Q`, the comparison-alternative domain, and the assessment
ledger is keyed by `Q`. Every closed decision binds both domains.

`NoEligibleCandidateIn<D,Q>` is a successful bounded negative decision only
after total terminal qualification resolution closes exact `Q` from closed
`D`, followed by checked decision-sufficiency coverage of every post-`Q` member
through terminal assessment facts, exact policy-approved irrelevance, or one
matching independently checked affirmative infeasibility certificate. Neither
irrelevance nor a certificate bypasses `D`/`Q` closure. The result is not another spelling for unsupportedness, refusal,
malformation, checker failure, empty heuristic output, or incomplete search.

## 8. Extension law

The production surface is open; the authority surface is closed and
versioned.

The following may change without new semantic meaning when they retain the
same exact contracts:

- producer, search algorithm, scheduling strategy, or cache;
- MLIR transform, e-graph engine, optimizer, solver, or manual authoring tool;
- proof search tactic or proof producer; and
- checker implementation independently authenticated against the unchanged
  exact checker contract, with a new validation-basis and trust identity.

The following require a new reviewed semantic profile or regime:

- transform intent or transition family;
- path, lineage, or quotient semantics;
- proposal-scope, resolution, candidate-domain, or symbolic-closure meaning;
- qualification-resolution, candidate-association, portfolio-completeness, or
  input-use policy;
- constraint, objective, comparator, Pareto, tie, or representative meaning;
- qualified outcome or negative meaning; or
- persistence and replay contract.

Unknown semantic tags are `Unsupported`. A dynamic plugin, callback, producer
assertion, or solver-success flag cannot acquire authority by registration.
Cross-version reuse requires an exact checked interpretation or transport
result; existing IDs are never reinterpreted.

## 9. Reversal triggers

This target must be reopened if an exact counterexample shows that:

1. problem meaning cannot be separated from producer or decision policy;
2. a valid consumer must identify a semantic candidate by mutable search
   history rather than exact target and transition meaning;
3. path differences can always be erased without reading lineage, assumptions,
   properties, costs, replay, or downstream facts;
4. a closed decision cannot state domain closure and checked decision-
   sufficiency coverage without trusting producer discovery state;
5. a required Compiler fact cannot retain its exact owner, polarity,
   hypotheses, assurance, and residual trust;
6. cold replay necessarily depends on rerunning a mutable producer rather than
   rechecking frozen semantic material; or
7. the Stage 4B or Evidence boundary creates an unavoidable authority cycle.

Search convenience, current code organization, migration cost, ecosystem
popularity, or a provider API is not a reopening reason by itself.

## 10. Exact nonclaims

This target does not establish:

- existence of any valid transform or candidate;
- admission, equality, refinement, intentional-change conformance, relation
  satisfaction, property truth, or property transport for any Protocol;
- truth or adequacy of any theorem, model, checker, certificate, or trust root;
- completeness of a producer search or candidate domain;
- eligibility, an objective value, Pareto completeness, selection, or
  `NoEligible` for any concrete request;
- optimality beyond one exact declared closed domain;
- OIR projection, endpoint feasibility, realization, deployment, invocation,
  performance, or runtime success;
- cryptographic security, implementation correspondence, release readiness,
  compatibility, migration feasibility, or normative cutover; or
- persistence of live authority.
