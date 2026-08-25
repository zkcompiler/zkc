# Analysis semantic model

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Target status:** Stage 4A durable promotion
> **Provisional owner:** `analysis`
> **Authority:** This document specifies the selected target for `docs-next/`.
> It is non-normative until explicit consolidation and cutover. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> This document makes no implementation, migration, compatibility, theorem,
> property-establishment, or consumer-reliance claim.

> **K1 transition notice — 2026-08-26:** The identity, canonical-value,
> algorithm, dependency, and evaluation forms below predate
> [Executable Semantic Foundations](../foundation/executable-foundations.md).
> K3 must reconcile Analysis inputs and checked results with the exact K1
> substrate and the K2 Protocol model; this page is not yet an integrated
> K1-aligned Analysis calculus.

## 1. Scope and architectural position

Analysis owns reusable post-admission evaluation of exact semantic questions.
Its target is a **federated typed calculus**:

~~~text
exact admitted subjects and owner-created views
  + one family-owned question and semantic model
  + an exact typed hypothesis context
  + a direct, internal, external, certificate, or Evidence-derived basis
  -> a family-owned checked proposition
  -> a qualified Analysis judgment
~~~

A small common layer owns lifecycle, identity categories, dependency closure,
checking discipline, qualified outcomes, local capabilities, replay, and
shared typed-expression primitives. It does not own a universal proposition
or result payload. Each closed family owns its subject tuple, semantic model,
question, conclusion, refutation meaning, valid basis lanes, and inference
rules.

The companion specifications divide the family surface without changing this
common contract:

- [Semantic relation families](semantic-relations.md) owns equality, traces,
  refinement, declared change, distribution, cost, and the exact seam to
  Relations-owned satisfaction;
- [Cryptographic property families](cryptographic-properties.md) owns the
  completeness, soundness, knowledge, and zero-knowledge experiment families
  and Fiat--Shamir theorem applicability; and
- [Transport, composition, and replay](transport-composition-and-replay.md)
  owns heterogeneous property transport, property composition, coverage,
  cold replay, caches, residual trust, and extension law.

Analysis does not own PIR formation or admission, relation definition or
satisfaction, Protocol-to-relation correspondence, Compiler decisions, OIR
validity, endpoint facts, observations, or consumer reliance. It consumes
only the exact admitted subjects, source-owned views, and checked capabilities
provided by those owners.

## 2. Semantic categories and live authority

### 2.1 Categories that never alias

The target distinguishes:

~~~text
semantic subject
AnalysisQuestion                 // stable experiment or relation problem
AnalysisGoal                     // exact hypothesis-free conclusion
AnalysisProposition              // exact conditional truth-apt claim
AnalysisRequest                  // one operational attempt specification
AnalysisCheckingAttemptInput     // capability-neutral partial ingress
AnalysisCheckingInvocation       // fully prepared occurrence-local input
SemanticDerivationBasis          // inference meaning
ValidationBasis                  // checker and translation meaning
SupportInstantiation             // exact established premise occurrences
CheckedDerivation                // proof, refutation, certificate, or check
qualified JudgmentRecord         // inert completed outcome; durable only when policy permits
checking or replay occurrence    // one operation, not semantic content
process-local live capability    // current authority
AnalysisReplayBundle             // inert reconstruction material
~~~

No category is an alias for another. In particular:

- a theorem statement is not a zkc proposition;
- a question has no truth value until paired with an exact conclusion and
  hypothesis context;
- a timeout, tactic, proof preference, or assurance request does not change
  question or proposition meaning;
- a semantic basis is not its checker implementation;
- a proof, result record, ID, or replay bundle is not a live capability; and
- failed proof search is not a semantic refutation.

### 2.2 Authority topology

Every authority-bearing input is a fresh, opaque, process-local capability
minted by its semantic owner. Analysis receives exact admitted subject
capabilities and owner-created purpose-specific views. A successful Analysis
check may mint only:

~~~text
EstablishedAnalysisJudgment<
  F, Affirmative, AssuranceClass, FamilyOperationPolicyId,
  ExactSourceOperationPolicyDependencyClosure, NamedConsumer, OperationPurpose,
  ExactJudgmentBinding, ExactCheckedResultAuthorityBinding<Analysis, F>>
EstablishedAnalysisJudgment<
  F, Negative, AssuranceClass, FamilyOperationPolicyId,
  ExactSourceOperationPolicyDependencyClosure, NamedConsumer, OperationPurpose,
  ExactJudgmentBinding, ExactCheckedResultAuthorityBinding<Analysis, F>>

ExactRef<T> = PortableId<T> | LocalHandle<T>

ExactJudgmentBinding = {
  judgment_record: ExactRef<JudgmentRecord>,
  basis_qualification: ExactRef<BasisQualification>,
  derivation: ExactRef<Derivation>,
  support_instantiation: ExactRef<SupportInstantiation>,
  semantic_basis: ExactRef<SemanticBasis>,
  validation_basis: ExactRef<ValidationBasis>
}
~~~

Every cross-owner support input uses the project-wide
[`ExactSourceAuthorityBinding`](../project/analysis-and-compiler-architecture.md#23-capability-neutral-source-bindings):

~~~text
OwnerCapabilityRequirement {
  exact owner capability-contract identity and ABI,
  exact operand/result binding schema,
  freshness and authority-lifetime requirements
}

ExactSourceAuthorityBinding<Owner, CapabilityFamily> {
  exact owner domain and capability family,
  semantic_coordinate:
      Portable(exact owner canonical subject/admission coordinate or
               exact owner checked-result record identity)
    | OwnerLocal(exact owner subject or premise/result-record reference),
  complete owner result-origin coordinates required by the capability ABI,
  exact admitted-subject facts or completed qualified outcome, polarity when
    applicable, and semantic facts,
  exact qualification, assurance, and residual trust,
  exact authenticated owner-policy disposition,
  exact source-result transitive policy-dependency closure,
  exact OwnerCapabilityRequirement
}

ExactAdmittedSubjectAuthorityBinding =
  ExactSourceAuthorityBinding with an admitted-subject semantic coordinate

ExactCheckedResultAuthorityBinding =
  ExactSourceAuthorityBinding with a checked-result semantic coordinate

AnalysisAdmissionCapabilityContractId<S> = H(
  "zkc/analysis-admission-capability-contract",
  exact Analysis owner domain and admitted subject family S,
  family-owned well-formedness/admission contract version,
  exact capability ABI and operand/result binding schema,
  freshness and authority-lifetime requirements)
~~~

`S` ranges over every Analysis-owned admitted family profile, basis registry,
validation profile, operation policy, question, proposition, and owner-created
Analysis view. The authenticated contract and ABI explicitly declare that an
Analysis admission capability has no separate operation policy, so its source
binding uses
`OwnerDefinesNoOperationPolicy(AnalysisAdmissionCapabilityContractId<S>, ABI)`.
This is especially important when `S` is `FamilyOperationPolicy`: binding the
admission capability to the policy being admitted would create an authority
cycle. A later semantic checking result remains bound to the exact admitted
`FamilyOperationPolicyId`; only admission authority uses this acyclic no-policy
contract.

On successful family-owned admission, the owner atomically creates the exact
`ExactAdmittedSubjectAuthorityBinding<Analysis,S>` and separately mints the
fresh admission capability that retains it. For a dependent subject or view,
the binding includes every exact upstream source binding and its total
transitive policy closure; the admission operation separately receives and
freshly validates the matching capabilities and dispositions. A failed,
unsupported, refused, malformed, or checker-failed admission attempt exports
neither binding nor capability.

This binding is inert. Its `OwnerCapabilityRequirement` contains neither a live
capability token nor an occurrence identity. The source owner creates the
checked-result binding atomically with each completed qualified semantic
capability exposed as a premise and the capability retains it; a family-owned
non-completed U/C/R/M/F outcome creates neither. An Analysis invocation
receives the binding and fresh capability separately and checks complete field
equality. A portable binding may enter a support identity. An owner-local
coordinate makes only that support and its explicit downstream identity chain
local. Portable replay reconstructs the result through its source owner and
requires exact binding equality; a local rerun creates a fresh owner-local
coordinate and is not exact cold replay.

Each coordinate independently uses its portable ID or local handle according to
its own preimage. Only combinations induced by the declared identity edges are
valid: for example, a local support may produce a local derivation and judgment
while the proposition, semantic basis, validation basis, and basis qualification
remain portable. A checker validates the complete mixed binding; it never
forces unrelated public coordinates into the local lane.

There is no assurance- or policy-erased `EstablishedAnalysisJudgment<F>`
capability. Attenuation for a consumer preserves the exact proposition,
polarity, hypotheses, assurance class, residual-trust closure,
`FamilyOperationPolicyId`, transitive source-operation-policy dependency
closure, named consumer, typed `OperationPurpose`, and `ExactJudgmentBinding`.
It also preserves the complete
`ExactCheckedResultAuthorityBinding<Analysis,F>` unchanged, including its
semantic coordinate, exact origins and qualified facts, policy disposition,
transitive source-policy closure, assurance/trust coordinates, and inert
`OwnerCapabilityRequirement`.
The binding contains the exact
`JudgmentRecordId` or `LocalJudgmentRecordHandle`, `BasisQualificationId` or
local handle, derivation, support-instantiation, semantic-basis, and validation-
basis ID or local handle. A capability for a different derivation or support
record cannot satisfy that binding merely because its proposition and visible
qualification coordinates match.

An ID, byte sequence, value-shaped aggregate, theorem name, proof file, solver
response, signature, cache entry, old result record, or serialized replay
bundle never mints authority. `Unsupported`, `CannotAnswer`, `Refused`,
`Malformed`, and `CheckerFailure` produce exact attempt records but no
affirmative or negative semantic capability.

## 3. Identity and regime law

### 3.1 Canonical identity

Every durable, portable identity-bearing Analysis value follows the shared
target rule:

~~~text
Id(T) = H(domain_tag, semantic_regime, CanonicalEncode_regime(T))
~~~

The preimage contains finite typed semantic data and exact typed content
references. It contains no live capability, pointer, callback, mutable
registry, search state, checker process, wall-clock timestamp, or incidental
printer spelling. Canonical encoding is injective over the typed domain; sums
carry variant tags, ordered products and sequences retain order, maps and sets
have canonical order and reject duplicates, and references retain their
subject family and regime.

Analysis keeps independent identities for meaning, support, validation,
execution, and persistence:

~~~text
AnalysisQuestionId
AnalysisGoalId
AnalysisPropositionId
AnalysisRequestId
SemanticBasisId
ValidationBasisId
BasisQualificationId
SupportInstantiationId
DerivationId
JudgmentRecordId
AnalysisAttemptRecordId
AnalysisReplayBundleId
~~~

Changing one category does not silently change another. Several bases,
checkers, and derivations may establish the same proposition. A different
bound or residual hypothesis is a different proposition even if it answers
the same question.

#### Confidential owner-local handle lane

An owner-private nonserializable reference is not an exact typed content
reference and therefore never enters the rule above. Any Analysis value whose
own canonical identity preimage directly contains such a reference, or contains
another local handle through an identity-bearing child field, receives no
public content ID.
Analysis instead uses the corresponding opaque owner-local handle:

~~~text
LocalAnalysisQuestionHandle
LocalAnalysisGoalHandle
LocalAnalysisPropositionHandle
LocalAnalysisRequestHandle
LocalSemanticBasisHandle
LocalSupportInstantiationHandle
LocalValidationBasisHandle
LocalBasisQualificationHandle
LocalDerivationHandle
LocalJudgmentRecordHandle
LocalAttemptRecordHandle
LocalAttemptInputHandle
LocalSourceOperationPolicyDependencyClosureHandle
~~~

These handles inhabit a collision-free domain scoped by the exact Analysis
owner instance and process generation. The owner allocates them from an
injective owner-internal canonical encoding of the complete typed local value,
including every exact upstream owner-local reference. Equality is defined only
inside that owner instance and generation. A handle is not a pointer, content
hash, semantic-regime ID, serializable token, portable reference, or authority.
Different owner instances or process generations never compare equal.
When a local Analysis structure requires a map, set, deduplication, or canonical
sequence, the owner uses one deterministic total order over the complete
injective owner-internal encoding. That order is valid only inside the same
owner instance and generation; local handles from different generations are
incomparable and no ordering output is portable.

Private-reference taint propagates forward only along explicit identity-preimage
edges: a value that names a local handle in its own canonical preimage is itself
local, even when all its other fields are public. It does not propagate backward
from a private support or derivation into an otherwise independent public
question, proposition, semantic basis, or validation basis. No `*Id` in the
durable list above is emitted for a tainted value, and no digest of the handle or
derived value may be used as a surrogate public identity. The owner-private
source policy and named-consumer restriction apply to the complete forward
local-handle closure.

### 3.2 Family profile split

Every supported family closes four independently identified profiles:

~~~text
FamilySemanticProfile<F> {
  family_semantic_profile_regime_id,
  family_tag,
  subject_tuple_schema,
  semantic_view_contract_schemas,
  model_schema,
  experiment_and_occurrence_schema,
  observer_and_direction_schema,
  parameter_and_quantifier_schema,
  hypothesis_schema,
  conclusion_schema,
  family_outcome_and_refutation_schema,
  quantitative_sorts_and_operators,
  semantic_read_requirements
}

FamilyBasisRegistry<F> {
  admitted_basis_lanes,
  semantic_rule_and_theorem_contracts,
  implication_transport_composition_and_coverage_port_schemas,
  exact_semantic_basis_extension_boundary
}

FamilyValidationProfile<F> {
  validation_and_checker_contracts,
  decoder_translation_and_proof_rule_contracts,
  validation_trust_root_policy
}

FamilyOperationPolicy<F> {
  capability_contract,
  replay_contract,
  disclosure_and_trust_contract,
  operation_and_unknown_question_policy
}

SourceOperationPolicyDependencyClosure {
  every direct and transitive admitted-subject and checked-result source
    authority binding,
  exact ExactSourceAuthorityBinding, including any source Analysis
    ExactJudgmentBinding,
  assurance, residual trust, and exact OwnerCapabilityRequirement,
  exactly one owner-policy disposition:
    BoundTo(exact owner operation-policy identity and authenticated contract)
      | OwnerDefinesNoOperationPolicy(
          exact owner capability-contract identity, exact capability ABI),
  exact source-to-pre-result dependency edges whose targets include every
    invocation admitted-subject, owner-created view, question, proposition,
    family profile, basis-registry, validation-profile, target-policy,
    semantic-basis premise, and correspondence-support slot, together with its
    named operation purpose,
  total coverage of every authority-bearing invocation slot and no extra edge,
  exact named consumer and operation purposes already exercised,
  canonical finite acyclic transitive closure
}
~~~

For `ExactProposition`, the pre-result proposition target above is the exact
admitted proposition supplied by the request. For `DeriveWithin`, it is only the
request's typed result-schema slot; the closure never names a proposition that
does not yet exist. The later produced proposition and its admission binding
enter the completion-time realization ledger and checked-result origin closure,
not the pre-execution dependency closure.

`SourceOperationPolicyDependencyClosureId` identifies this exact inert closure.
It is not permission. Every mint, attenuation, use, disclosure, persistence,
cache lookup, and replay must freshly satisfy the conjunction of the target
`FamilyOperationPolicy` and every bound source-owner policy for its exact named
consumer and purpose. A source prohibition or refusal prevents that operation;
the target policy cannot replace, erase, or relax it. The
`OwnerDefinesNoOperationPolicy` variant is legal only when that owner's admitted
capability contract explicitly declares the absence, so omission is never
ambient policy erasure.

Closure edges never name the future `SupportInstantiationId`, `DerivationId`,
`JudgmentRecordId`, completed result, or corresponding local handle whose
preimage contains the closure. They terminate at cycle-free pre-result support
slots and purposes, so policy provenance cannot create an identity cycle.

`ExactSourceOperationPolicyDependencyClosure` is the durable
`SourceOperationPolicyDependencyClosureId` in the portable lane and the
`LocalSourceOperationPolicyDependencyClosureHandle` when any dependency edge is
owner-local. The latter obeys the same transitive nonpersistence rule as every
other local handle.

`semantic_view_contract_schemas` identifies source-fact meanings and complete
read contracts, not concrete adapter implementations or live view tokens.
Adding another adequate adapter for an unchanged contract therefore changes
neither family semantics nor question identity.

Only `FamilySemanticProfileId` enters `AnalysisQuestionId`. It fixes the
subject, model, experiment, observer, parameters, conclusion, refutation,
quantitative algebra, and semantic-read meaning. A rule catalog, theorem,
checker, proof lane, assurance policy, capability policy, replay purpose, or
trust policy cannot change question or proposition identity.

`FamilyBasisRegistryId`, `FamilyValidationProfileId`, and
`FamilyOperationPolicyId` enter only the basis, qualification, operation, or
replay identity that reads them. A checker implementation is authenticated
against the exact validation contract supplied to the invocation. Every check
or replay also requires a fresh process-local checker-execution capability
whose implementation identity, ABI, contract, and checked implementation-to-
contract correspondence set exactly match the admitted `ValidationBasisId`.

The v0 family set and every meaning-bearing constructor are closed and
versioned. An unknown family, model, rule, result, or refutation tag is
`Unsupported`; an ambient plugin or host callback cannot give it meaning.

### 3.3 Thin common envelope

Every family supplies:

- its exact admitted subject closure;
- owner-created views and complete semantic and basis read closures;
- its semantic model instantiation;
- observer, direction, and occurrence coordinates when meaningful;
- typed parameters and quantifiers; and
- its question result schema and proposition-specific hypothesis,
  conclusion, and refutation schemas.

The common layer does not manufacture universal optional fields. A family
without an adversary, oracle, simulator, cost model, witness, or occurrence
subject structurally omits that coordinate.

## 4. Source-owned views and read closure

Each source owner defines the view types Analysis may receive, the finite fact
vocabulary they expose, and the adequacy predicate for each read contract.
Analysis distinguishes:

~~~text
SemanticReadClosure<F> {
  every source fact and direct semantic dependency used to define the
  question's meaning
}

BasisReadClosure<B> {
  every source fact and dependency used only to validate one theorem,
  derivation, proof, certificate, direct procedure, or correspondence
}
~~~

`SemanticReadClosureId` enters `AnalysisQuestionId`.
`BasisReadClosureId` enters the exact semantic or validation basis that reads
it. Different adequate live view occurrences may reconstruct the same finite
closure; view tokens and capabilities never enter content identity.

Family-profile admission checks that the semantic closure is permitted by
every source-owned view schema. Every offered basis separately declares and
checks its complete basis closure. A read that affects proposition meaning
cannot be hidden in a checker. A proof-only read cannot be moved into the
question merely to force two basis choices to have different propositions.

At invocation time:

- a missing named view or required fact is `CannotAnswer` before semantic
  evaluation;
- a view-shaped value without matching source authority is `Refused`;
- an ill-typed or undeclared read is `Malformed` or `Unsupported` under the
  family policy; and
- the checker cannot reopen carrier bytes, consult an ambient registry, or
  infer an omitted fact.

Adding a semantic read changes the semantic profile, model, or question.
Adding a proof-only read changes the corresponding basis. Neither change may
be concealed in implementation behavior.

## 5. Question, goal, proposition, and request

### 5.1 Stable question

~~~text
AnalysisQuestion<F> {
  analysis_semantic_regime_id,
  family_semantic_profile_id,
  exact_admitted_subject_closure,
  exact_definition_and_occurrence_graph,
  exact_subject_statement_witness_trace_and_construction_maps,
  admitted_semantic_model_instance,
  family_experiment_regime,
  observer_visibility_and_direction_coordinates,
  typed_parameter_and_quantifier_context,
  semantic_read_closure,
  family_result_schema
}
~~~

`AnalysisQuestionId` identifies one stable relation or property experiment and
its permitted conclusion shape:

~~~text
AnalysisQuestionId = H(
  "zkc/analysis-question",
  AnalysisSemanticRegimeId,
  FamilySemanticProfileId,
  exact semantic subject closure,
  exact occurrence graph and semantic maps,
  ModelInstantiationId,
  experiment, observer, direction,
  alpha-normalized typed parameters and quantifiers,
  SemanticReadClosureId,
  exact family_result_schema)
~~~

It contains no residual hypothesis context, exact claimed bound or result,
theorem choice, proof bytes, checker version, timeout, worker limit, or trust
acceptance policy.

### 5.2 Exact conditional proposition

~~~text
AnalysisGoal<F> {
  question_id,
  exact_typed_conclusion
}

AnalysisProposition<F> {
  goal_id,
  hypotheses: CanonicalTypedHypothesisContext
}
~~~

The identities are:

~~~text
AnalysisGoalId = H(
  "zkc/analysis-goal",
  AnalysisQuestionId,
  family-specific exact conclusion)

AnalysisPropositionId = H(
  "zkc/analysis-proposition",
  AnalysisGoalId,
  HypothesisContextId)
~~~

`AnalysisGoalId` is a hypothesis-free conclusion subidentity. A theorem or
correspondence assumption can therefore name the exact goal without a cyclic
reference to the proposition whose context contains that assumption. A goal
is not truth-apt and grants no authority.

The proposition has explicit conditional meaning:

~~~text
Gamma |-_model Conclusion<F>(subjects, parameters, result)
~~~

Rules may discharge, inherit, strengthen, or introduce hypotheses only through
typed family operations. The final proposition contains every residual
assumption. Different bounds, metric regimes, extractor guarantees, simulator
regimes, cost values, or residual contexts produce different proposition IDs.

### 5.3 Operational request

~~~text
AnalysisRequest<F> {
  exact_question: exact AnalysisQuestion<F> and
    ExactAdmittedSubjectAuthorityBinding<Analysis, AnalysisQuestion<F>>,
  target:
      ExactProposition(
        exact AnalysisProposition<F> and
        ExactAdmittedSubjectAuthorityBinding<Analysis, AnalysisProposition<F>>)
    | DeriveWithin(F::ExactResultSchema),
  exact required owner-created semantic and offered-basis view contracts,
    references, and semantic/basis read-closure coordinates,
  offered_semantic_and_validation_bases,
  exact_family_operation_policy: exact FamilyOperationPolicy<F> and
    ExactAdmittedSubjectAuthorityBinding<Analysis, FamilyOperationPolicy<F>>,
  exact_named_consumer: NamedConsumer,
  operation_purpose: OperationPurpose,
  requested_assurance_profile,
  operational_resource_limits,
  optional_named_persistence_purpose,
  no live capability
}
~~~

~~~text
AnalysisRequestId = H(
  "zkc/analysis-request",
  AnalysisQuestionId,
  exact question admitted-subject authority binding,
  exact target proposition or derive-within result schema,
  exact proposition admitted-subject authority binding when present,
  exact required view contract/reference and read-closure coordinates,
  offered basis identities,
  exact FamilyOperationPolicyId and policy admitted-subject authority binding,
  exact named consumer and operation purpose,
  requested assurance profile,
  operational-limits profile,
  named persistence purpose when present)
~~~

A request is an unauthoritative attempt. A timeout, solver, proof assistant,
tactic, worker limit, basis preference, or operation-policy change changes
`AnalysisRequestId`, never the proposition. The exact policy governs
capability minting, replay, disclosure, trust acceptance, and unknown-question
behavior for the attempt; no ambient replacement may reinterpret the request.
`DeriveWithin` may return newly authenticated exact propositions. Failure to
find one is `CannotAnswer`, not a semantic negative.

The request is wholly capability-neutral. Its admitted-subject bindings are
inert exact source coordinates and requirements, not admission tokens. Request
construction, content identity, attempt recording, persistence, and replay
therefore never serialize authority. Preparation separately receives fresh
question, exact-target proposition when present, and policy capabilities, plus
the concrete owner-created view values, their exact bindings, and their fresh
source capabilities. It requires complete equality with every request binding,
view contract/reference, and read-closure coordinate before constructing an
`AnalysisCheckingInvocation`. Concrete view occurrences and bytes never enter
`AnalysisRequestId`.

Questions and propositions themselves are authenticated, checked for exact
identity, type, dependencies, maps, model, and read closure, then admitted by
the family. A matching ID without the resulting process-local admitted
capability is insufficient.

## 6. Hypotheses, premises, and trust

### 6.1 Canonical hypothesis graph

`AnalysisHypothesisContext` is a finite acyclic typed graph. Its leaves may be:

- declared cryptographic or hardness assumptions;
- exact unproved propositions admitted by the family;
- termination, losslessness, state-separation, or oracle restrictions;
- adversary, query, time, uniformity, or auxiliary-input restrictions;
- quantitative side conditions; or
- assumed model, statement, or subject-correspondence propositions.

ROM, QROM, ideal-permutation, CRS/SRS, trace, cost, abort, termination, and
similar coordinates that change the experiment belong to the question's
model, not to removable metadata. A theorem inside that model may still carry
exact residual hypotheses.

Established Analysis judgments and owner-provided structural capabilities are
derivation dependencies, not unresolved hypotheses. Their residual contexts
are inherited through the applied rule. Every hypothesis edge names its
substitution, direction, and discharge rule. Strings, theorem names, and
citations cannot stand in for propositions.

Contexts use alpha-normalized typed binders and a canonical acyclic DAG.
Logical equivalence is never guessed. Two differently expressed contexts have
different identities unless an exact checked rule relates them. A proposition
cannot be established solely by assuming itself, and proposition and
derivation dependencies are cycle-free.

### 6.2 Total dependency disposition

Every semantic basis includes a total ledger over every imported definition,
axiom, lemma assumption, theorem assumption, and proof-environment dependency:

~~~text
DependencyDisposition =
    EstablishedPremise(exact proposition, polarity, and semantic facts)
  | ResidualHypothesis(exact proposition)
  | DefinitionalOrLogicTrustRoot(exact definition or logic root claim)
~~~

Every truth-apt unproved proposition becomes a `ResidualHypothesis` and is
canonically unioned into the resulting proposition. An exact prior judgment
may realize an `EstablishedPremise`; its proposition, polarity, and semantic
facts affect basis meaning, while the selected record, assurance, and trust
belong to the support instantiation. Only logic or definitional adequacy may
terminate at `DefinitionalOrLogicTrustRoot`. A domain proposition cannot be
hidden there for convenience.

Logical premises and residual trust are distinct. A hardness assumption,
unproved theorem, or assumed correspondence is part of proposition meaning. A
checker, encoding, proof kernel, runtime, or normative-definition correctness
obligation belongs to the validation trust DAG described in
[Transport, composition, and replay](transport-composition-and-replay.md).

## 7. Basis, support, validation, and derivation

### 7.1 Exact structures

~~~text
SemanticDerivationBasis {
  basis_lane,
  family_semantic_profile_id and exact used semantic-profile slice,
  admitted_family_basis_registry_id and exact used registry slice,
  exact_rule_or_theorem_refs,
  exact_model_subject_and_statement_correspondence_propositions,
  exact_encodings_and_query_polarities,
  total_dependency_disposition_ledger,
  basis_read_closure,
  exact_premise_proposition_polarity_and_semantic_fact_requirements,
  substitutions_and_quantitative_transformer_contracts
}

SupportInstantiation {
  semantic_basis: ExactRef<SemanticBasis>,
  exact premise ExactCheckedResultAuthorityBinding values,
  exact correspondence-support ExactCheckedResultAuthorityBinding values,
  exact SourceOperationPolicyDependencyClosureId or local handle,
  exact_dependency_disposition_realization
}

ValidationBasis {
  admitted_family_validation_profile_id,
  semantic_basis: ExactRef<SemanticBasis>,
  exact_validation_and_checker_semantic_contracts,
  exact_checker_implementation_and_abi_identities,
  checker_implementation_and_contract_correspondence_identities,
  decoder_elaborator_translation_and_proof_rule_closure,
  validation_only_dependency_and_read_closure,
  exact_trust_root_dag
}

AnalysisBasisQualification {
  semantic_basis: ExactRef<SemanticBasis>,
  validation_basis: ExactRef<ValidationBasis>,
  assurance_class,
  residual_trust_closure_id
}

CheckedDerivation {
  exact_proposition: ExactRef<AnalysisProposition>,
  semantic_basis: ExactRef<SemanticBasis>,
  validation_basis: ExactRef<ValidationBasis>,
  support_instantiation: ExactRef<SupportInstantiation>,
  derivation_body_or_direct_check_transcript,
  premise_occurrences,
  substitutions,
  side_condition_results,
  quantitative_transform_ledger
}

PreExecutionRequestRealizationLedger<F> {
  exact AnalysisRequest<F> and matching ID or local handle,
  total no-missing/no-extra association of every admitted subject, model, view,
    basis, policy, and source binding to its declared request/question slot,
  target:
      ExactPropositionReady(exact admitted proposition binding)
    | DeriveWithinReserved(exact F::ExactResultSchema and no produced
        proposition),
  exact requested assurance profile,
  exact operational resource limits, reserved resource envelope, and terminal
    counter schema,
  exact NamedConsumer and OperationPurpose
}

CompletedRequestRealizationLedger<F> {
  exact PreExecutionRequestRealizationLedger<F>,
  exact completed proposition and its
    ExactAdmittedSubjectAuthorityBinding<Analysis, Proposition>,
  exact target realization:
      ExactPropositionEquality
    | DeriveWithinSchemaMatchAndAdmission,
  exact achieved assurance and acceptance against the requested profile,
  exact terminal accounting for every and only declared resource counter,
  total no-missing/no-extra completion coverage
}

AnalysisCheckingOccurrenceHandle =
  fresh owner-issued process-local nonserializable handle

AnalysisCheckingInvocation {
  exact authenticated AnalysisRequest value and matching ID or local handle,
  exact admitted family-semantic-profile, question, and policy capabilities with
    their exact ExactAdmittedSubjectAuthorityBinding values,
  every exact admitted semantic subject and admitted model-instance value named
    by AnalysisQuestion.exact_admitted_subject_closure or its semantic read
    closure, each complete ExactAdmittedSubjectAuthorityBinding, and each
    separately supplied fresh matching source-owner capability,
  one total no-missing/no-extra association from those values and bindings to
    the exact question subject/model closure,
  for AnalysisRequest.target.ExactProposition only, the exact admitted
    proposition capability and ExactAdmittedSubjectAuthorityBinding,
  for AnalysisRequest.target.DeriveWithin, no initial proposition capability;
    the produced proposition must later be authenticated and admitted with its
    exact binding and fresh capability before Completed,
  exact owner-created semantic and offered-basis view values, their exact
    ExactAdmittedSubjectAuthorityBinding values, and separately supplied fresh
    purpose-specific view capabilities,
  exact admitted family basis-registry and validation-profile capabilities with
    their exact ExactAdmittedSubjectAuthorityBinding values,
  exact authenticated SemanticDerivationBasis value and matching ID or local handle,
  exact authenticated SupportInstantiation value and matching ID or local handle,
  exact authenticated SourceOperationPolicyDependencyClosure value and matching
    ID or local handle,
  exact named consumer: NamedConsumer and operation_purpose: OperationPurpose,
  exact source bindings and separately supplied fresh premise and
    correspondence capabilities,
  exact authenticated source-owner policy dispositions matching every closure
    entry: complete `BoundTo` policy preimages with fresh admitted policy or
    owner-mediated purpose-check authority, or exact
    `OwnerDefinesNoOperationPolicy` capability-contract and ABI preimages with
    fresh contract admission or owner-mediated confirmation,
  exact authenticated ValidationBasis value and matching ID or local handle,
  exact PreExecutionRequestRealizationLedger<F>,
  fresh CheckerExecutionCapability<
    exact ValidationBasis ID or local handle,
    CheckerImplementationId,
    CheckerAbiId,
    CheckerContractId,
    ImplementationToContractCorrespondenceSetId>,
  checking_occurrence_handle: AnalysisCheckingOccurrenceHandle allocated only
    after successful preparation
}

AnalysisAttemptSlotStatus =
    Authenticated(exact capability-neutral typed value, binding, contract,
                  or reference required by that slot)
  | OfferedCandidate(exact capability-neutral typed candidate and any claimed
                     reference or binding)
  | Missing
  | OpaqueMalformed(exact normalized defect class,
                    exact LocalAttemptInputHandle)

AnalysisCheckingAttemptShape<F> =
    RequestUnavailable(
      exact request-slot status whose variant is Missing or OpaqueMalformed;
      no request-derived child-slot obligation)
  | RequestParsed(
      exact capability-neutral AnalysisRequest<F>,
      exact request-slot status whose variant is Authenticated or
        OfferedCandidate,
      exact required-slot schema derived from that request, including the exact
        target variant,
      exactly one AnalysisAttemptSlotStatus for every and only derived request
        and AnalysisCheckingInvocation slot, excluding the request root and
        owner-generated AnalysisCheckingOccurrenceHandle,
      exact slot-to-schema association)

AnalysisCheckingAttemptInput<F> {
  exact expected family F and AnalysisSemanticRegimeId,
  exact AnalysisCheckingAttemptShape<F>,
  no live capability and no claim that an attempt occurrence happened
}

PrepareAnalysisCheckingInvocation(
  exact AnalysisCheckingAttemptInput<F>,
  occurrence-local capability offers for the declared authority slots, which
    may be absent, stale, nonmatching, or prohibited and are never retained)
  ->
    Ready(allocate a fresh AnalysisCheckingOccurrenceHandle and construct the
          exact AnalysisCheckingInvocation bound to it)
  | Rejected(exact AnalysisAttemptDisposition<F>,
             exact failed requirement and reached policy/contract checks)

AttemptAnalysisChecking(
  exact AnalysisCheckingAttemptInput<F>,
  occurrence-local capability offers)
  -> AnalysisAttemptOutcome<F>
~~~

The semantic basis identifies inference meaning. The support instantiation
identifies the exact established source bindings and capability requirements that
must realize its premises. Fresh matching capabilities are occurrence-local
operation inputs and never enter the support content identity. The validation
basis identifies how that basis and derivation were checked. None changes
proposition meaning.

`AnalysisCheckingAttemptInput<F>` is the capability-neutral outer carrier that
makes missing, malformed, unauthenticated, stale, and prohibited offers
representable without pretending a fully populated invocation already exists.
Malformed material with no canonical typed identity is named only by a fresh
owner-local `LocalAttemptInputHandle`; that handle is not portable, is not
authority, and establishes no historical occurrence. `AttemptAnalysisChecking`
first resolves the total slot ledger and separately supplied capability offers.
Only `Ready` constructs an `AnalysisCheckingInvocation` and may proceed to
semantic execution. Every `Rejected` branch constructs the matching
capability-neutral attempt record and can never reach `Completed`.

The freshly allocated `AnalysisCheckingOccurrenceHandle` identifies only the
live prepared operation. It is excluded from request, proposition, derivation,
judgment, completed-result, attempt-record, and replay identities; it is never
serialized or persisted and does not establish a historical occurrence. Any
policy-permitted audit association instead uses a separately allocated inert
record-relative reference.

`AnalysisCheckingInvocation` is the resulting occurrence-local fully typed
input, not a serializable value or a content-identity preimage. Before
execution, the family
matches the admitted family semantic profile, question, and target operation
policy to their exact admitted-subject bindings and separately supplied fresh
capabilities. For `ExactProposition` it performs the same match for the offered
proposition. It independently matches every underlying admitted semantic
subject and model value to its complete owner-created binding and separately
fresh source-owner capability. The association must cover every and only entry
named by the question's admitted-subject and semantic-read closures; an
Analysis-owned admitted-question capability is not a receipt for current PIR,
Relations, or other source-owner authority. It also
matches every source-owned semantic or offered-basis view value to its exact
`ExactAdmittedSubjectAuthorityBinding` and separately supplied fresh view
capability. The concrete view contract, read manifest/attenuation, source
subject, named consumer, and typed purpose must all agree. View-shaped values
offered at preparation time and inert view contracts, references, or read-
closure coordinates stored in the request never substitute for this authority.

Before execution, the family checks the complete
`PreExecutionRequestRealizationLedger<F>`. The selected semantic and validation
bases must be exact members of the request's offered set. Every subject/model
entry must match exactly one admitted value, binding, fresh capability, and
authenticated source-policy disposition, with no missing or ambient source.
An `ExactProposition` target reserves its exact admitted proposition binding. A
`DeriveWithin` target reserves only the exact result schema and explicitly
contains no produced proposition. Requested assurance, the resource envelope,
the terminal counter schema, the named consumer, and the operation purpose must
all match the exact request. The ledger is rejected before checking if any
association, reservation, or authority match is incomplete.

After semantic and validation execution, but before `Completed`, the family
seals the exact `CompletedRequestRealizationLedger<F>`. For
`ExactProposition`, the checked proposition must equal the reserved target. For
`DeriveWithin`, the produced proposition must answer the identical question,
satisfy the reserved result schema, traverse its own authentication and
admission lifecycle, and yield both an exact
`ExactAdmittedSubjectAuthorityBinding<Analysis,Proposition>` and a separately
fresh matching admitted-proposition capability. The family then checks achieved
assurance against the requested profile and closes exact terminal accounting
for every and only declared resource counter. A target, schema, admission,
assurance, limit, or accounting failure yields the exact family-owned
noncompleted branch and cannot construct a completed ledger, checked-result
binding, or live judgment capability.

It then
checks every fresh premise and correspondence capability against the inert
semantic-basis and support requirements, requiring exact equality among the
semantic basis, support instantiation, validation basis, and checked derivation,
including the selected judgment-record, basis-
qualification, derivation, support, semantic-basis, validation-basis, assurance,
trust, and source-operation-policy dependency binding. It freshly verifies that
the target operation policy and every contributing source-owner policy permit
this exact consumer and `OperationPurpose`; every explicit no-policy disposition
must match its freshly validated owner capability contract. The request, authenticated source-
policy closure, invocation, completed result, judgment record, and live
capability must bind and compare exactly the same named consumer and purpose. It
checks the fresh checker-execution
capability against the stable implementation, ABI, contract, and correspondence
identities in the validation basis. The completed live derivation occurrence and resulting live
judgment capability retain this exact match. Durable semantic derivation and
judgment records retain only their declared semantic, support, validation,
policy, and trust fields. Separate policy-permitted attempt or audit records
may retain the request ID and a separately allocated inert record-relative
reference, never the checking occurrence handle. Neither record class encodes
or rehydrates a live capability or authenticates actual run history.

A target, offered-basis, assurance, or resource mismatch produces the exact
family-owned `CannotAnswer`, `Refused`, `Malformed`, or `CheckerFailure` outcome
appropriate to the failed boundary. It never becomes a semantic negative and
no completed capability or judgment is attributed to that request.

If a question, proposition, premise, support instantiation, or other value's own
identity preimage contains an owner-local source coordinate or local handle,
that value and every later value whose own preimage names its
local handle use the owner-local lane defined in Section 3.1. Depending on the
actual identity graph, this may affect a question, goal, proposition, request,
semantic basis, support instantiation, validation basis, basis qualification,
derivation, judgment, attempt record, or derived result; no category is tainted
merely because a separate later support choice is private. The exact family
operation policy must preserve the source owner's named-consumer disclosure
restriction and prohibit persistence, public disclosure, public digesting, and
any exact cold-replay claim for the entire chain. Same-process use is limited to
the owner-authorized consumer.

A later authorized confidential rerun creates a new private occurrence and
therefore new local handles exactly for values whose own preimages name or
forward-reference the new local coordinate, plus a fresh live capability.
Public semantic values whose preimages do not read it remain equal. Relating either local proposition to
another requires a separate checked family rule. A cross-process exact result
would require a separately specified protected stable confidential-record
identity and replay contract; this target does not infer one from a local
reference.

### 7.2 Exact record identities

The following formulas apply only to the durable, untainted lane. A durable
support instantiation may contain portable exact source bindings, but never an
owner-local source coordinate or local handle.

~~~text
SemanticBasisId = H(
  "zkc/analysis-semantic-basis",
  exact basis_lane,
  FamilySemanticProfileId and exact used semantic-profile slice,
  admitted FamilyBasisRegistryId and exact used registry slice,
  rules/theorems, correspondences, encodings, exact query polarities,
  semantic-basis dependency closure, BasisReadClosureId,
  exact premise PropositionIds, required polarities and semantic facts,
  DependencyDispositionLedgerId, substitutions, transformers)

SupportInstantiationId = H(
  "zkc/analysis-support-instantiation",
  SemanticBasisId,
  exact portable premise ExactCheckedResultAuthorityBinding values,
  exact portable correspondence-support ExactCheckedResultAuthorityBinding values,
  SourceOperationPolicyDependencyClosureId,
  exact total DependencyDispositionLedger realization)

ValidationBasisId = H(
  "zkc/analysis-validation-basis",
  admitted FamilyValidationProfileId,
  SemanticBasisId,
  exact checker contracts, implementations, and CheckerAbiId values,
  exact implementation-to-contract correspondence identities,
  elaborator/decoder/translation/proof-rule closure,
  validation-only read closure,
  ResidualTrustClosureId)

JudgmentRecordId = H(
  "zkc/analysis-judgment",
  answered AnalysisPropositionId,
  exact semantic affirmative-answer projection or NegativeAnswerId,
  DerivationId,
  SupportInstantiationId,
  SemanticBasisId,
  ValidationBasisId,
  FamilyOperationPolicyId,
  SourceOperationPolicyDependencyClosureId,
  assurance class,
  ResidualTrustClosureId,
  public family-retained facts)
~~~

The semantic answer projection excludes the
`CompletedRequestRealizationLedger`, operational request/reservation/counter
fields, named operational occurrence, and live capability. `NegativeAnswerId`
is likewise the identity of the negative answer's semantic projection, as
specified in Section 8.2. Policy, source-policy closure, assurance, trust,
bases, derivation, and public semantic retained facts enter
`JudgmentRecordId` only through the explicit fields above.

For the confidential lane, each structurally corresponding value instead
receives `LocalAnalysisHandle<T>` under the collision-free, owner-internal rule
of Section 3.1. Its complete preimage remains available only to the exact owner
instance for type and equality checking. It is never hashed or serialized into
a public `SemanticBasisId`, `SupportInstantiationId`, `ValidationBasisId`,
`BasisQualificationId`, `DerivationId`, or `JudgmentRecordId`.

`BasisQualificationId` identifies the exact accepted pairing of semantic and
validation basis, assurance class, and residual trust. Downstream shorthand
`BasisId` means this qualification, never an erased proof-system label.

One checking or replay occurrence is excluded from semantic identity. Its live
derivation binding retains the exact checker-execution and support-capability
matches only for that authority lifetime. Private retained facts use a family-
owned opaque occurrence binding rather than a public content digest.

### 7.3 External proof boundary

An external proof contributes only after three separate checks:

~~~text
CheckedExternalStatementProof(exact statement, environment, proof, validation)

CheckedSubjectModelCorrespondence(
  exact zkc subjects and views,
  exact external symbols and semantic objects,
  exact occurrence and parameter substitutions,
  explicit correspondence hypotheses)

CheckedDirectionalStatementAdequacy(
  external statement,
  exact zkc AnalysisProposition,
  exact sufficient implication direction,
  maps, losses, and residual hypotheses)
~~~

The latter two are truth-apt Analysis propositions, not Boolean validation
metadata. If either is assumed, that exact proposition remains in the final
hypothesis context. Literal equality is unnecessary when a checked one-way
implication suffices, but direction is mandatory, particularly for negative
results. Kernel acceptance of an external theorem alone establishes only the
external statement.

Directional statement adequacy has the ordinary Analysis category split:

~~~text
CorrespondenceQuestionId = H(
  "zkc/analysis-question",
  AnalysisSemanticRegimeId,
  CorrespondenceFamilySemanticProfileId,
  exact external statement and environment identity,
  exact target AnalysisGoalId,
  exact subject, model, occurrence, and parameter maps)

CorrespondenceGoalId = H(
  "zkc/analysis-goal",
  CorrespondenceQuestionId,
  exact implication direction and quantitative loss)

CorrespondencePropositionId = H(
  "zkc/analysis-proposition",
  CorrespondenceGoalId,
  canonical correspondence hypothesis context)
~~~

The hypothesis-free target goal breaks a potential identity cycle. The
correspondence proposition remains conditional and separately checkable; its
proof and checker stay in derivation and validation identities.

### 7.4 Supported checking lanes

A family explicitly admits any subset of these lanes:

1. A complete finite direct procedure that can establish the exact family
   affirmative or family-negative proposition inside its declared domain.
2. An internal finite acyclic `DerivationPlan<F>` whose nodes bind exact
   premises, substitutions, models, side conditions, and quantitative
   transformers. The checker performs no proof search.
3. An external proof basis with checked statement, subject/model
   correspondence, and directional adequacy.
4. A certificate or solver basis with exact query, polarity, encoding, theory,
   certificate language, semantic mapping rule, and validation roots.
5. An Evidence-derived basis only through a family rule over exact attributable
   Evidence records or policy-qualified appraisals that states why their
   retained producer observation meaning, sampling plan, environment, and
   uncertainty establish the proposition.

Outside a direct procedure's complete domain, the result is `Unsupported` or
`CannotAnswer`, never negative. Solver `sat`, `unsat`, `unknown`, invalid
certificate, unsupported proof rule, and checker failure are interpreted first
inside the exact encoded query. Only an explicit family rule maps a checked
query result to an Analysis outcome. A solver-trusted lane remains a different
assurance qualification from an independently checked certificate.

## 8. Qualified outcomes and negative meaning

### 8.1 Outcome algebra

~~~text
FamilyCompletedOutcome<F> =
    F::Affirmative(
      exact proposition,
      checked derivation,
      basis qualification,
      assurance class,
      residual trust closure,
      family operation policy ID,
      source operation-policy dependency closure,
      exact CompletedRequestRealizationLedger<F>,
      exact named consumer and operation_purpose: OperationPurpose,
      exact derivation, support, semantic-basis, and validation-basis
        coordinates,
      family-retained facts)
  | F::Negative(NegativeAnswer<F>)

NegativeAnswer<F> = {
  answered_proposition_id,
  established_counter_proposition_id,
  exact_family_refutation_or_decision_relation_id,
  exact_refutation_scope,
  checked_refutation_or_complete_decision_result,
  basis_qualification,
  assurance_class,
  residual_trust_closure,
  family_operation_policy_id,
  source_operation_policy_dependency_closure,
  exact CompletedRequestRealizationLedger<F>,
  exact named consumer and operation_purpose: OperationPurpose,
  exact derivation, support, semantic-basis, and validation-basis coordinates,
  family_retained_refutation_facts
}

AnalysisAttemptDisposition<F> =
    Unsupported(exact unsupported family, model, regime, or construct)
  | CannotAnswer(exact missing semantic input, correspondence, or basis)
  | Refused(exact missing authority or prohibited invocation)
  | Malformed(exact framing, typing, identity, cycle, or structural defect)
  | CheckerFailure(exact normalized operational-failure class)

AnalysisAttemptRecord<F> = {
  exact AnalysisCheckingAttemptInput<F>, including either its unavailable
    request status or its parsed request, derived schema, and every
    capability-neutral subject, view, basis, support, validation,
    checker-contract, and source-binding slot actually offered or missing,
  exact request and capability-neutral invocation projection when preparation
    reached Ready, or exact rejected slot and normalization state otherwise,
  exact missing, mismatched, stale, prohibited, malformed, or failed
    requirement,
  exact reached FamilyOperationPolicyId, authenticated immediate/transitive
    source-policy dispositions, NamedConsumer, and OperationPurpose, or the
    exact slot status showing why any such coordinate was unavailable,
  exact AnalysisAttemptDisposition<F> and
    Reached(exact residual trust)
      | Unavailable(exact governing unavailable request-root or
          validation/trust slot status and exact dependency path),
  no ExactCheckedResultAuthorityBinding and no live capability
}

AnalysisAttemptRecordId<F> = H(
  "zkc/analysis-attempt-record",
  exact AnalysisCheckingAttemptInput<F>.AnalysisSemanticRegimeId,
  exact expected family F,
  CanonicalEncode(AnalysisAttemptRecord<F>))

AnalysisAttemptRecordRef<F> =
    Portable(exact AnalysisAttemptRecord<F>,
             exact AnalysisAttemptRecordId<F>)
  | OwnerLocal(exact AnalysisAttemptRecord<F>,
               exact LocalAttemptRecordHandle)

AnalysisAttemptOutcome<F> =
    Completed(
      exact FamilyCompletedOutcome<F>,
      exact ExactCheckedResultAuthorityBinding<Analysis, F>,
      fresh EstablishedAnalysisJudgment<
        F, exact completed-outcome polarity, exact AssuranceClass,
        exact FamilyOperationPolicyId,
        exact ExactSourceOperationPolicyDependencyClosure,
        exact NamedConsumer, exact OperationPurpose,
        exact ExactJudgmentBinding,
        exact ExactCheckedResultAuthorityBinding<Analysis, F>> bound to both
        preceding values)
  | Unsupported(exact AnalysisAttemptRecordRef<F> whose disposition is
                Unsupported)
  | CannotAnswer(exact AnalysisAttemptRecordRef<F> whose disposition is
                 CannotAnswer)
  | Refused(exact AnalysisAttemptRecordRef<F> whose disposition is Refused)
  | Malformed(exact AnalysisAttemptRecordRef<F> whose disposition is Malformed)
  | CheckerFailure(exact AnalysisAttemptRecordRef<F> whose disposition is
                   CheckerFailure)
~~~

The record body is constructed before its reference. `Portable` is legal only
when the entire record preimage is portable and every applicable source and
Analysis operation policy permits this disclosure; otherwise Analysis
allocates a fresh collision-free `LocalAttemptRecordHandle` after constructing
the body. Neither branch contains a capability. Checking or retaining the
record can authenticate only its canonical record-relative request,
association, offered-input, and disposition statement. It cannot establish an
affirmative or negative proposition or authenticate that an attempt, failure,
or historical occurrence happened. An actual occurrence claim requires a
separate owner-authenticated occurrence/log result, which Stage 4A does not
define. Reuse or replay of the record does not require the operational failure
to recur and cannot satisfy any semantic premise.

The displayed `*_id` fields and `NegativeAnswerId` describe the portable form of
each coordinate. A mixed or local outcome substitutes a corresponding
`Local*Handle` only for a coordinate whose own identity preimage is tainted;
other proposition, basis-qualification, semantic-basis, or validation-basis IDs
remain portable. An attempt uses a portable request/record ID or local
request/attempt handle when preparation reaches those coordinates. Before that
point a `RequestUnavailable` branch retains only its exact missing or opaque-
malformed request-root status; a `RequestParsed` branch retains the exact
capability-neutral request and every derived slot status. Any
`OpaqueMalformed` slot forces the attempt record into the owner-local lane.
Every affected coordinate inherits the exact same-process named-consumer and
transitive source-policy restrictions.

A family without an exact refutation schema or complete decision procedure
omits `F::Negative`. It does not inherit a generic Boolean false case. Every
attempt record binds its exact outer attempt-input carrier. When request or
policy preparation succeeds it additionally binds the exact portable
`AnalysisRequestId` or local `LocalAnalysisRequestHandle` and
`FamilyOperationPolicyId`; otherwise it binds the exact missing, candidate, or
malformed slot status instead of inventing either coordinate. Only a completed
outcome under an exact authenticated request and policy and
the freshly checked conjunction of every transitive source-owner operation
policy mints the family-, polarity-, assurance-, policy-, source-policy-
closure-, named-consumer-, operation-purpose-, and exact-record-binding-bound
live capability returned by that same `Completed` branch; changing policy does
not change proposition meaning. U/C/R/M/F return neither a checked-result
binding nor an `EstablishedAnalysisJudgment` capability.

The family first seals the exact `CompletedRequestRealizationLedger<F>` from the
invocation's exact pre-execution ledger and completion-time proposition,
admission binding, target-realization proof, achieved assurance, and terminal
accounting. It retains that completed ledger in either polarity of
`FamilyCompletedOutcome<F>`. The operational request, reservation, and counters
do not enter semantic `JudgmentRecordId`; that ID uses only the explicit
semantic projection in Section 7.2. They do remain exact completed-result
origin facts, so two operational completions may share a semantic judgment
coordinate while retaining different complete checked-result bindings.

The completed outcome body is constructed without a future `JudgmentRecordId`
or `LocalJudgmentRecordHandle`. Its explicit semantic projection and derivation
coordinates determine the judgment record or local handle. Only then may the
owner construct the exact `ExactCheckedResultAuthorityBinding<Analysis,F>`.
Its result coordinate is that judgment record or local handle, and its origin
closure embeds the complete `ExactJudgmentBinding`, completed outcome and
completed request-realization ledger, assurance/trust, family policy,
transitive source-policy closure, named consumer, typed purpose, and inert
`OwnerCapabilityRequirement`. The owner then atomically returns that complete
binding and a separately fresh live capability carrying both the complete
judgment binding and exact source binding in the same `Completed` outcome. No
inert outcome or negative-answer preimage contains its own future record
identity or live capability.

### 8.2 Negative-result discipline

`NegativeAnswerId` binds the semantic projection consisting of the proposition
actually answered, the exact counter-proposition established, the family-owned
refutation or complete-decision relation between them, its exact scope, the
checked semantic refutation result, and public family-retained refutation
facts. It excludes the completed request-realization ledger, operational
request/reservation/counters, named operational occurrence, and every live
capability. A family may define a canonical total `Negate_F(P)` and use that
exact proposition. A narrower counter-proposition cannot refute a broader
request without a checked family implication.

A counterexample normally remains the refutation witness rather than entering
either proposition identity. The result and capability retain its exact
observer, model, occurrence, parameter, and hypothesis scope. It cannot be
widened to another experiment.

An invalid certificate is negative only for a separate `CertificateValid`
question. Timeout, interrupted search, resource exhaustion, failed derivation
search, or solver `unknown` is never semantic negative without an exact
completeness theorem for that procedure and limit.

## 9. Lifecycle, consumers, and nonclaims

Question and proposition values follow:

~~~text
canonical candidate
  -> identity, dependency, type, map, model, and read-closure authentication
  -> family-owned well-formedness admission
  -> opaque process-local admitted capability
~~~

Checking consumes admitted values, the exact admitted family operation policy,
fresh support authority satisfying every premise and correspondence
requirement, exact authenticated source-owner policy records with fresh admitted
policy or owner-mediated purpose-check authority matching the complete source-
policy closure, and the fresh identity/ABI/contract-matched checker-execution
capability required by the exact validation basis. It first validates the exact
pre-execution request realization and, only after execution and any
`DeriveWithin` proposition admission, seals the exact completed realization.
It returns one policy-bound qualified record and may mint one exact result
capability only when every transitive source-owner policy permits that consumer
and purpose. The completed outcome, binding, and capability retain the exact
completed request-realization ledger, source-policy dependency closure and
completed judgment binding, the complete
`ExactCheckedResultAuthorityBinding<Analysis,F>`, and its inert
`OwnerCapabilityRequirement`. Serialization, FFI,
mutation, reset, or process crossing destroys every capability. A later
consumer reconstructs, reauthenticates, re-admits, and rechecks under the exact
recorded policy with newly minted support and checker-execution capabilities.

Compiler may consume exact Analysis capabilities in typed constraints and
objectives. It cannot reinterpret their propositions, erase their hypotheses,
change polarity, widen subject scope, relabel assurance, or erase or exceed the
exact family operation policy or any policy in the transitive source-policy
dependency closure. It preserves and checks the exact completed
`ExactJudgmentBinding`, including its record or local reference and exact
derivation, support, semantic-basis, and validation-basis coordinates. Evidence
may record check receipts and implementations, but such records do not
establish the proposition. A relying consumer separately decides whether the
exact hypotheses, bound, assurance class, immediate and transitive source
operation policies, completed judgment binding, and residual roots are
acceptable.

This specification does not establish:

- any cryptographic, semantic, cost, or correspondence proposition;
- correctness or completeness of a rule, theorem, checker, model, encoding,
  formalization, solver, or Evidence-derived inference;
- a proposition from a question, goal, request, proof search, theorem name,
  or persisted record alone;
- a negative where the family lacks an exact refutation or complete decision
  boundary;
- persistence of live authority;
- relation satisfaction, target admission, Compiler selection, endpoint
  feasibility, or global verification; or
- implementation support, migration feasibility, release readiness, or
  consumer reliance.
