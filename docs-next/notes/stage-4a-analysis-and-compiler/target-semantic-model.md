# Federated Analysis and validated-decision Compiler target model

> **Document kind:** Temporary integrated target design
> **Document state:** Stage 4A provisional target; scenario, matrix, and
> independent convergence review pending
> **Authority:** None. This page does not define a current normative judgment,
> establish a property or compilation result, admit a Protocol, mint live
> authority, report implementation support, authorize migration, or activate
> Stage 4B.
> **Candidate basis:** Candidate B with bounded mechanisms retained from
> Candidates A, C, D, and E
> **Scope:** Complete ideal Stage 4A Analysis and Protocol-Compiler semantics;
> implementation organization and migration are deliberately excluded
> **Disposition:** Promote only after validation into durable `analysis/`,
> `compiler/`, `relations/`, and `project/` owners; retain decisions and
> reversal triggers in convergence; delete this page with the temporary
> package.

## 1. Architectural thesis

The provisional target is a **federated typed Analysis calculus followed by a
validated-decision Compiler**:

```text
exact admitted Stage 3 subjects and owner-created views
  + family-owned semantic question and model
  + exact typed hypothesis context
  + direct, internal, external, or certificate basis
  -> family-owned checked claim
  -> qualified Analysis result

admitted predecessor
  + exact compilation problem
  -> replaceable unauthoritative search
  -> frozen unauthoritative proposal scope
  -> PIR-owned target authentication and admission
  -> exact separately owned transition judgments
  -> semantic candidate domain
  -> exact Analysis constraints and typed objectives
  -> complete assessment ledger
  -> qualified deterministic Compiler decision
```

The common Analysis layer owns lifecycle, identity categories, dependency
closure, checking discipline, qualified outcomes, capabilities, replay, and
shared typed-expression primitives. It does not own a universal proposition or
result payload. Each family owns its subject tuple, semantic model, claim,
result, negative meaning, valid bases, and inference rules.

Compiler owns problem framing, proposal orchestration, semantic-candidate
domain claims, assessments, comparison, and decisions. It owns neither target
admission, predecessor/successor semantic relations, Analysis property meaning,
Evidence observations, nor Stage 4B endpoint facts.

The model absorbs four bounded mechanisms from the controls:

- the current kernel's closed rule bodies, explicit derivations, exact
  arithmetic, and no-search checking discipline;
- proof-DAG identity and dependency visibility without a universal Claim IR;
- external proof systems through checked basis adapters rather than semantic
  delegation; and
- optional proof-carrying transforms and symbolic-domain certificates without
  requiring certificates for every direct check.

## 2. Semantic categories and authority

### 2.1 Category separation

The target distinguishes:

```text
semantic subject
AnalysisQuestion                 // stable experiment or relation problem
AnalysisProposition              // exact conditional truth-apt claim
AnalysisRequest                  // one operational attempt or synthesis request
semantic derivation basis
validation/checker basis
derivation or refutation
qualified result record
checking occurrence
process-local live capability
replay bundle
operational search record
Compiler decision
```

No category is an alias for another. In particular:

- a theorem statement is not a zkc claim;
- an Analysis question is not yet a proposition with a truth value;
- an operational request, basis preference, timeout, or requested assurance
  does not change question or proposition meaning;
- a proof is not a claim or a capability;
- a semantic derivation basis is not the checker implementation that validates
  it;
- a result record is not the checked occurrence that created it;
- a candidate target is not its proposal recipe;
- a candidate domain is not a producer's search state; and
- a decision is not target admission, a transition theorem, or a property
  theorem.

### 2.2 Live authority

Every authority-bearing input is a fresh process-local capability produced by
its semantic owner. Analysis receives admitted subjects and owner-created
views. Compiler receives admitted predecessor and target capabilities plus
exact completed transition and Analysis capabilities.

Only a successful current check may mint:

```text
EstablishedAnalysisJudgment<F, Affirmative, AssuranceClass>
EstablishedAnalysisJudgment<F, Negative, AssuranceClass>
CheckedCandidateDomainCapability
EligibleAssessmentCapability
QualifiedCompilerDecisionCapability
```

There is no erased `EstablishedAnalysisJudgment<F>` super-capability through
which an independently checked result, trusted solver assertion, or
Evidence-derived inference can be substituted for another assurance class.
An attenuated consumer view preserves exact proposition, polarity,
hypotheses, assurance, and residual-trust closure.

An ID, value-shaped aggregate, theorem name, proof file, solver response,
signature, cache entry, prior result record, or serialized replay bundle never
mints one of these capabilities.

`Unsupported`, `CannotAnswer`, `Refused`, `Malformed`, and `CheckerFailure`
produce exact attempt records but no semantic affirmative or negative
capability. A consumer may rely on the operational fact only through the exact
record-checking boundary appropriate to that consumer.

### 2.3 Canonical semantic identity

Every identity-bearing Stage 4A value uses the Stage 1--3 rule:

```text
Id(T) = H(domain_tag, semantic_regime, CanonicalEncode_regime(T))
```

The canonical preimage contains finite typed semantic data and exact typed
content references. It contains no live capability, host pointer, dynamic
callback, mutable registry, search state, prover session, checker process ID,
wall-clock timestamp, or incidental printer spelling.

Analysis uses domain-separated identities for each semantic category:

```text
AnalysisQuestionId = H(
  "zkc/analysis-question",
  AnalysisSemanticRegimeId,
  FamilySemanticProfileId,
  exact semantic subject closure,
  exact occurrence graph and semantic maps,
  ModelInstantiationId,
  experiment, observer, direction,
  alpha-normalized typed parameters and quantifiers,
  SemanticReadClosureId)

AnalysisGoalId = H(
  "zkc/analysis-goal",
  AnalysisQuestionId,
  family-specific exact conclusion)

AnalysisPropositionId = H(
  "zkc/analysis-proposition",
  AnalysisGoalId,
  HypothesisContextId)

AnalysisRequestId = H(
  "zkc/analysis-request",
  AnalysisQuestionId,
  exact target proposition or derive-within result schema,
  offered basis identities,
  requested assurance profile,
  operational-limits profile,
  named persistence purpose when present)
```

`AnalysisRequestId` is an operational/replay identity, not semantic claim
identity. Two requests may ask for the same proposition through different
tools or limits. A successful derive-within request computes and authenticates
one exact proposition; an unsuccessful request establishes none.

## 3. Analysis family profiles

### 3.1 Closed family profile

Each supported family separates proposition meaning from the machinery that
may establish, validate, carry, or replay it:

```text
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
  exact semantic-basis extension boundary
}

FamilyValidationProfile<F> {
  validation_and_checker_contracts,
  decoder_translation_and_proof_rule_contracts,
  validation trust-root policy
}

FamilyOperationPolicy<F> {
  capability_contract,
  replay_contract,
  disclosure_and_trust_contract,
  operation and unknown-question policy
}
```

Only `FamilySemanticProfileId` enters `AnalysisQuestionId`. It identifies the
exact subject, model, experiment, observer, parameter, conclusion, refutation,
quantitative, and semantic-read meaning of the family. A basis registry,
theorem or rule catalog, checker contract or implementation, assurance lane,
capability policy, replay consumer, disclosure rule, or trust policy cannot
change that question or proposition identity.

`semantic_view_contract_schemas` identifies the source-fact meanings and read
contracts that may affect a question. It is not a catalog of concrete view
adapters. Adding another independently admitted adapter that reconstructs an
unchanged exact contract changes only its input, basis, validation, or
operation identity; it does not change an existing question.

`FamilyBasisRegistryId`, `FamilyValidationProfileId`, and
`FamilyOperationPolicyId` enter only the exact semantic basis, validation
basis, qualification/record, operation, or replay identity that reads them.
Live checker implementations are authenticated against the exact validation
contracts supplied to an invocation.

The v0 family set is closed and versioned. An unknown family or model tag is
`Unsupported`; it cannot load a host callback or acquire meaning from a plugin
registry. A new family requires an explicit profile and review of every field
above.

### 3.2 Thin common envelope

The common envelope requires every family to supply:

```text
subjects
owner-created views and complete semantic/basis read closures
semantic model instantiation
observer, direction, and occurrence coordinates when meaningful
typed parameters
question result schema and proposition-specific hypothesis/conclusion schemas
```

It does not supply optional universal fields. If a family has no adversary,
oracle, simulator, cost model, or witness subject, the field is structurally
absent rather than `None`, empty, or defaulted.

### 3.3 Source-owned views and two read closures

Each upstream owner defines the view types Analysis may receive, the finite
fact vocabulary they expose, and the adequacy predicate for each permitted
read contract. Analysis distinguishes:

```text
SemanticReadClosure<F> {
  every source fact and direct semantic dependency used to define the
    question's meaning
}

BasisReadClosure<B> {
  every source fact and dependency used only to validate one theorem
    instantiation, proof, certificate, direct procedure, or correspondence
}
```

`SemanticReadClosureId` enters `AnalysisQuestionId`.
`BasisReadClosureId` enters the semantic or validation basis identity that
reads it, not proposition identity. Different adequate view occurrences may
reconstruct the same closure. View tokens and live capabilities never enter a
content identity.

Admission of a family semantic profile checks that its semantic closure is permitted by
every source-owned view schema. Each offered basis separately declares and
checks its complete basis closure. A field cannot migrate between the two
closures merely to preserve an old identity: if it affects proposition
meaning, it is semantic; if it only validates one support path, it is basis-
local.

During checking:

- a missing named view or field is `CannotAnswer` before semantic evaluation;
- a view-shaped value without matching source authority is `Refused`;
- an ill-typed or extra read request is `Malformed` or `Unsupported` according
  to the exact profile rule; and
- no checker may reopen carrier bytes, query an ambient registry, or infer an
  omitted field.

Adding a semantic read changes the family profile, model instantiation, or
question and therefore `AnalysisQuestionId`. Adding a proof-only read changes
the corresponding basis identity. Neither can be hidden in checker behavior.

## 4. Question, proposition, request, basis, derivation, and result

### 4.1 Analysis question

```text
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
```

`AnalysisQuestionId` identifies one stable relation or property experiment and
its permitted conclusion shape. It contains no residual hypothesis context,
particular bound or conclusion, proof search policy, theorem choice, proof
bytes, checker version, timeout, worker limit, or accepted trust policy.

An analysis producer may propose a conclusion or derivation for a question. A
direct checker may compute one. Neither proposal has authority before checking.

### 4.2 Exact conditional proposition

```text
AnalysisGoal<F> {
  question_id,
  exact_typed_conclusion
}

AnalysisProposition<F> {
  goal_id,
  hypotheses: CanonicalTypedHypothesisContext
}
```

`AnalysisPropositionId` is the truth-apt semantic claim. For a quantitative
family, a different bound, metric, extractor guarantee, simulator regime, cost
value, or residual hypothesis is a different proposition. Conditional meaning
is explicit:

```text
Gamma |-_model Conclusion<F>(subjects, parameters, result)
```

`AnalysisGoalId = H(AnalysisQuestionId, exact_typed_conclusion)` is the
hypothesis-free conclusion subidentity. It permits a correspondence or theorem
assumption to name the exact goal without recursively depending on the
proposition whose hypothesis context may contain that assumption. It is not a
truth-apt proposition or a live capability.

Rules may discharge, inherit, strengthen, or introduce a hypothesis only
through a typed operation declared by the family. The final effective context
contains every residual assumption.

The word *claim* elsewhere in this page is a prose abbreviation for an exact
`AnalysisProposition` or another owner's exact proposition. It does not name a
fourth Analysis semantic category or a separate `AnalysisClaimId`.

Several derivations with different proof bytes, tools, or trust roots may
establish the same proposition. Derivations that produce different bounds or
residual hypotheses answer the same `AnalysisQuestionId` but establish
different `AnalysisPropositionId`s.

### 4.3 Operational Analysis request

```text
AnalysisRequest<F> {
  admitted_question,
  target:
      ExactProposition(AdmittedAnalysisProposition<F>)
    | DeriveWithin(F::ExactResultSchema),
  exact owner-created semantic and offered-basis views,
  offered semantic and validation bases,
  requested assurance profile,
  operational resource limits,
  optional named persistence purpose
}
```

The request is one unauthoritative attempt specification. A timeout, tactic,
solver, proof assistant, worker limit, or basis preference changes
`AnalysisRequestId`, never question or proposition meaning. `DeriveWithin`
may return one or more newly authenticated exact propositions; failure to find
one is `CannotAnswer`, not a negative property result.

Question and proposition values pass their own lifecycle:

```text
canonical question/proposition candidate
  -> exact identity, dependency, type, map, model, and closure authentication
  -> family-owned well-formedness admission
  -> process-local AdmittedAnalysisQuestion<F>
     or AdmittedAnalysisProposition<F>
```

Admission retains the exact live upstream subject authority and adequate
views. A matching `AnalysisQuestionId` or `AnalysisPropositionId` is never an
admitted capability.

### 4.4 Hypothesis graph

`AnalysisHypothesisContext` is a finite acyclic typed graph whose leaves may
be:

- declared cryptographic or hardness assumptions;
- exact unproved proposition assumptions admitted by the family;
- termination, losslessness, state-separation, and oracle restrictions;
- adversary, query, time, uniformity, and auxiliary-input restrictions;
- quantitative side conditions; or
- explicitly assumed model- or statement-correspondence propositions.

ROM, QROM, ideal-permutation, CRS/SRS, concrete-hash, trace, cost, abort, and
termination interpretations that change the experiment's meaning are model
coordinates in `AnalysisQuestion`, not labels that can be added or removed as
metadata. A theorem may still carry hypotheses internal to that exact model.

Previously established Analysis judgments and owner-provided structural
capabilities are exact derivation dependencies, not unresolved hypotheses.
Their own residual hypothesis contexts are inherited into the derived
proposition through the applied rule.

Every edge names its substitution, direction, and discharge rule. Strings,
citations, and theorem names cannot stand in for hypotheses. A checked
conditional theorem establishes the exact conditional claim, not the truth of
its leaves.

Contexts use alpha-normalized typed binders and a canonical acyclic DAG.
Logical equivalence is not guessed: two differently expressed contexts have
different identities unless an explicit checked rule relates them. A root
cannot be established solely by assuming that same root, and proposition and
derivation dependencies are cycle-free.

### 4.5 Semantic basis, validation basis, and derivation identities

```text
SemanticDerivationBasis {
  basis_lane,
  used_family_semantic_profile_slice,
  exact family_basis_registry_slice,
  exact_rule_or_theorem_refs,
  exact_model_subject_and_statement_correspondence_propositions,
  exact_encodings_and_query_polarities,
  total_dependency_disposition_ledger,
  basis_read_closure,
  exact premise proposition, polarity, and semantic-fact requirements,
  substitutions and quantitative transformer contracts
}

DependencyDisposition =
    EstablishedPremise(exact proposition, polarity, and semantic facts)
  | ResidualHypothesis(exact proposition)
  | DefinitionalOrLogicTrustRoot(exact definition or logic root claim)

SupportInstantiation {
  semantic_basis_id,
  exact premise JudgmentRecordIds and live capability requirements,
  exact correspondence-support records,
  exact dependency-disposition realization
}

ValidationBasis {
  semantic_basis_id,
  exact validation/checker semantic contracts,
  checker implementation and contract-correspondence identities,
  decoder, elaborator, translation, and proof-rule closure,
  validation-only dependency and read closure,
  exact trust-root DAG
}

AnalysisBasisQualification {
  semantic_basis_id,
  validation_basis_id,
  assurance_class,
  residual_trust_closure_id
}

CheckedDerivation {
  exact_proposition_id,
  semantic_basis_id,
  validation_basis_id,
  support_instantiation_id,
  derivation_body_or_direct_check_transcript,
  premise_occurrences,
  substitutions,
  side_condition_results,
  quantitative_transform_ledger
}
```

The identities are separate:

```text
QuestionId       // requested semantic problem
GoalId           // exact hypothesis-free conclusion; no truth authority
PropositionId    // exact conditional truth-apt claim
RequestId        // one operational attempt specification
SemanticBasisId  // inference, theorem, encoding, and correspondence meaning
ValidationBasisId // checker semantics, implementation closure, and trust roots
BasisQualificationId
                  // accepted pairing and assurance class; "BasisId" in
                  // downstream shorthand refers to this identity
DerivationId     // one proof, refutation, certificate, or direct transcript
JudgmentRecordId // completed outcome and exact checked support
AnalysisReplayBundleId
                  // exact inert replay material plus consumer and purpose
ReplayOccurrenceHandle
                  // process-local nonserializable owner-issued occurrence
AuditEventRecordId // optional inert operational event record; no authority
```

The exact basis and result identities follow:

```text
SemanticBasisId = H(
  "zkc/analysis-semantic-basis",
  exact family slice, rules/theorems, correspondences, encodings,
  semantic-basis dependency closure, BasisReadClosureId,
  exact premise PropositionIds, required polarities and semantic facts,
  DependencyDispositionLedgerId, substitutions, transformers)

ValidationBasisId = H(
  "zkc/analysis-validation-basis",
  SemanticBasisId,
  exact checker contracts and implementations,
  elaborator/decoder/translation/proof-rule closure,
  validation-only read closure,
  ResidualTrustClosureId)

JudgmentRecordId = H(
  "zkc/analysis-judgment",
  answered AnalysisPropositionId,
  exact affirmative answer or NegativeAnswerId,
  DerivationId,
  SupportInstantiationId,
  SemanticBasisId,
  ValidationBasisId,
  assurance class,
  ResidualTrustClosureId,
  public family-retained facts)
```

One checking or replay occurrence is deliberately excluded. Private or
sensitive retained facts use a family-owned opaque occurrence binding rather
than a public content digest.

Several semantic or validation bases and derivations may establish one
proposition. Basis, checker, or proof changes do not alter proposition meaning.
A consumer that constrains acceptable assurance or trust cites the exact basis
qualification in addition to the proposition capability.

Semantic correspondence cannot hide inside validation metadata. A conditional
correspondence is itself an exact proposition whose hypothesis context,
direction, maps, and loss enter `SemanticBasisId`; its checked proof enters the
derivation dependency closure. Changing only the implementation used to check
that correspondence changes `ValidationBasisId`, not the correspondence
proposition.

The dependency-disposition ledger is total over every imported definition,
axiom, lemma assumption, theorem assumption, and proof-environment dependency.
Every truth-apt unproved proposition becomes `ResidualHypothesis` and is
canonically unioned into the resulting `AnalysisPropositionId`. An exact prior
judgment may realize `EstablishedPremise`; its proposition/polarity/facts enter
semantic basis meaning while the selected `JudgmentRecordId`, assurance, and
trust enter `SupportInstantiationId` and the checked derivation. Only logic or
definitional adequacy—not a domain proposition asserted for convenience—may
terminate at `DefinitionalOrLogicTrustRoot`. There is no generic axiom/import
closure that can hide in residual trust.

## 5. Analysis checking lanes

### 5.1 Complete direct procedure

A family may admit a finite complete direct checker. It receives the exact
question or target proposition and source-owned views, computes the exact
family conclusion, and returns either an affirmative proposition or the
family's exact negative proposition and refutation facts. Its semantic basis
declares the exact completeness domain; its validation basis identifies the
exact direct-checker contract and implementation closure.

Outside that domain the result is `Unsupported` or `CannotAnswer`, never a
negative. Equal semantic IDs may supply a trivial direct affirmative only for
the exact equality claim whose profile states that implication.

### 5.2 Internal typed derivation

An internal `DerivationPlan<F>` is a finite acyclic graph of exact rule
instances. Every node identifies its premise occurrences, substitution, model,
side conditions, and quantitative transformer. The checker owns no proof
search. Search failure therefore cannot be interpreted by the checker as a
semantic negative.

The current Soundness Kernel's closed rules, exact plan checking, explicit
assumptions, exact arithmetic, and refusal discipline become one internal
semantic-basis profile with a separately identified validation basis rather
than the universal Analysis payload.

### 5.3 External proof basis

An external proof contributes only after three semantically separate results:

```text
CheckedExternalStatementProof(
  exact elaborated external statement,
  exact logic/import/axiom environment,
  exact proof term or artifact,
  exact validation basis)

CheckedSubjectModelCorrespondence(
  exact zkc subjects and views,
  exact external symbols and semantic objects,
  exact occurrence and parameter substitutions,
  explicit correspondence hypotheses)

CheckedDirectionalStatementAdequacy(
  external statement,
  zkc AnalysisProposition,
  exact sufficient implication direction,
  exact maps, losses, and residual hypotheses)
```

The latter two are truth-apt Analysis propositions, not unchecked Boolean
fields. In particular, directional adequacy has canonical identity:

```text
CorrespondenceQuestionId = H(
  "zkc/analysis-question",
  AnalysisSemanticRegimeId,
  CorrespondenceFamilySemanticProfileId,
  exact external statement and environment identity,
  exact target AnalysisGoalId,
  exact subject/model/occurrence/parameter maps)

CorrespondenceGoalId = H(
  "zkc/analysis-goal",
  CorrespondenceQuestionId,
  exact implication direction and quantitative loss)

CorrespondencePropositionId = H(
  "zkc/analysis-proposition",
  CorrespondenceGoalId,
  canonical correspondence hypothesis context)
```

If correspondence is assumed rather than established, this exact proposition
appears in the final residual hypothesis context. If it is established, its
judgment capability is an exact semantic-basis dependency. Proof checking is
recorded separately in `ValidationBasisId`.

Literal equality is not required when a checked sound abstraction or one-way
implication suffices. Direction is mandatory, especially for negative results.
Kernel proof checking without the latter two checks is only a fact about the
external proposition.

### 5.4 Certificate or solver basis

A certificate lane binds:

- exact query and polarity;
- encoding and theory;
- source proposition;
- certificate format and rule set;
- semantic certificate rule and query-to-proposition correspondence;
- proof checker contract and dependency closure; and
- exact validation trust roots for solver-independent checking or the trusted
  solver assertion.

`sat`, `unsat`, `unknown`, invalid certificate, unsupported proof rule, and
checker failure are interpreted first inside that exact query. Only an explicit
family rule maps a checked result to an Analysis outcome.

A solver without a checked certificate may support a separately qualified
solver-trusted basis if the family profile permits it. It cannot silently mint
the same trust qualification as an independently checked certificate.

### 5.5 Evidence-derived basis

Tests, benchmarks, traces, and measurements are Evidence observations. They
establish an Analysis proposition only through a family rule that states why the
exact observation, sampling plan, environment, and uncertainty suffice. A
measurement-derived cost estimate remains distinguishable from an exact cost
theorem.

## 6. Qualified Analysis outcomes

### 6.1 Outcome algebra

The common lifecycle does not impose a universal Boolean result. Each family
defines its own completed payload and, if soundly available, its own semantic
negative:

```text
FamilyCompletedOutcome<F> =
    F::Affirmative(
      exact proposition,
      checked derivation,
      basis qualification,
      assurance class,
      residual trust closure,
      family-retained facts)
  | F::Negative(NegativeAnswer<F>)

NegativeAnswer<F> = {
      answered_proposition_id,
      established_counter_proposition_id,
      exact_family_refutation_or_decision_relation_id,
      exact_refutation_scope,
      checked refutation or complete-decision result,
      basis qualification,
      assurance class,
      residual trust closure,
      family-retained refutation facts
    }

AnalysisAttemptOutcome<F> =
    Completed(FamilyCompletedOutcome<F>)
  | Unsupported(exact unsupported family, model, regime, or construct)
  | CannotAnswer(exact missing semantic input, correspondence,
                 or completed basis)
  | Refused(exact missing authority or prohibited invocation)
  | Malformed(exact framing, typing, identity, cycle, or structural defect)
  | CheckerFailure(exact failed operational boundary;
                   no semantic conclusion)
```

A family with no exact refutation schema or complete decision procedure omits
`F::Negative`; it does not inherit a generic false case. Only a completed
family outcome mints the correspondingly typed
`EstablishedAnalysisJudgment<F, Polarity, AssuranceClass>` capability.

An invalid certificate is a negative result only for a separate
`CertificateValid` question. It is not a negative result for the claim the
certificate attempted to support. Timeout, interrupted search, resource
exhaustion, or solver `unknown` is never semantic `Negative` without a theorem
that makes the exact procedure complete under the exact limit.

### 6.2 Negative facts

Every family defines its own negative payload. Examples include:

- a kind- and map-indexed Core or Protocol disagreement;
- an exact observable trace counterexample;
- a refinement witness showing target behavior outside the source allowance;
- a distribution/metric counterexample under a complete finite procedure;
- an explicit cost-order reversal under one exact model; or
- a proof of the exact cryptographic property's formal negation.

Negative capabilities retain the counterfact and exact scope. They cannot be
widened to another observer, model, input distribution, property notion, or
parameter regime.

`NegativeAnswerId` binds the proposition actually answered, the exact
counter-proposition established, the family-owned refutation or complete-
decision relation between them, and its scope. A family may instead define a
canonical total `Negate_F(P)` and use that exact proposition as the
counter-proposition. A narrower counter-proposition cannot refute a broader
request without a checked family implication. The negative judgment record,
live capability, and replay material retain both proposition identities and
the relation; a counterexample normally remains its refutation witness rather
than entering either proposition identity.

## 7. Direct semantic relation families

### 7.1 Core and Protocol equality

`CoreEqUnderMap` compares exact admitted Core views under one separately
authenticated total kind-preserving map and one exact Core semantic regime. Its
proposition includes transcript order, claim flow, effects, checks, failures,
terminals, randomness topology, dependency correspondence, and every protected
observation read by the selected equality profile.

`ProtocolEqUnderMap` additionally includes challenge interpretation and, for FS,
transcript-construction meaning. Equal `CoreId` values cannot establish
`ProtocolEqUnderMap` between Fresh and FS Protocols. Equal Protocol IDs supply an
identity-map affirmative only under the exact matching regime; a broader
observer quotient is a different family profile.

An incomplete, ill-typed, non-total, or wrong-kind map is a malformed map
proposal and establishes no equality result. A total admitted map that fails
an exact preservation equation may establish a negative only for that exact
under-map proposition; it does not refute the existence of another valid map.
If existential isomorphism is required, it is a separate family whose complete
search or refutation boundary is explicit. `CoreEq` and `ProtocolEq` elsewhere
in this package are shorthand for these exact mapped relations.

### 7.2 Trace equality and directed refinement

```text
TraceEq<O>(source, target, O, TraceModel, exact maps)

TraceRefines<S,T,O>(source, target, O, TraceModel, direction, exact maps)
```

`TraceModel` fixes the event alphabet, projection, initial-state relation,
auxiliary input, terminal observations, failure/abort observations, divergence,
stuck behavior, and any fairness or receptiveness conditions. `TraceRefines` is
directed under the fixed convention:

```text
TraceRefines(source, target, O)
  means ObservedTraces(target, O) subseteq ObservedTraces(source, O)
```

The target therefore adds no observation outside the source allowance under
that exact model. Symmetry, the reverse convention, or conversion to equality
requires a named rule and both directions under exactly compatible models.

### 7.3 Declared change and `ChangeConforms`

`IntentionalChange` is an unauthoritative human- or policy-declared
`ChangeContract`, not a semantic result. Analysis checks the exact proposition:

```text
ChangeConforms(source, target, admitted ChangeContract,
               exact observer/model/maps)
```

The contract states:

- the exact protected observation relation that must still hold;
- a finite permitted-delta ledger;
- exact changed event, claim, failure, terminal, or challenge occurrences;
- required unchanged maps and dependencies; and
- every new property or consumer obligation created by the change.

An unlisted observable change is a negative `ChangeConforms` result when the
exact comparison procedure is complete. An affirmative result establishes only
conformance to the declared change envelope. It proves neither that a human
actually intended the change nor that the change is desirable, accepted by a
consumer, cryptographically property-preserving, or endpoint-feasible.

Compiler fields named `intentional_change` denote the declared contract and
exact affirmative `ChangeConforms` proposition/capability required by the
compilation problem; the declaration alone grants no eligibility.

### 7.4 Distributional relations

`DistributionEq` and `DistributionClose` use explicit subdistribution
semantics. Their questions include initial input distribution, shared versus
independent randomness, joint/correlation regime, conditioning, abort and
failure mass, termination/losslessness, measurable observation map, metric,
direction, and bound.

Perfect equality, statistical distance, and computational indistinguishability
are distinct families or regimes. Extensional equality does not establish
feasible computation or cost.

Exact finite rational profiles may expose complete direct affirmative and
negative procedures. Symbolic, measure-theoretic, or computational profiles
require their exact theorem/model basis; failed coupling or proof search is not
a distributional negative.

### 7.5 Cost relations

`CostValue` and `CostRelation` bind exact subject occurrences to one cost model:

```text
cost machine or static measure
input and environment regime
resource dimensions and aggregation
worst, average, amortized, or distributional interpretation
measurement method and uncertainty when Evidence-derived
```

Proof bytes, verifier work, prover work, memory, latency, query count, and
communication are different dimensions. Comparisons require an exact declared
order or conversion. A model-derived cost and a measured estimate do not share
one epistemic qualification merely because their numbers use the same unit.

## 8. Cryptographic property profiles

### 8.1 Shared experiment envelope

Cryptographic families reuse an exact experiment envelope containing only the
coordinates each family profile declares:

- Protocol and occurrence subjects;
- exact relation definition, instance, and satisfaction operands when read;
- setup, SRS, commitment, Interface, Plan, construction, or composition
  subjects when read;
- security parameter and instance-size regime;
- adversary, observer, extractor, and simulator interfaces;
- uniformity, auxiliary input, state, and initialization;
- oracle topology, access, programming, query, and move limits;
- classical, ROM, ideal-permutation, QROM, CRS/SRS, or other exact model;
- randomness ownership, independence, sharing, derivation, and substitution;
- abort, retry, failure, conditioning, termination, and expected runtime; and
- single, sequential, parallel, interleaved, concurrent, or multi-session
  schedule.

This is shared typed infrastructure, not one universal security proposition.

### 8.2 Family-specific content

| Family | Irreducible result and experiment content |
|---|---|
| Completeness | Honest prover/verifier, valid relation pair, honest randomness, accepted/output event, failure and termination |
| Plain soundness | False-language event, malicious prover class, accepted/output-language event, exact error |
| Knowledge soundness | Exact relation, extractor access, straightline/rewinding/quantum mode, trace inputs, knowledge error, runtime, adversary failure, accepting-run conditioning |
| Special soundness | Accepting transcript-tree shape, challenge-diversity coordinates, extractor, information-theoretic or computational failure |
| Round-by-round soundness | Doomed-state predicate, exact partial transcripts, challenge occurrences, per-round transition errors |
| Round-by-round knowledge | Knowledge-state predicate, round extractor, witness flow, per-round extraction errors |
| State-restoration soundness | Restoration game, doomed-state event, stored-prefix semantics, salt, move/query budgets, challenge namespace, static/adaptive and restricted/full variants |
| State-restoration knowledge | Restoration extraction game, extractor access and mode, stored-prefix semantics, salt, move/query budgets, failure and time profile |
| Zero knowledge | Real/simulated experiments, observer, simulator, metric, auxiliary input, adaptivity, oracle programming, session and composition regime |

No inheritance edge is implied by family names. Standard soundness does not
imply RBR or state restoration; special soundness does not generically imply
RBR knowledge; ROM does not imply QROM; HVZK does not imply malicious-verifier,
adaptive, multi-theorem, parallel, or concurrent ZK. Every conversion is a
typed theorem/rule instance with exact assumptions and quantitative loss.

### 8.3 Typed quantitative algebra

The common quantitative substrate is a multi-sorted exact expression language.
Representative sorts include:

```text
Probability
StatisticalDistance
ComputationalAdvantage
ExtractionFailure
KnowledgeError
ExtractionSuccess
QueryCount
MoveCount
RoundCount
RunningTime
ExpectedRunningTime
ByteCount
CommunicationCount
FieldSize
Degree
SecurityParameter
AsymptoticFunction
CostObservation
```

Family profiles admit only meaningful operators and side conditions. The
combined library may include exact rational arithmetic, sums, products,
`1 - product(1 - epsilon_i)`, maxima, minima, powers, binomial coefficients,
substitution, reindexing, expectation, and explicit concrete-to-asymptotic
lifts. Operators never coerce dimensions implicitly.

Every inference retains a loss ledger showing source terms, substitutions,
side conditions, and the exact output expression. Unsupported symbolic forms
return `Unsupported` rather than approximate silently.

## 9. Fiat--Shamir, transport, composition, satisfaction, and coverage

### 9.1 Fiat--Shamir theorem applicability

Stage 3 supplies exact admitted Fresh and FS Protocols, an exact admitted
transcript construction, and affirmative `CheckedFSConstruction` with exact
maps. Stage 4A defines the conventional `FSCompile` seam precisely as:

```text
CheckFSTheoremApplicability<T>(
  admitted Fresh Protocol,
  admitted FS Protocol,
  admitted transcript construction,
  affirmative CheckedFSConstruction,
  exact FS theorem schema T,
  exact established theorem capability
    or explicitly admitted assumed-theorem proposition,
  exact source and target semantic model instantiations,
  for every theorem, subject, model, transcript, codec, oracle, occurrence,
    and parameter correspondence:
      affirmative established correspondence capability
        or explicitly admitted assumed-correspondence proposition,
  global hypotheses and quantitative parameters)
  -> AnalysisAttemptOutcome<FSTheoremApplicability<T>>
```

The affirmative capability is named
`EstablishedFSTheoremInstance<T, AssuranceClass>`. Its semantic record is
`CheckedFSTheoremInstance<T>`. The names `FS-valid`,
`CheckedFSTheoremInstantiation`, and an unqualified `FSCompileCapability` are
not aliases because they encourage construction, validity, or preservation
inferences that the result does not establish.

`FSTheoremInstanceId` binds the exact Stage 3 operands and maps, theorem schema,
model instances, correspondence proposition IDs, parameter substitution,
global residual hypotheses, every assumed correspondence proposition, and the
exact property-port schemas exposed by `T`. The semantic and validation bases
proving that instance retain their own identities. Every assumed theorem or
correspondence proposition is canonically unioned into the theorem-instance
hypothesis context; it cannot satisfy a premise requiring an established
affirmative correspondence capability.

An affirmative result states only that this exact construction and occurrence
instantiate the named theorem schema under the retained hypotheses. It exposes
zero or more attenuated live
`PropertyTransportPort<T,SourcePremiseSchemas,TargetFamily>` capabilities. One
port binds an exact tuple of source-family proposition schemas, the target
family and regime, extra hypothesis and side-condition schemas, subject/model/
occurrence maps, and one quantitative transformer. It does not assert any
source property and transports no property by default.

Codec, framing, statement/session binding, message prefix, salt, rate,
capacity, challenge decoding and bias, oracle model, query/move bounds,
adaptivity, abort, and termination enter whenever theorem `T` reads them.

No applicable theorem, incomplete correspondence, or unsupported ROM/QROM
regime yields `Unsupported` or `CannotAnswer`; none makes the admitted target
malformed or a cryptographic property false. A mere theorem assertion or
citation is also insufficient. If the family deliberately permits an assumed
theorem proposition, that exact unresolved proposition appears in the final
hypothesis context. A negative theorem-applicability proposition exists only
where an exact complete instantiation procedure or checked
counter-proposition supports it.

### 9.2 Property transport

```text
PropertyTransport<T,SourcePremiseSchemas,PTarget>(
  exact tuple of affirmative established source judgments matching
    SourcePremiseSchemas,
  affirmative
    PropertyTransportPort<T,SourcePremiseSchemas,PTarget>
    or another exact transform-theorem port with the same signature,
  independently admitted target subject,
  exact source-to-target subject, occurrence, relation, witness, observer,
    model, and parameter maps,
  exact side-condition judgment capabilities,
  exact target AnalysisProposition<PTarget>)
  -> AnalysisAttemptOutcome<PTarget>
```

The checker recomputes the target conclusion and requires its hypothesis
context to equal the canonical union of inherited source hypotheses, theorem
and relation hypotheses, and undischargeable side conditions, minus only
hypotheses discharged by exact checked rules. It retains the complete
substitution and quantitative-loss ledger.

A different source-premise tuple, target property, property regime, or
quantitative transformer requires a different port even over the same
structural construction. This permits, for example, a theorem whose exact
restricted state-restoration premise establishes a distinct plain-soundness
target family; it does not invent a subtype cast. Direct re-analysis of the
target remains a separate valid basis lane and may establish the same target
proposition without transport. Failure to apply a transport is never a
negative target property; it is unsupported, cannot-answer, refused,
malformed, or checker failure. A target negative needs its own exact
refutation basis.

### 9.3 Property composition

Property composition begins only from independently admitted children and
target, an admitted composition specification, and affirmative
`CheckedCoreComposition` with resolved maps.

```text
PropertyComposition<P,Op>(
  exact affirmative child occurrence judgment capabilities,
  admitted target,
  admitted composition specification,
  affirmative CheckedCoreComposition with resolved maps,
  exact operator and property theorem,
  randomness/challenge topology,
  relation and witness morphisms,
  captured failures and reaches,
  terminal/suppression policy,
  admitted ChangeContracts and exact ChangeConforms capabilities,
  exact side-condition judgments,
  assumptions, substitutions, and loss ledger,
  exact target AnalysisProposition<P>)
  -> AnalysisAttemptOutcome<P>
```

`Sequential`, `Parallel`, `Interleaved`, `Concurrent`, `SharedChallenge`,
`Batched`, `Repeated`, `Lift`, `FailureCapture`, and `FiatShamirTransform` are
different operator profiles. A family supplies only the laws justified for one
exact operator. Child property truth alone is never a composition theorem.
Child residual hypotheses are inherited exactly. Failure to compose does not
establish a negative target property.

### 9.4 `RelationSatisfies` ownership

Stage 4A assigns `RelationSatisfies` to **Relations**, not Analysis. Predicate
truth for one admitted definition and instance under one occurrence-local
private witness is base relation semantics. Analysis consumes its exact
qualified capability in completeness, knowledge, and other questions.

The Relations-owned operation requires an exact admitted relation-semantics
subject rather than trying to execute an opaque `RelationDefinitionRef`:

```text
CheckRelationSatisfaction(
  exact RelationDefinitionRef,
  admitted RelationSemanticModel,
  admitted RelationInstance,
  occurrence-local PrivateWitnessAssignment,
  exact Relations-owned evaluation or checking basis,
  exact assumptions)
  -> Qualified<CheckedRelationSatisfaction>
```

Relations must retain:

- exact definition, interface, instance, public values, and interpretation
  regime;
- occurrence-local private witness authority;
- exact satisfaction checker/model and dependency closure;
- affirmative, negative, unsupported, cannot-answer, refused, malformed, and
  checker-failure outcomes; and
- no inference from relation correspondence or equal bytes to satisfaction.

The public satisfaction record identity excludes secret witness bytes. The
live confidential capability retains the witness occurrence without exposing
a globally content-addressed secret equality oracle.

An affirmative result states that this exact witness occurrence satisfies this
exact instance under the exact model. A negative states only that this exact
witness occurrence does not satisfy it; it establishes neither instance
unsatisfiability nor witness nonexistence. Public persistence is prohibited by
default. A remote non-revealing proof of satisfaction is a separate proof or
certificate protocol, not serialized witness authority.

### 9.5 Property coverage and reliance

Coverage has four owners that must not collapse:

1. PIR, Relations, or another structural owner exports the exact finite claim,
   round, occurrence, observer, or obligation surface.
2. The Analysis family profile expands that surface into exact proposition
   obligations where that expansion is part of property meaning.
3. Analysis checks exact proposition, polarity, subject, map, model,
   hypothesis, bound, and assurance matches and returns a factored coverage
   ledger.
4. The named relying consumer defines which obligations, hypotheses,
   assurance classes, and residual trust roots are acceptable for its use.

The source- or consumer-owned requirement is exact:

```text
AnalysisRequirementManifest {
  owner_and_purpose,
  exact source surface and expansion profile,
  exact required proposition patterns and polarities,
  exact accepted hypothesis and bound predicates,
  exact accepted assurance and trust-root predicates
}
```

Analysis defines:

```text
CheckAnalysisCoverage(
  owner-defined AnalysisRequirementManifest,
  exact source-owned surface views,
  exact qualified Analysis judgment capabilities,
  exact occurrence and projection maps,
  coverage profile)
  -> Qualified<CheckedAnalysisCoverage>
```

An affirmative result means only that the supplied exact judgments cover the
exact manifest. A negative retains missing, wrong-subject, wrong-map,
wrong-model, wrong-polarity, wrong-hypothesis, wrong-bound, or wrong-assurance
entries. It is not a negative cryptographic property.

Analysis cannot invent the structural surface or consumer reliance policy.
This result is distinct from Protocol admission, endpoint realization
coverage, truth of any individual proposition, and a global `ArtifactVerified`
or universal “all claims” state.

## 10. Compiler semantic planes

### 10.1 Five-plane architecture

Compiler separates five planes whose identities and authorities do not
collapse:

```text
Problem plane
  TransformProblem + DecisionPolicy

Production plane
  CompileRunRequest + SearchJob + replaceable producer state

Proposal-resolution plane
  ExplorationSpace + FrozenProposalScope + DeclaredAlternatives
  + total AlternativeResolution ledger

Qualification and assessment plane
  PIR-owned admission + exact transition qualification
  + CompilerLegality + exact constraints and objectives

Decision plane
  CandidateDomain + exact closure basis + complete decision ledger
  + scoped closed decision or explicitly open report
```

The problem plane states what semantic transition and comparison are being
asked for. The production plane may be mutable, nondeterministic,
interruptible, parallel, heuristic, or absent. The proposal-resolution plane
freezes exactly which alternatives a scoped claim purports to resolve before
admission results are known. The qualification plane creates semantic
candidates only after independent admission and exact transition checks. The
decision plane compares only those qualified cases under one declared scope.

No producer observation, proposal, alternative ordinal, target bytes,
assessment record, score, or decision may stand in for an upstream live
capability.

### 10.2 Transform problem, decision policy, and run request

```text
TransformProblem {
  exact admitted predecessor references,
  exact target-admission regime,
  permitted TransformIntent profiles,
  required transition relation claims and accepted polarities,
  permitted intentional-change contracts,
  semantic-path policy,
  required lineage-map families
}

DecisionPolicy {
  alternative-scope and domain-formation specification,
  exact basis and residual-trust acceptance policy,
  required Analysis claim patterns,
  required peer-owner, Stage4B-owned, and Evidence-derived fact/value schemas,
  exact candidate-association and input-completeness rules,
  exact QualificationResolutionPolicy,
  exact typed constraints,
  exact typed objectives,
  comparison, Pareto, tie, and representative policy,
  requested closed-decision or open-report strength
}

CompileRunRequest {
  transform_problem_id,
  decision_policy_id,
  SearchJob,
  optional named replay or audit consumer
}
```

`TransformProblemId` identifies transition meaning without scoring or search.
`DecisionPolicyId` identifies the comparison claim without a producer.
`CompileRunRequestId` identifies one operational attempt. Producer choice,
seeds, heuristics, worker count, timeout, solver limits, mutable registry
state, and discovery order occur only in `SearchJob` unless an exact bounded
exploration space is itself the declared scope of a weaker report.

Changing a producer does not change a transform problem or decision policy.
Changing a required observer, relation, intentional delta, domain scope,
constraint, objective, comparator, or accepted trust basis does.

`DecisionPolicy` contains schemas and rules, not concrete future facts about a
candidate. In particular, it may require a Stage 4B feasibility result or an
Evidence-derived cost estimate of a declared type, but it cannot name the
result record before the candidate exists. Exact candidate-associated inputs
enter the qualification and assessment plane through an immutable
`AssessmentInputPortfolio` defined in Section 12.3.

Qualification multiplicity is resolved by one exact policy:

```text
QualificationResolutionPolicy =
    RequireSpecifiedSupport(exact qualification schema)
  | RequireSpecifiedCorroboratingSet(exact set schema)
  | ChooseCanonicalSupport(exact total order and admissibility predicate)
  | CompareQualifiedAlternatives
```

Only an explicitly pre-bound submitted-input policy variant may name concrete
`QualificationId` values in advance; it then names the exact submitted
candidate association too. Ordinary producer flows declare schemas and obtain
concrete qualification identities from the later assessment-input portfolio.

The final form expands the derived comparison carrier from one resolved
support selection per `CandidateId` to every accepted exact qualified
alternative `(CandidateId, QualificationId)` or, when explicitly declared,
`(CandidateId, CanonicalQualificationSetId)`. No implementation may choose a
convenient proof basis after seeing scores or silently vary the qualification
set between replay occurrences.

### 10.3 Transform intent, recipes, proposals, and alternatives

`TransformIntent<F>` states the exact family, source subjects, target-shape
restrictions, relation direction, observers and models, protected
observations, permitted deltas, required map schemas, and direct, adjacent,
composed, or adjacent-plus-end-to-end checking policy. It makes no claim that
a target exists.

`ProposalRecipe` states one method for producing exact carrier material. MLIR
Transform programs, e-graph explanations, SMT synthesis traces, verified
rewriters, learned plans, and manual edits are recipes. A recipe alone is not
a candidate or replay basis; it must materialize a frozen proposal before
semantic processing.

```text
ProposalOccurrence {
  compile_run_request_id,
  search_job_occurrence_id,
  exact proposed final carrier material,
  exact proposed semantic-intermediate carrier material,
  unauthoritative lineage and occurrence maps,
  unauthoritative relation, proof, and certificate material,
  producer and recipe provenance
}

ProposalMemberDescriptor =
    ExactProposalOccurrence(exact occurrence and submitted material)
  | ExactSubmittedTransitionMaterial(exact source, target, path, and maps)
  | ExactFiniteGrammarMember(exact grammar coordinate and materialization input)

ProposalScope {
  transform_problem_id,
  scope_kind,
  exact canonical finite member-descriptor sequence
    or exact finite grammar with canonical bounds and member order,
  exact multiplicity and pre-admission duplicate policy,
  exact freeze rule
}

ProposalScopeId = H(
  "zkc/compiler-proposal-scope",
  TransformProblemId,
  scope kind,
  canonical descriptor sequence or grammar and bounds,
  canonical member order,
  multiplicity and pre-admission duplicate policy,
  freeze rule)

DeclaredAlternative {
  proposal_scope_id,
  canonical member coordinate,
  exact ProposalMemberDescriptor
}
```

`ProposalOccurrenceId` and `DeclaredAlternativeId` are operational and scope
identities, not semantic candidate identities. A proposal scope used by a
closed claim is frozen before target admission, transition outcomes,
constraints, or objectives are observed. This prevents a producer from
declaring only successful or high-scoring outputs after evaluation.

`DeclaredAlternativeId = H(ProposalScopeId, canonical member coordinate,
exact member descriptor)`. The proposal-scope preimage therefore does not
contain `DeclaredAlternativeId` and no identity cycle exists. Expanding a
finite grammar deterministically reconstructs the same ordered descriptor
sequence before any semantic result is observed. A heuristic discovery stream
that cannot do this is `OpenExploration`, not a closed proposal scope.

## 11. Alternative resolution, admission, and transition qualification

### 11.1 Total alternative resolution before candidate formation

Every declared alternative receives exactly one terminal or unresolved
resolution entry:

```text
AlternativeResolution =
    ResolvedTo(CanonicalNonEmptySet<CandidateId>)
  | DuplicateOf(exact earlier alternative, checked quotient,
                CanonicalNonEmptySet<CandidateId>)
  | ConclusivelyExcluded(exact admission or relation facts)
  | Unsupported(exact carrier, regime, family, model, or checker boundary)
  | CannotAnswer(exact missing basis or incomplete semantic check)
  | Refused(exact missing authority or policy refusal)
  | Malformed(exact proposal, map, certificate, or framing defect)
  | CheckerFailure(exact failed checking occurrence)
  | SearchOrResolutionIncomplete(exact interruption or unproved pruning)
```

`AlternativeResolutionLedgerId` binds every and only
`DeclaredAlternativeId` in canonical order to one such result. A terminal
conclusive exclusion maps an alternative to no candidate for an exact stated
reason. Any unsupported, cannot-answer, refusal, checker failure, or incomplete
entry remains unresolved for a closed originating-scope claim even if other
alternatives succeed.

A checked `AlternativeResolutionCoverage` establishes totality over one exact
alternative scope and the exact canonical image in semantic candidates. It
does not establish that the producer discovered every legal transform unless
a separate exact exploration- or grammar-coverage result proves that claim.

### 11.2 PIR-owned target admission

Every proposed whole Protocol and every semantic intermediate is independently
authenticated and admitted by PIR under its exact regime and dependency
closure:

```text
exact raw carrier
  -> PIR authentication
  -> PIR whole-Protocol admission
  -> process-local AdmittedProtocol capability
```

The producer, Compiler, proposal ledger, persisted bytes, or a prior decision
cannot supply or serialize this capability. Admission establishes only valid
Protocol meaning. It establishes neither transform intent, predecessor/target
relation, property transport, eligibility, nor selection.

An exact negative admission result may conclusively exclude one alternative
from a frozen scope. Malformation, unsupportedness, missing authority, and
checker failure retain their own qualified meanings and never become a
negative transition fact.

### 11.3 Semantic path and exact transition qualification

```text
SemanticPath {
  ordered exact admitted Protocol identities,
  ordered exact edge proposition identities,
  exact typed lineage and occurrence maps,
  exact intentional-change contracts,
  exact adjacent and requested end-to-end relation coordinates
}

TransitionCase {
  transform_problem_id,
  exact admitted predecessor,
  exact admitted target,
  semantic_path_id,
  exact required transition propositions, polarities, and family-specific
    semantic facts,
  exact checked lineage meanings,
  exact admitted semantic intermediates when read
}
```

The exact Analysis, Relations, PIR, or other bridge owner defines and checks
each semantic predicate. Compiler orchestrates the checks but cannot define,
weaken, or reinterpret them. A family may require `ProtocolEq`, directed
`TraceRefines`, `ChangeConforms`, another exact relation, or a typed
conjunction of independently owned results.

Every semantic intermediate is independently admitted and every adjacent edge
is independently checked. Producer-internal IR that carries no semantic claim
does not become a Protocol intermediate. An end-to-end relation is additional;
it replaces adjacent checks only when a named exact rule proves that the
omitted path facts are irrelevant to every requested consumer.

Lineage maps are checked typed witnesses to a relation. They do not establish
that relation or transport a property by themselves.

### 11.4 Separate Compiler legality

`CompilerLegality` is a Compiler-owned question over one exact transform
problem and transition case. It checks only such problem-local facts as:

- allowed transform families and path shapes;
- maximum semantic path length or declared application multiplicity;
- request conformance and closed parameter ranges;
- other rules whose meaning is explicitly Compiler policy.

It consumes, but never recreates, exact admission and transition capabilities.
Acceptance of a proof basis, assumption, assurance class, or residual-trust
closure is not transition legality. Those facts are resolved by the exact
`DecisionPolicy` and `QualificationResolutionPolicy` during assessment.
Its result is:

```text
Legal
Illegal(exact completed policy fact)
Unsupported
CannotAnswer
Refused
Malformed
CheckerFailure
```

`Illegal` is not a negative Protocol relation or property result.

## 12. Candidate, qualification, assessment, and domain identity

### 12.1 Identity layers

```text
TargetAlternativeId
  = exact admitted target Protocol identity

SemanticPathId
  = exact admitted subject sequence + exact edge claims, maps, and deltas

TransitionCaseId
  = TransformProblemId + exact source and target + SemanticPathId
    + exact required relation propositions, polarities, family-specific
      semantic facts, models, maps, and intentional deltas

QualificationId
  = one exact affirmative admission/transition support DAG
    + semantic and validation basis identities + residual trust

CandidateId
  = TransformProblemId + TransitionCaseId

ComparisonAlternativeId
  = DecisionPolicyId + CandidateId + exact resolved CanonicalQualificationSetId

CandidateQuotientClassId
  = CandidateDomainPolicyId + exact checked equivalence class of CandidateIds

AssessmentId
  = DecisionPolicyId + ComparisonAlternativeId + AssessmentInputPortfolioId
    + AssessmentInputCompletenessResultId
    + exact legality, constraint, objective, and decisive dependency results

DecisionId
  = TransformProblemId + DecisionPolicyId + CandidateDomainId
    + ComparisonAlternativeDomainId
    + exact closure and decision ledger + comparison result
```

The target identity, semantic transition, one proof basis, one assessment, and
one decision are therefore never aliases. Checking-occurrence identity is yet
another category.

`CandidateId` excludes producer identity, recipe, search order, alternative
ordinal, proof bytes, and checking occurrence. Multiple proposals or proofs
may support one candidate.

`ComparisonAlternativeId` is not a second semantic candidate. It is a
DecisionPolicy-scoped comparison operand that binds one candidate to the exact
qualification or canonical corroborating set used to assess it. Projecting a
comparison alternative to `CandidateId` is total and unique; the reverse may
be one-to-many only under `CompareQualifiedAlternatives`.

### 12.2 Path and basis multiplicity

The same admitted target through different semantic paths denotes distinct
`TransitionCaseId` and `CandidateId` values by default. An operational producer
plan is not a semantic path and therefore does not distinguish candidates.

Two paths, lineage maps, or transition cases may be quotiented only by an exact
checked `CandidateQuotient` proving that the difference is irrelevant to every
constraint, objective, property dependency, replay obligation, selected
consumer, and later declared input. Target-ID equality, provider deduplication,
or equal scores are not such a proof.

Different proof objects that establish the identical proposition, result,
hypotheses, model, and assurance coordinates support one candidate through
different `QualificationId` values. If a basis changes an assumption, model,
observer, map, quantitative result, or accepted assurance condition, the
semantic claim or assessment has changed rather than merely its proof bytes.

Normally `QualificationResolutionPolicy` selects or requires one exact
qualification or canonical corroborating set inside one candidate assessment.
When it chooses canonical support, the declared total order and admissibility
predicate make the result replay-stable. If proof-basis trust is itself an
optimization axis, `CompareQualifiedAlternatives` makes the comparison carrier
explicitly `(CandidateId, QualificationId)` (or an exact declared
qualification set), and the decision reports both. It must not silently
duplicate or mutate the semantic candidate domain.

### 12.3 Candidate assessment and complete ledger

```text
AssessmentInputPortfolio {
  decision_policy_id,
  candidate_id,
  exact candidate-associated QualificationIds and live capability requirements,
  exact Analysis and peer-owner result records required by policy schemas,
  exact Stage4BOwnedFactOrValue records required by policy schemas,
  exact Evidence-derived result records required by policy schemas,
  exact association material from every input to this candidate and policy
}

AssessmentInputCompletenessProposition {
  assessment_input_portfolio_id,
  decision_policy_id,
  exact required-schema coverage, uniqueness, association, polarity,
    assurance, and residual-trust acceptance claims
}

CandidateAssessment {
  candidate_id,
  comparison_alternative_id,
  assessment_input_portfolio_id,
  assessment_input_completeness_result_id and live affirmative capability,
  exact qualification set fixed by the comparison alternative,
  exact admission and transition support ledger,
  exact CompilerLegality result,
  required Analysis and peer-owner result ledger,
  typed constraint-result ledger,
  typed objective-value ledger,
  exact residual-trust closure,
  assessment_outcome
}
```

`AssessmentInputPortfolioId` content-identifies only the immutable, canonical
candidate-indexed portfolio body. It contains concrete results only after a
`CandidateId` exists. Each result retains its owner, proposition or value
schema, polarity, model, assurance, residual trust, and live-capability
requirement; the portfolio cannot cast or merge them.

The separate Compiler-owned `AssessmentInputCompletenessResult` binds that
portfolio ID and the exact policy, checks association and required-schema
coverage, and mints a process-local capability. It is an input to
`CandidateAssessment`, never a field in the portfolio it checks. Completeness
means complete for the exact `DecisionPolicy` schema, not that every
conceivable property of the candidate was computed. Each concrete peer-owner
fact remains independent of the resulting assessment; a checked
`AssessmentInputUse` edge records how that fact's exact subject tuple satisfies
one policy schema for the candidate.

Assessment outcomes are:

```text
Eligible(exact satisfied constraint closure and sufficient objective facts)
DefinitivelyIneligible(nonempty exact violated-constraint or illegality facts)
Undetermined(exact unsupported, cannot-answer, refusal, malformed-support,
             missing-value, or checker-failure blockers)
```

One exact violation or illegality result may conclusively exclude a candidate
even when other unused results are unavailable. An eligible candidate requires
every conjunctive requirement and enough qualified objective information for
the requested comparison. Assessment completeness is therefore relative to
the exact decision policy, not a demand to compute irrelevant fields.

`AssessmentLedgerId` covers every and only member of one exact comparison-
alternative domain. It records a decisive terminal assessment or exact
unresolved blockers for each member. The separate qualification-resolution
ledger covers every semantic candidate, including candidates that cannot yet
be mapped to an accepted comparison alternative. Operational absence is never
semantic ineligibility.

### 12.4 Exploration, proposal, and candidate domains

The target keeps three scopes distinct:

```text
ExplorationSpace
  plans, grammar, numeric bounds, heuristics, and operational search limits

ProposalScope
  one exact frozen descriptor sequence or exact finite descriptor grammar from
  which every DeclaredAlternativeId is reconstructed without semantic results

CandidateDomain
  one canonical finite set of admitted, relation-qualified CandidateIds
```

The authoritative comparison domain ranges over `CandidateId`, never raw
plans, recipes, proposal occurrences, or unresolved declared alternatives. A
proposal scope becomes a candidate domain only through exact total alternative
resolution, checked duplicate treatment, and a checked canonical-image result.

Every closed domain uses an admitted, immutable policy:

```text
CandidateDomainPolicy {
  transform_problem_id,
  domain_form,
  exact originating-scope association rule,
  exact member or canonical-image rule,
  exact CandidateId order,
  exact semantic quotient and multiplicity rule,
  exact closure-proposition schema
}

CandidateDomainPolicyId = H(
  "zkc/compiler-candidate-domain-policy",
  exact CandidateDomainPolicy)

CandidateDomain {
  candidate_domain_policy_id,
  exact originating ProposalScopeId and AlternativeResolutionLedgerId
    when the form reads them,
  canonical finite nonduplicated CandidateId sequence,
  exact quotient-class partition when quotienting is enabled
}

CandidateDomainId = H(
  "zkc/compiler-candidate-domain",
  CandidateDomainPolicyId,
  exact originating-scope and resolution identities when read,
  canonical CandidateId sequence,
  exact quotient partition)

CandidateDomainClosureProposition {
  candidate_domain_id,
  exact membership, admission, relation-qualification, uniqueness,
    canonical-order, originating-scope image, quotient, finiteness,
    and coverage claims required by its domain form
}
```

Only an affirmative checked result for that exact proposition mints the
process-local `CheckedCandidateDomain<D>` capability. A domain object, member
list, solver certificate, digest, or persisted prior capability does not.

Qualification resolution then derives the actual comparison carrier without
changing semantic candidate identity:

```text
ComparisonAlternative {
  decision_policy_id,
  candidate_id,
  exact nonempty CanonicalQualificationSetId accepted by policy
}

QualificationResolutionEntry =
    ResolvedTo(CanonicalNonEmptySeq<ComparisonAlternativeId>)
  | DefinitivelyQualificationIneligible(exact completed policy fact)
  | Undetermined(exact missing support, incomplete support enumeration,
                 unsupportedness, refusal, malformation, or checker failure)

QualificationResolutionLedger {
  candidate_domain_id,
  decision_policy_id,
  exactly one entry for every CandidateId in canonical domain order
}

ComparisonAlternativeDomain {
  candidate_domain_id,
  decision_policy_id,
  qualification_resolution_ledger_id,
  canonical finite nonduplicated ComparisonAlternativeId sequence
}

ComparisonAlternativeDomainId = H(
  "zkc/compiler-comparison-alternative-domain",
  CandidateDomainId,
  DecisionPolicyId,
  QualificationResolutionLedgerId,
  canonical ComparisonAlternativeId sequence)

ComparisonAlternativeDomainClosureProposition {
  comparison_alternative_domain_id,
  exact total candidate coverage, qualification-policy conformance,
    canonical expansion, membership, uniqueness, and projection claims
}
```

For specified, corroborating-set, or canonical-support policies, each resolved
candidate maps to exactly one comparison alternative. Under
`CompareQualifiedAlternatives`, it maps to every and only accepted
qualification alternative declared by the policy's closed enumeration rule.
A definitive qualification rejection may exclude a candidate only through a
completed exact policy fact; an incomplete or open set of possible supports is
`Undetermined` and blocks a closed decision.

Only an affirmative checked comparison-domain closure result mints
`CheckedComparisonAlternativeDomain<Q>`. It proves neither candidate-domain
closure nor any assessment. The decision projects its selected comparison
alternative back to exactly one `CandidateId` and reports the exact support
selection separately.

Supported domain forms are:

```text
SubmittedCandidateSet
  exact canonical finite set of already admitted and transition-qualified
  CandidateIds; closure checks membership, uniqueness, ordering, and every
  stated qualification

ResolvedSubmittedProposalScope
  exact frozen ProposalScopeId + total AlternativeResolutionCoverage
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
  no closed candidate-domain claim
```

Symbolic domain denotation and closure are separate from candidate
infeasibility and optimality. In v0, every member of the symbolic denotation is
already named by `CandidateId`, and its target material has already been
independently materialized, authenticated, admitted by PIR, and transition-
qualified. A symbolic certificate may compress the reconstruction of the
canonical image, domain closure, repeated assessment, or optimality proof; it
cannot replace target materialization, admission, or relation qualification.
An infeasibility certificate establishes constraint failure over that already
closed domain. An optimality certificate establishes the exact comparison
claim over that already closed and adequately assessed domain. One solver
status or certificate cannot silently stand for all three claims.

Under the frozen Stage 3 authority model, symbolic compression cannot grant
ordinary CandidateDomain authority over unnamed or unadmitted alternatives. A
stronger lazy or universally quantified rule that denotes semantic candidates
without independently materializing and admitting every target would require a
separately reviewed future Stage 3 reopening. It is an opportunity, not a v0
claim.

Every completeness claim is scope-qualified. None implies a global optimum
over all legal Protocols.

## 13. Constraints, objectives, and comparison

### 13.1 Typed constraint algebra

A constraint cites an exact claim pattern, accepted qualified polarity,
hypothesis and bound predicate, compatible models and dimensions, and accepted
basis and residual-trust policy.

```text
ConstraintResult =
    Satisfied(exact accepted fact and capability closure)
  | Violated(exact completed contradictory or out-of-policy fact)
  | Undetermined(exact missing or nonterminal semantic input)
  | Unsupported(exact family, model, or predicate boundary)
  | Refused(exact authority or policy refusal)
  | Malformed(exact constraint or offered-input defect)
  | CheckerFailure(exact failed checking occurrence)
```

An affirmative premise requires the exact affirmative capability. An exact
negative may satisfy only an explicitly negative constraint. Models,
observers, directions, property families, hypotheses, quantitative dimensions,
and assurance classes cannot be coerced. Compiler cannot discharge or discard
Analysis hypotheses.

Direct target re-analysis and property-specific transport may establish the
same exact proposition through different qualifications. The constraint checks
claim meaning first and applies its exact basis/trust policy separately.

### 13.2 Objective provenance and knowledge shape

Every objective value has both an owner/provenance class and an epistemic
shape:

```text
ObjectiveProvenance =
    DirectStructural
  | AnalysisDerived
  | EvidenceDerived
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
```

Every value also names its exact subject association, semantic or measurement
model, units and dimensions, environment and procedure when read, uncertainty,
assumptions, availability conditions, dependencies, comparison direction, and
residual trust.

Different provenance or knowledge shapes are comparable only through an
explicit typed rule that retains their qualifications. Minimizing a proved
upper bound is not minimizing actual cost. A measured estimate is not an exact
semantic theorem. A missing value is not implicit infinity; an explicit
availability preference produces only a decision under that named policy.

Raw OIR, realization, endpoint, supplier, or deployment subjects are not
objective values. A `Stage4BOwnedFactOrValue` is an exact later-owner result
bound to the exact target Protocol and every later-owned subject it reads. The
Compiler-owned assessment-input check separately proves that this subject
tuple applies to one exact `CandidateId` and policy schema.

### 13.3 Comparison, ties, and Pareto results

The exact policy is one of:

- lexicographic comparison over a typed objective vector;
- constrained single-objective minimization or maximization;
- dimension-checked weighted aggregation with exact normalization and weights;
- a complete Pareto frontier under exact component orders; or
- another closed versioned comparator with an exact order and completeness
  contract.

Provider order, enumeration ordinal, scheduling, cache state, or discovery time
is never an implicit objective.

For a closed total comparison the result retains both:

```text
OptimalEquivalenceClass
CanonicalRepresentative
```

The canonical minimum `CandidateId` supplies a deterministic representative
only after the exact objective policy has established an equivalence class. It
does not erase tied optima. If user or provider priority matters, it is an
explicit `DeclaredPolicyPreference` objective.

For Pareto requests, the authoritative result is the complete canonical
nondominated set within the exact domain. Selecting one frontier member
requires a separate explicit totalizing policy and produces a distinct
decision claim. An incomplete or uncertainty-induced partial order cannot
silently become a single closed optimum.

## 14. Compiler outcomes and decisions

### 14.1 Closed decisions

```text
CompilerDecision {
  transform_problem_id,
  decision_policy_id,
  alternative_scope_id when the claim reads one,
  candidate_domain_id,
  comparison_alternative_domain_id,
  exact alternative-resolution, candidate-domain-closure,
    qualification-resolution, and comparison-domain-closure bases,
  exact decision-complete AssessmentLedgerId,
  comparison_policy_id,
  Best {
    optimal_equivalence_class,
    canonical_representative_comparison_alternative_id,
    canonical_representative_candidate_id,
    exact selected_qualification_set_id,
    selected_assessment_id
  }
    | CompletePareto { canonical_frontier, exact optional totalization }
    | NoEligible { exact terminal exclusion or infeasibility basis },
  exact residual_trust_closure
}
```

Closed claims are named by their exact scope, for example:

```text
BestInSubmittedCandidateSet<D,Q>
BestInResolvedSubmittedScope<S,D,Q>
BestInEnumeratedClosedDomain<D,Q>
BestInCertifiedSymbolicDomain<D,Q>
CompleteParetoFrontierIn<D,Q>
NoEligibleCandidateIn<D,Q>
```

`D` is the semantic `CandidateDomain`; `Q` is its exact derived
`ComparisonAlternativeDomain`. `NoEligibleCandidateIn<D,Q>` is the target
spelling of the charter's provisional
`NoSelection<D>` closed outcome. The rename removes the ambiguity between
"nothing was eligible in this exact closed domain" and "an open search did not
select anything." It changes no Stage 4A requirement: the former needs a
complete exact exclusion basis, while the latter is only an open report.

`Best` requires both closed domains and a decision-complete assessment or exact
optimality basis over every member of `Q`. `NoEligible` requires both closed
domains and, for every member of `D`, either definitive qualification
ineligibility or definitive illegality/violated-constraint facts for every
derived member of `Q`, or an independently checked infeasibility certificate
over exactly those already closed domains.

No closed `NoEligible` is legal while any declared alternative needed for
scope closure, candidate-domain member, qualification resolution, comparison-
domain member, relation, legality result, constraint, or decisive Analysis
input remains unresolved. Unsupportedness,
cannot-answer, refusal, malformation, missing objective data, and checker
failure cannot be recast as ineligibility.

### 14.2 Open reports

Open or incomplete work may still return useful qualified reports:

```text
QualifiedFeasibleCandidate(exact admitted eligible candidate and assessment)
NondominatedInAssessedSubset(exact subset and comparison qualifications)
IncompleteSearchReport(
  frozen exploration/proposal progress,
  retained qualified candidates,
  unresolved alternatives or assessments,
  exact blockers)
```

These reports mint no domain-closure, global frontier, optimality, or
`NoEligible` capability. An empty heuristic result is an incomplete report or
an empty observed subset, never a negative statement over an unstated
universe. `BestAmongCompletedAssessments` may be offered as an explicitly
subset-relative report; it is not `BestInDomain`.

### 14.3 Outer qualified outcomes

The Compiler operation also preserves:

```text
Unsupported(requested family, model, domain, certificate, or comparator)
CannotAnswer(missing named semantic input, resolution, or closure basis)
Refused(missing authority or prohibited policy)
Malformed(request, alternative scope, domain, identity, cycle, or framing)
CheckerFailure(operational failure; no decision conclusion)
```

A proposal-local terminal defect belongs in the alternative-resolution ledger
when the exact enclosing scope permits that classification. A defect in the
request, domain definition, coverage checker, assessment ledger, or decision
checker is a whole-operation outcome.

### 14.4 Decision authority and non-implications

The capability chain remains factored:

```text
CheckedCompileRunRequest
CheckedTransition<F>
QualifiedCandidate
CheckedCandidateDomain<D>
CheckedQualificationResolution<D>
CheckedComparisonAlternativeDomain<Q>
CheckedCandidateAssessment
CheckedAssessmentClosure<Q>
QualifiedCompilerDecision<D,Q>
```

`QualifiedCompilerDecision` establishes only its exact scoped comparison
claim. It never mints, serializes, widens, or substitutes for Protocol
admission, a transition relation, property transport, a Stage 4B fact, or a
consumer reliance decision. A consumer may receive these independent live
capabilities together, but no generic `VerifiedCandidate` capability exists.

## 15. Replay, persistence, caching, and trust

### 15.1 Cold Analysis replay

An optional `AnalysisReplayBundle` is created only for a named independent
consumer, expensive reconstruction, or a real cross-process trust separation.
It retains the exact subject reconstruction manifests, semantic and basis read
closures, model, question, exact proposition, operational request when
relevant, hypothesis closure, semantic basis, validation basis,
proof/certificate or direct-check material, correspondence propositions,
checker contracts, expected qualified result, disclosure policy, and exact
rooted residual-trust closure.

```text
AnalysisReplayBundleId = H(
  "zkc/analysis-replay-bundle",
  exact canonical AnalysisReplayBundle,
  named consumer identity,
  exact replay purpose and disclosure policy)

ReplayOccurrenceHandle =
  fresh process-local nonserializable owner-issued handle

AuditEventRecordId = H(
  "zkc/analysis-replay-audit-event",
  AnalysisReplayBundleId,
  owner-issued inert occurrence reference,
  exact attempted operation and operational outcome)
```

`ReplayOccurrenceHandle` is deliberately not a semantic content ID and cannot
cross reset or serialization. `AuditEventRecordId` may distinguish inert audit
records for repeated operations, but neither it nor the owner-issued reference
mints Analysis authority.

Cold replay reauthenticates and re-admits every subject, reconstructs every
owner-created view and dependency, rechecks external statement/model
correspondence propositions, reruns the semantic derivation through the exact
validation basis, requires exact proposition and qualified-result equality, and
mints a fresh local capability. `AnalysisReplayBundleId`, stored result bytes,
a prior exit code, an `AuditEventRecordId`, or an earlier occurrence handle
never carries authority.

Cheap direct checks are recomputed by default. Secret witnesses, private
adversarial state, and sensitive counterexamples are not included in a public
bundle; a family may prohibit persistence entirely or require a separately
owned confidential replay contract.

### 15.2 Cold decision replay

A `CompilerReplayBundle` retains:

- exact `TransformProblem` and `DecisionPolicy`;
- the `CompileRunRequest` and `SearchJob` only when an operational audit or
  explicitly scoped exploration claim reads them;
- the exact `ExplorationSpace`, frozen `ProposalScope`,
  `DeclaredAlternativeId` set, and total `AlternativeResolutionLedger` when
  needed to justify scope resolution;
- semantic `CandidateDomain` definition, checked canonical image, quotient
  policy, and exact denotation and closure bases;
- the total `QualificationResolutionLedger`, derived
  `ComparisonAlternativeDomain`, and exact closure bases;
- symbolic denotation/closure certificates separately from any infeasibility
  or optimality certificates;
- exact target and semantic-intermediate carrier material plus dependency
  bundles sufficient to reauthenticate and re-admit them;
- exact transition claims, maps, bases, and replay material;
- exact Analysis claims, bases, and replay material;
- exact `AssessmentInputPortfolio` bodies, their separate completeness and use
  results, resolved qualification sets, `CompilerLegality`, constraint
  definitions and results, and objective definitions and qualified values;
- every exact `Stage4BOwnedFactOrValue` or Evidence-derived value read by an
  assessment, plus the separate Compiler-owned candidate-target association;
- decision-complete assessment ledger;
- comparator, optimal equivalence class or Pareto frontier, representative
  policy, and decision; and
- named consumer and residual trust.

The bundle contains no `AdmittedProtocol`, checked-transition, assessment, or
decision capability. Replay does not rerun a mutable producer. It reconstructs
and reauthenticates the exact subjects, obtains fresh PIR admissions, rechecks
transition qualifications and legality, validates exact Analysis and peer-
owner bases, rechecks alternative resolution and domain closure, recomputes
the decision-relevant assessments, repeats comparison, and mints fresh local
capabilities from their respective owners.

Decision replay, producer rerun, and bit-for-bit proposal reproducibility are
three different properties.

### 15.3 Caches

The target distinguishes:

```text
ProducerSearchCache
  unauthoritative plans, proposals, and discovery hints

SemanticReplayCache
  immutable basis and certificate material requiring exact revalidation

EvidenceCache
  exact observations retaining environment, procedure, time, and uncertainty

ProcessLocalAuthorityMemo
  owner-internal reuse of an already live capability under identical immutable
  dependencies and within the same authority lifetime
```

A persistent cache key includes every semantic subject, regime, question,
proposition, model, assumption, semantic and validation basis, checker
contract, alternative scope, resolution rule, domain and quotient policy,
constraint, objective, Stage 4B or Evidence association, environment, and
version coordinate that can affect the cached material. A hit is only a hint
until exact key reconstruction and the required owner revalidation complete.

Basis drift makes an entry stale. It does not make the underlying semantic
claim false. Cached bytes, signatures, old decision IDs, and matching digests
cannot rehydrate a live capability. Only process-local owner memoization may
reuse one that has never crossed reset, serialization, authority lifetime, or
dependency identity.

### 15.4 Residual trust

Every completed record carries an exact finite acyclic
`ResidualTrustClosure`. Each node states one exact correctness or adequacy
claim and each edge states why that claim depends on another. Every path must
terminate at an explicitly identified trust root; `trusted`, `machine checked`,
`zkc`, a project name, or an institution name is not a root.

Representative root forms are:

```text
NormativeSemanticDefinitionRoot(exact regime/model/rule identity and claim)
SourceAdmissionRoot(exact owner operation and checker contract)
CheckerImplementationRoot(exact implementation identity,
                          contract-correspondence claim,
                          execution-platform identity)
ExternalKernelRoot(exact logic, kernel, elaborator, imports, and soundness claim)
CertificateDecoderOrTranslationRoot(exact language, decoder/translation, claim)
TrustedDecisionOracleRoot(exact engine, input contract, and asserted claim)
MeasurementProcedureRoot(exact environment, procedure, and uncertainty claim)
```

`ResidualTrustClosureId` hashes the complete rooted DAG, including exact root
claims and identities. A formally verified checker replaces an implementation
root only with its exact proof-kernel, model, compiler, and execution roots; it
does not erase the bottom. Missing, circular, `other`, or free-text roots make
the basis malformed or unsupported.

Every completed record therefore names, rather than hides:

- semantic-regime and model adequacy;
- rule/theorem truth and faithful encoding;
- subject-to-model and external-statement correspondence;
- checker implementation correctness or formal verification status;
- certificate translation and proof-checker assumptions;
- admitted dependency meanings;
- measurement environment and procedure when applicable; and
- consumer-specific reliance outside the semantic result.

“Small checker,” “verified producer,” “machine checked,” “certificate
accepted,” and “replayed” are separate qualifications.

Logical premises and trust roots remain different. A hardness assumption,
unproved external theorem, or assumed model correspondence belongs to the
proposition's hypothesis context. A checker, encoding, kernel, runtime, or
normative-definition correctness obligation belongs to the residual-trust DAG.
A later consumer may accept or reject roots, but cannot change the proposition
or silently reclassify a hypothesis as trust metadata.

A Compiler decision retains the exact union of every root used decisively for
alternative resolution, domain closure, target and transition qualification,
legality, constraint satisfaction or violation, objective comparison,
infeasibility or optimality certification, and representative selection. It
cannot compress this graph into one assurance rank or inherit only the roots
of the selected target: a closed optimum or `NoEligible` claim also depends on
the exact facts used to classify and compare the other domain members.

## 16. Stage 4B, Evidence, and reliance boundaries

Stage 4A and Stage 4B share exact meanings for protected observations,
failures, terminals, challenge occurrences, Interfaces, Plans, and occurrence
maps. Stage 4A does not define OIR, projection, local OIR validity,
realization, supplier binding, endpoint feasibility, deployment, invocation,
or execution results.

An Analysis question that reads an OIR, target, supplier, realization,
invocation, or endpoint result includes that exact later-owned subject and
view. Compiler never treats a raw later-owned subject, identifier, supplier
claim, or runtime record as an objective value or eligibility fact. It may
consume only an exact `Stage4BOwnedFactOrValue` whose live capability retains:

- the exact candidate target Protocol identity and admission regime to which
  the fact applies;
- every exact OIR, Interface, Plan, projection, realization, target, supplier,
  endpoint, environment, and occurrence operand actually read;
- the exact Stage 4B question, model, checker, qualified outcome, basis, and
  residual trust; and
- enough source-owned subject and map identity to check association to a
  candidate target without naming a future Compiler assessment.

The `Stage4BOwnedFactOrValue` never contains `AssessmentId`. The
`AssessmentInputUse` result binds the independent fact, exact policy schema,
`CandidateId`, and `AssessmentInputPortfolioId`; the later assessment consumes
that result. This orientation prevents an input/assessment identity cycle and
leaves Stage 4B meaning invariant under Compiler policy.

Such a fact is read only when `DecisionPolicy` names it. Its absence is an
exact undetermined, unsupported, or refused assessment boundary when required,
never a hidden rejection criterion. If it is absent from the policy, Compiler
must be invariant under its substitution.

Projection, realization, and endpoint meaning are invariant under Compiler
history. Two decisions that identify the same exact admitted target cannot
change its Stage 4B projection or realization result merely because they used
different producers, proposals, semantic paths, domains, objectives, or
selection histories. Any Stage 4B operation reconstructs its result from its
own exact admitted Protocol, Interface, Plan, OIR, target, supplier, endpoint,
and regime inputs. Compiler provenance may be Evidence or policy metadata; it
cannot be a hidden semantic input.

If one Protocol candidate has several Stage 4B alternatives, Stage 4A either
consumes one exact later-owned fact under a declared aggregation/choice policy,
or a future higher-level owner defines an explicit product domain. Stage 4A
does not silently widen `CandidateId` into an OIR, realization, deployment, or
endpoint alternative.

Evidence owns observations, provenance, experimental procedures, environments,
samples, uncertainty, and measurement records. Analysis owns any rule that
turns exact Evidence into a qualified semantic claim. Compiler may also
consume an exact Evidence-owned estimate through the objective schema, but it
must preserve the Evidence association and epistemic shape rather than relabel
it as an exact semantic value. Compiler owns only comparison policy over exact
accepted facts and values. A later reliance consumer decides whether that
basis is sufficient for one use.

A durable Compiler record identifies an exact selected Protocol alternative;
it does not contain, mint, serialize, or rehydrate its `AdmittedProtocol`
capability. A same-process result may return the independently PIR-owned live
capability alongside the decision, but no authority conversion occurs.
Compiler output is not OIR, emitted code, deployed software, a successful
execution, or a release/security verdict.

## 17. Extension law

The semantic surface is closed where meaning is at stake and open where
production is replaceable.

Open without semantic redesign:

- a new producer for an existing transform intent;
- a new search algorithm, MLIR transform, e-graph engine, or synthesis tool;
- a new proof search tactic or proof producer for an existing semantic-basis
  contract;
- a new validation/checker implementation that is independently authenticated
  against an unchanged exact checker contract, with a new
  `ValidationBasisId` and trust closure;
- a new derivation, external theorem instance, or certificate accepted under
  an already admitted family, theorem schema, correspondence adapter, and
  certificate rule set; or
- a cache or scheduling strategy that does not affect semantic inputs.

Requires reviewed extension of the appropriate closed profile:

- a new Analysis family, model, experiment, observer, conclusion, refutation,
  semantic-read contract, or qualified outcome changes
  `FamilySemanticProfile` and normally `AnalysisSemanticRegime`;
- a theorem/rule schema, implication/transport/composition port, external
  statement/model correspondence adapter, or certificate semantic language
  changes `FamilyBasisRegistry`;
- a checker contract/ABI, decoder, proof-rule kernel, or validation trust-root
  policy changes `FamilyValidationProfile`;
- a capability, disclosure, unknown-question, persistence, or replay-consumer
  contract changes `FamilyOperationPolicy`;
- a transform intent or Compiler-local legality family changes its exact
  `TransformProblem` profile;
- candidate-domain or coverage semantics changes `CandidateDomainPolicy`;
  and
- a constraint, objective, qualification-resolution, comparator, tie, or
  report/decision policy changes `DecisionPolicy`.

Unknown semantic tags are `Unsupported`. Dynamic callbacks cannot acquire
authority from registration alone.

Every new or revised Analysis family closes its semantic profile, basis
registry, validation profile, and operation policy independently. A semantic
change to subjects, occurrences, maps, semantic reads, model, experiment,
observer, quantitative algebra, conclusion, or refutation changes
`AnalysisSemanticRegimeId` or `FamilySemanticProfileId`. Adding a theorem,
rule, proof lane, checker, capability policy, replay consumer, disclosure rule,
or trust policy changes only the exact basis, validation, operation, or replay
identity that reads it unless it also changes proposition meaning. Existing
identities are never reinterpreted.

Cross-version reuse requires an exact checked interpretation or transport
proposition. An external prover plugin may propose proof material, but it
cannot register a new family, rule, model, negative meaning, or capability cast
inside an existing regime.

## 18. Selected nonclaims and reversal triggers

The provisional target does not establish:

- truth of any cryptographic theorem or assumption;
- correctness of an external formalization or model correspondence;
- correctness, completeness, or formal verification of a checker;
- a proposition from an `AnalysisQuestion`, `AnalysisRequest`, theorem name,
  proof search attempt, or persisted record alone;
- a family-negative result when that family has no exact refutation or
  complete-decision schema;
- relation satisfaction without the Relations-owned operation;
- property preservation from structural relation alone;
- any property from `CheckedFSTheoremInstance` alone, or FS/composition
  property transport without exact property rules;
- property truth, consumer reliance, or a global verified state from
  `CheckedAnalysisCoverage`;
- acceptability of a residual trust root for a later consumer;
- global optimality beyond one exact candidate domain;
- `NoEligible` from incomplete search or assessment;
- endpoint feasibility, implementation correctness, runtime success, or
  release readiness;
- persistence of live authority; or
- implementation or migration feasibility.

Reconsider the federated target only if evidence shows one of the following:

1. a genuinely small universal logic covers every selected family without
   hiding model, observer, abort, adversary, resource, or negative semantics;
2. one external proof environment supplies every required native question with
   fully checked correspondence and acceptable replay stability;
3. a universal certificate architecture is simpler while keeping direct checks
   and unsupported families honest;
4. cross-family theorem reuse dominates family-local meaning enough that the
   profile boundary creates more ambiguity than it removes;
5. the five Compiler planes cannot express a real transform family without
   reintroducing producer authority or an uncheckable domain claim;
6. semantic candidate identity cannot be separated from proof basis for a
   required consumer, even with explicit assessed-support identity; or
7. the Stage 4B peer boundary demonstrates a concrete read-set contradiction
   that cannot be repaired by an exact later-owned input.

No such falsifier has yet been established. The model remains provisional
until the complete scenario and matrix program passes and independent
convergence review selects it.
