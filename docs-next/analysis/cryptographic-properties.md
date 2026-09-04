# Cryptographic property profiles

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative Analysis target
> **Target status:** One relation-bound Fresh premise and one classical-ROM
> Fresh-to-Fiat--Shamir transport profile
> **Provisional owner:** `analysis`
> **Authority:** This page defines a redesign target only. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> Admitting these schemas or passing a finite gate establishes no theorem truth,
> cryptographic security, concrete-hash security, or implementation support.

<!-- zkc-profile-source:analysis-property-semantics:start -->

## 1. Selection and research basis

This profile selects one exact theorem edge, not a generic rule that Fiat--Shamir
preserves every property:

```text
2-out-of-N special soundness of one exact three-move public-coin Fresh profile
  -> adaptive knowledge soundness of its exact Fiat--Shamir profile
     in the classical random-oracle model
```

The concrete theorem schema is pinned to the February 16, 2022 ePrint version 2
of Attema, Fehr, and Klooß,
[*Fiat--Shamir Transformation of Multi-Round Interactive
Proofs*](https://eprint.iacr.org/2021/1377.pdf). The exact artifact digest and
ordered locator tuple are owned once by `AFKV2SelectedSourceAuthority` in
Section 5; evaluators assert that record rather than restating it. The
corresponding published article is [Journal of Cryptology 36, article 36
(2023)](https://link.springer.com/article/10.1007/s00145-023-09478-y). A source
record for the journal revision must be formed separately with its own exact
locators. If the admitted theorem semantics are byte-for-byte unchanged, only
source validation and its consumers rotate; a semantic change requires a new
theorem schema and statement digest. Locators from two revisions cannot be
mixed inside one source record. The common
experiment architecture is also informed by Bellare and Rogaway's
[game-based treatment](https://web.cs.ucdavis.edu/~rogaway/papers/games.pdf),
the module/interface separation used by
[EasyCrypt](https://www.easycrypt.info/easycrypt-doc/refman.pdf), and the
state-separated package model in
[SSProve](https://eprint.iacr.org/2021/397.pdf).

Those sources motivate the selected definitions; their URLs, titles, or
locally admitted theorem records are not proof authority. Until a checked proof
is imported, the exact AFK theorem proposition remains an explicit hypothesis.

Property names are not subtypes. Special soundness, ordinary soundness,
round-by-round soundness, and knowledge soundness require explicit theorem
edges. The nonimplications and qualified implications studied in
[*On Soundness Notions for Interactive Oracle
Proofs*](https://eprint.iacr.org/2023/1256.pdf) are a reason to reject ambient
coercions. Classical ROM and QROM are likewise different experiment profiles;
[Unruh's QROM analysis](https://eprint.iacr.org/2017/398.pdf) cannot be selected
by changing a Boolean flag on the classical profile.

## 2. Closed experiment coordinates

Every active cryptographic question selects an exact
`AnalysisExperimentProfile` containing:

- an ordered quantifier prefix;
- an exact strategy/adversary ABI and allowed views;
- setup and the exact presence or absence of externally sampled Statement,
  auxiliary input, advice, and randomness distributions;
- verifier, public-coin, and oracle interfaces;
- scheduling and termination semantics;
- outcomes, failures, aborts, and the win event; and
- a typed resource basis.

An experiment name such as `ROM`, `adaptive`, or `Schnorr` is not an adequate
model identity. Wrong quantifier order, visibility, query API, randomness
ownership, failure treatment, or resource scope creates a different profile.

This page uses one compact convention for its long closed profiles:

```text
AnalysisCryptographicLawRef(P,body_schema,field_ordinal,signature) =
  the unique AnalysisProfileLawRef<signature> at that body-schema field in the
  exact direct profile P selected by that body's constructor case

AnalysisCryptographicLawTerm(P,body_schema,field_ordinal,arguments) =
  AnalysisLawTerm whose law_ref is the corresponding
  AnalysisCryptographicLawRef and whose canonical_arguments are arguments
```

In a body display below, a mathematical formula or English expansion in a
law-, schema-, predicate-, denotation-, schedule-, event-, failure-, resource-,
map-, transform-, or conclusion-valued field denotes that exact profile ref or
term at the field's written ordinal. The profile argument may be omitted in a
later display only after the named concrete constructor and its authenticated
predecessors have fixed one direct profile. The expansion is reader-facing and
is not encoded. Coordinate, ID, enum, natural, canonical value, sequence, map,
and record fields remain the literal typed values displayed. The selected
profile law source fixes every ref's full signature and exact law bytes; an
absent, duplicate, wrong-profile, or wrong-signature ref is malformed. Thus no
sentence, citation text, display label, or runtime provider supplies an
identity field.

A concrete bounded Schnorr/property constructor whose complete predecessor
closure is property-owned uses `AnalysisCryptographicPropertyLanguageProfileId`.
Every concrete asymptotic-family constructor that defines `F`, an
`F`-dependent experiment or theorem subject, or an AFK abstract-family
language declaration uses `AnalysisAFKTransportLanguageProfileId`; this includes
the all-`n` source-property result rather than creating a property-to-transport
back-edge. The one selected ownership exception is
`analysis.challenge-domain`: it is a property-owned finite projection from the
exact challenge coordinates in one authenticated concrete subject tuple, not
an `F`-parametric experiment, theorem, or transport constructor. Its body
retains those owner coordinates and the Analysis-owned finite model; it
contains no transport-family ID. The property profile neither imports
transport declarations nor restates family semantics. A theorem-source
validation body,
or an AFK support/validation/operation-policy/judgment body that consumes or
governs one, uses
`AnalysisAFKTheoremSourceValidationLanguageProfileId`. This is a total named-
constructor classification with that one enumerated boundary case, not an open
default: a concrete body not admitted by exactly one authenticated constructor
case is malformed. Each profile reaches the common kernel through its exact
import chain, but none copies upstream catalogs or resolves a declaration by a
family/revision label.

### 2.1 Exact property-family contracts

The active family catalog is finite. Direct profile ownership is exactly:

```text
AnalysisCryptographicPropertyFamilyCoordinates = CanonicalSeq [
  KOutOfNSpecialSoundness,
  FixedExtractorUniversalCorrectness,
  AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  ChallengeDomainCorrespondence,
  AcceptanceRelationCorrespondence,
  AlgebraAndCanonicalEncodingLaws,
  PolynomialTimeRelationMembership,
  PolynomialTimeSourceVerifier,
  PolynomialTimeExtractor
]

AnalysisAFKTransportFamilyCoordinates = CanonicalSeq [
  AsymptoticKOutOfNSpecialSoundness,
  AdaptiveKnowledgeSoundnessQltN,
  TheoremTruth,
  TheoremApplicability,
  FamilyInstanceCorrespondence,
  TotalSingleValuedFamilyDenotation,
  FamilyProjectionCoherence,
  UniformPrimeOrderSchnorrFamily,
  UniformPolynomialTimeRelationMembership,
  UniformPolynomialTimeVerifier,
  FreshUniformIndependentPublicCoin,
  ExactClassicalRandomOracleProcess,
  FixedPublicSetupIndependence,
  TotalUniformChallengeSamplerAdequacy,
  FixedFamilyChallengeCardinality,
  FiniteBoundedRandomOracleIndexAndEfficientOperations,
  AFKExperimentObservationCorrespondence,
  FamilyDenotationAtIndex,
  FamilyProjectionAtIndex,
  FamilyInstanceRoleMapAdequacy,
  FamilyInstanceQuantitativeNormalizationAdequacy,
  FamilyInstanceProcessCorrespondence
]

AnalysisCryptographicBranchFamilyCoordinates =
  CanonicalAppend(
    AnalysisCryptographicPropertyFamilyCoordinates,
    AnalysisAFKTransportFamilyCoordinates)
```

The two sequences are duplicate-free and their union is exactly the
cryptographic/AFK branch-owned subset of the active family set listed in
`analysis-model.md`. The incremental-composition coordinates belong to the
independent profiles defined in
[Incremental Composition](incremental-composition.md) and are not members of
this union. An omitted, extra, or multiply owned coordinate within these two
sequences refuses the corresponding branch profile. For a coordinate `f`, let
`OwnerProfile(f)` be the property profile for the first sequence and the
semantic transport profile for the second. The following names are exact
declaration/law refs in that profile, indexed by the complete coordinate rather
than its spelling:

```text
AnalysisFamilySubjectSchemaRef(f) =
  AnalysisProfileLawRef<ClosedFamilySubjectSchema> for exactly f
AnalysisFamilyQuestionPayloadSchemaRef(f) =
  AnalysisProfileLawRef<ClosedFamilyQuestionPayloadSchema> for exactly f
AnalysisFamilyConclusionSchemaRef(f) =
  AnalysisProfileLawRef<ClosedFamilyConclusionSchema> for exactly f
AnalysisFamilyQuestionToConclusionLaw(f) =
  AnalysisLawTerm<TotalQuestionToConclusionReconstruction> for exactly f
AnalysisFamilyPolarityMeaningRef(f) =
  AnalysisProfileLawRef<FamilyPolarityMeaning> for exactly f
AnalysisFamilyFailurePartitionRef(f) =
  CommonAnalysisAttemptFailurePartitionRef<OwnerProfile(f)>
AnalysisNoQuantitativeResultSchemaRef(f) =
  AnalysisProfileLawRef<ClosedFamilyQuantitativeResultSchema> admitting
  exactly NoQuantitativeResult for f
AnalysisAdaptiveFormulaTripleResultSchemaRef(f) =
  AnalysisProfileLawRef<ClosedFamilyQuantitativeResultSchema> admitting
  exactly the ordered error/success/expected-call formula-ID triple selected
  by f, with the exact dependent sorts fixed by that family's payload
```

The allowed context sequence is the following total case split:

```text
AnalysisFamilyAllowedContexts(f) =
  [SemanticExperimentContext] when f is in
    AnalysisCryptographicPropertyFamilyCoordinates;
  [FamilySemanticExperimentContext] when f is one of
    AsymptoticKOutOfNSpecialSoundness,
    AdaptiveKnowledgeSoundnessQltN,
    TotalSingleValuedFamilyDenotation,
    FamilyProjectionCoherence,
    UniformPrimeOrderSchnorrFamily,
    UniformPolynomialTimeRelationMembership,
    UniformPolynomialTimeVerifier,
    FreshUniformIndependentPublicCoin,
    ExactClassicalRandomOracleProcess,
    FixedPublicSetupIndependence,
    TotalUniformChallengeSamplerAdequacy,
    FixedFamilyChallengeCardinality,
    FiniteBoundedRandomOracleIndexAndEfficientOperations,
    AFKExperimentObservationCorrespondence;
  [SourceFree(TheoremTruthSourceFreeReasonRef)] when f is TheoremTruth;
  [SemanticExperimentContext,FamilySemanticExperimentContext]
    when f is TheoremApplicability;
  [FamilyInstanceContext] when f is one of
    FamilyInstanceCorrespondence,
    FamilyDenotationAtIndex,
    FamilyProjectionAtIndex,
    FamilyInstanceRoleMapAdequacy,
    FamilyInstanceQuantitativeNormalizationAdequacy,
    FamilyInstanceProcessCorrespondence;
  undefined otherwise

AnalysisFamilyQuantitativeResultSchema(f) =
  AnalysisAdaptiveFormulaTripleResultSchemaRef(f) when f is
    AdaptiveKnowledgeExtractionAtFixedLengthQltN or
    AdaptiveKnowledgeSoundnessQltN;
  AnalysisNoQuantitativeResultSchemaRef(f) for every other active f;
  undefined otherwise

FixedExtractorFiniteCoverDischargeContract = {
  exact_cover_schema:
    AnalysisProfileLawRef<"finite-cover-cover-schema-v0">,
  exact_candidate_algorithm_schema:
    AnalysisProfileLawRef<"finite-cover-candidate-schema-v0">,
  exact_representative_success_schema:
    AnalysisProfileLawRef<"finite-cover-success-schema-v0">,
  exact_coverage_certificate_schema:
    AnalysisProfileLawRef<"finite-cover-coverage-certificate-v0">,
  exact_quotient_factorization_certificate_schema:
    AnalysisProfileLawRef<"finite-cover-factorization-certificate-v0">,
  exact_success_transfer_certificate_schema:
    AnalysisProfileLawRef<"finite-cover-transfer-certificate-v0">,
  finite_cover_target_reconstruction_law:
    AnalysisLawTerm<"finite-cover-target-reconstruction-v0">,
  operation_checker_binding_admission_law:
    AnalysisLawTerm<"finite-cover-operation-binding-v0">,
  deterministic_stream_progress_law:
    AnalysisLawTerm<"finite-cover-stream-progress-v0">
}

ActiveFamilyFiniteCoverDischargeContract(f) =
  FixedExtractorFiniteCoverDischargeContract
    when f is FixedExtractorUniversalCorrectness;
  None for every other active f;
  undefined otherwise

AnalysisFamilySemanticsContractFor(f) =
  AnalysisFamilySemanticsContract<OwnerProfile(f)> {
  exact_subject_schema: AnalysisFamilySubjectSchemaRef(f),
  exact_question_payload_meta_schema:
    AnalysisFamilyQuestionPayloadSchemaRef(f),
  exact_hypothesis_free_conclusion_meta_schema:
    AnalysisFamilyConclusionSchemaRef(f),
  question_to_conclusion_reconstruction_law:
    AnalysisFamilyQuestionToConclusionLaw(f),
  allowed_question_context_variants: AnalysisFamilyAllowedContexts(f),
  exact_quantitative_result_schema:
    AnalysisFamilyQuantitativeResultSchema(f),
  affirmative_and_negative_meaning: AnalysisFamilyPolarityMeaningRef(f),
  finite_cover_discharge_contract:
    ActiveFamilyFiniteCoverDischargeContract(f),
  failure_classification: AnalysisFamilyFailurePartitionRef(f)
}

AnalysisFamilyContractCatalog(P) =
  CanonicalKeySortedMap {
    f -> AnalysisFamilySemanticsContractFor(f)
    for every f in AnalysisActiveFamilyCoordinates with OwnerProfile(f) = P
  }
```

The property profile enables checked finite-cover discharge for exactly
`FixedExtractorUniversalCorrectness`. The row publishes the exact
subject-parametric target reconstruction, three pairwise-distinct certificate
schemas, operation-binding law, and deterministic-stream law. Every other
active family retains `None`; in particular the finite result cannot discharge
`KOutOfNSpecialSoundness`, an asymptotic family, or a security experiment. An
unprofiled enumeration cannot add or widen this authenticated contract.

For `TheoremTruth` and `TheoremApplicability`, the two expanded rows in
`transport-composition-and-replay.md` must be byte-identical to the result of
this constructor; they are explanations, not duplicate contracts. For every
other family, the exact profile law source contains the indexed schema and law
refs above. Admission requires the catalog key set to equal the owning family
sequence exactly and verifies every question body against its one row. Host
code, a display family name, or a future family cannot add another case.

## 3. Relation-bound Fresh special soundness

All active nominal constructors below are parameterized by one exact subject
tuple; a bare display label is never an ID:

```text
AnalysisSubjectTuple S = {
  fresh_protocol_id,
  fiat_shamir_protocol_id,
  shared_core_id,
  transcript_construction_id,
  checked_fs_construction_result_ref,
  relation_definition_id,
  relation_semantic_model_id,
  relation_interface_id,
  relation_instance_id,
  fresh_prover_plan_id: ProverPlanId,
  relation_axis_ingress: {
    fresh: {
      protocol_relation_binding_id,
      plan_witness_binding_id,
      statement_correspondence_question_id_and_StatementEdgeRef,
      claim_correspondence_question_id_and_ClaimMeaningRef,
      witness_correspondence_question_id_and_PlanWitnessEdgeRef,
      grounding_equation_id,
      equation_grounding_question_id
    },
    fiat_shamir: {
      protocol_relation_binding_id,
      plan_witness_binding_id,
      statement_correspondence_question_id_and_StatementEdgeRef,
      claim_correspondence_question_id_and_ClaimMeaningRef,
      witness_correspondence_question_id_and_PlanWitnessEdgeRef,
      grounding_equation_id,
      equation_grounding_question_id
    }
  },
  core_check_ref,
  core_accept_terminal_ref,
  challenge_ref,
  challenge_value_type,
  analysis_challenge_values:
    CanonicalNonEmptySortedUniqueSeq<CanonicalValue<challenge_value_type>>,
  public_setup_invocation_views: {
    fresh: PublicSetupInvocationViewId,
    fiat_shamir: PublicSetupInvocationViewId
  },
  fixed_setup_static_sources: {
    relation_group_parameter_fields:
      CanonicalNonEmptySortedUniqueSeq<ConcreteOwnerField(
        OwnerFieldCoordinate<Relations,RelationDefinitionBody>)>,
    transcript_application_domain_field:
      PIRStaticViewFieldCoordinate<TranscriptDeclarationViewBody>
  }
}

AnalysisRelationAxisIngressAdequacyEvaluatorId,
AnalysisFreshFsRelationShapeAdequacyEvaluatorId, and
AnalysisFixedSetupStaticSourcesAdequacyEvaluatorId
  = three pairwise-distinct exact `AnalysisAdequacyEvaluatorId` values in
    `AnalysisCryptographicPropertyLanguageProfileId`; their closed input schemas are
    respectively one complete axis-ingress record plus its Protocol, the two
    complete admitted axis records, and the complete static-source record plus
    its authenticated owner bodies

AnalysisRelationAxisIngressWellFormed(S,axis) iff
  AnalysisRelationAxisIngressAdequacyEvaluatorId returns Success(true) and
  the selected ProtocolRelationBinding names the ProtocolId for axis,
  the selected PlanWitnessBinding names a Plan Witness surface for that same
    Protocol,
  every Statement, claim, Witness, and EquationGrounding question names the
    exact selected binding, Plan binding, equation, and owner ref for axis,
  every selected affirmative owner binding answers that exact question,
  the grounding equation's Protocol run slots name that same Protocol, and,
  for the fresh axis, S.fresh_prover_plan_id names the Plan whose checked
  realization and checked witness-surface extraction produced the surface
  the selected PlanWitnessBinding names

AnalysisFreshFsRelationShapeAgrees(S) iff
  AnalysisFreshFsRelationShapeAdequacyEvaluatorId returns Success(true) and
  replacing only S.relation_axis_ingress.fiat_shamir's ProtocolId-qualified
  owner coordinates with their Fresh-axis counterparts yields the exact Fresh
  binding, Plan surface, occurrence-edge, claim, Witness, and grounding shapes
  under the Relations-owned comparison law

AnalysisFixedSetupStaticSourcesWellFormed(S) iff
  AnalysisFixedSetupStaticSourcesAdequacyEvaluatorId returns Success(true) and
  every relation_group_parameter_fields entry names S.relation_definition_id
    and is exactly one owner-schema leaf used by the selected group law, and
  transcript_application_domain_field is exactly the application_domain leaf
    below ConstructionView(S.transcript_construction_id,
                           CanonicalFramedConstructionViewKindRef(
                             TranscriptDeclarationView))

AnalysisRelationAxisIngressInput = {
  subject: AnalysisSubjectTuple,
  axis: Fresh | FiatShamir
}

AnalysisFreshFsRelationShapeInput = {subject: AnalysisSubjectTuple}

AnalysisFixedSetupStaticSourcesInput = {subject: AnalysisSubjectTuple}

AnalysisRelationAxisIngressAdequacyEvaluatorId =
  the exact `AnalysisAdequacyEvaluatorId<AnalysisRelationAxisIngressInput>` in
  AnalysisCryptographicPropertyLanguageProfileId

AnalysisFreshFsRelationShapeAdequacyEvaluatorId =
  the distinct exact `AnalysisAdequacyEvaluatorId<
    AnalysisFreshFsRelationShapeInput>` in that same profile

AnalysisFixedSetupStaticSourcesAdequacyEvaluatorId =
  the distinct exact `AnalysisAdequacyEvaluatorId<
    AnalysisFixedSetupStaticSourcesInput>` in that same profile

Each of the three bodies names the exact no-extra supported input profiles
reached from the property profile's authenticated Relations/PIR import closure, the
complete owner field-coordinate schema it reads, a portable checker and
evaluation contract, exact direct module roots, `Success(true)` as its sole
affirmative value, and the exact
`CryptographicPropertyAttemptFailurePartitionRef`. Their complete declaration
coordinates and bodies are pairwise distinct.

The bounded Analysis executable currently reuses the smaller generic property-
profile adequacy surrogate described in the Analysis model. It does not yet
encode these three pairwise-distinct evaluator declarations or derive their
complete owner-profile sets. Its finite checks therefore do not establish this
target catalog or its no-extra input-profile rule.

AnalysisStatementType(S) =
  the one ValueType whose equality is checked across the selected PIR Statement
  BindingRef, exact StatementEdgeRef target, and selected relation public slot

AnalysisWitnessType(S) =
  the one ValueType whose equality is checked across the selected Plan Witness
  surface, exact PlanWitnessEdgeRef target, and selected relation Witness slot

AnalysisCommitmentType(S) =
  the one ValueType of the unique prover Message occurrence preceding the
  selected Fresh challenge whose output is the profile-declared first-message
  input in the exact selected Check dependency closure

AnalysisResponseType(S) =
  the one ValueType of the unique prover Message occurrence following the
  selected Fresh challenge whose output is the profile-declared response input
  in that same exact Check dependency closure

AFKProofType(S) = CanonicalRecord<
  the exact ordered prover-controlled FS proof-occurrence projections consumed
  by the selected FS verifier, excluding the Statement and auxiliary output,
  with each field carrying its owner PIR ValueType and occurrence coordinate>

AnalysisChallengeRefCoordinate(S) =
  the unique element of ExactPIRAtomicLeavesUnder(
    AnalysisOwnerViewCoordinate(S,PublicCoinView),
    [challenges[S.challenge_ref].challenge_ref])

AnalysisChallengeNominalDomainCoordinate(S) =
  the unique element of ExactPIRAtomicLeavesUnder(
    AnalysisOwnerViewCoordinate(S,PublicCoinView),
    [challenges[S.challenge_ref].domain])

AnalysisChallengeFreshLawCoordinate(S) =
  the unique element of ExactPIRAtomicLeavesUnder(
    AnalysisOwnerViewCoordinate(S,PublicCoinView),
    [challenges[S.challenge_ref].fresh_law])

SchnorrFreshLawRef(S) =
  the value of the leaf AnalysisChallengeFreshLawCoordinate(S) selects in
  the authenticated PublicCoinView, an exact
  ProtocolDeclarationRef<"pir.public-coin-law"> that the PIR owner placed on
  the challenge entry; no other projection or inference supplies it

The displayed paths above are aliases for the profile-fixed ordinal paths.
All three results are exact `PIRStaticViewFieldCoordinate` values and
therefore carry the owning `CoreId` through the `PublicCoinView` coordinate.
Formation also requires the three leaves to belong to the same challenge
entry selected by `S.challenge_ref`.

AnalysisChallengeDomainBody(S) = {
  source_challenge_coordinate: AnalysisChallengeRefCoordinate(S),
  value_type: S.challenge_value_type,
  source_nominal_domain_coordinate: AnalysisChallengeNominalDomainCoordinate(S),
  model_values: S.analysis_challenge_values,
  adequacy_evaluator_id: AnalysisChallengeDomainAdequacyEvaluatorId,
  semantic_status:
    AnalysisChallengeSemanticStatus.FiniteModelRequiringOrdinaryOwnerCorrespondence
}

AnalysisChallengeSemanticStatus =
  FiniteModelRequiringOrdinaryOwnerCorrespondence

AnalysisChallengeDomainInput = {
  source_challenge_coordinate: PIRStaticViewFieldCoordinate,
  value_type: ValueType,
  source_nominal_domain_coordinate: PIRStaticViewFieldCoordinate,
  model_values: CanonicalNonEmptySeq<CanonicalValue<value_type>>,
  semantic_status: exactly
    AnalysisChallengeSemanticStatus.FiniteModelRequiringOrdinaryOwnerCorrespondence
}

AnalysisChallengeDomainAdequacyEvaluatorId =
  the exact AnalysisAdequacyEvaluatorId<AnalysisChallengeDomainInput> in the selected
  cryptographic profile; it authenticates both coordinates, checks that they
  select the `challenge_ref` and `domain` leaves of one entry under the exact
  owner `PublicCoinView`, checks that the entry's value type equals
  `value_type`, and checks canonical member representations, exact sorted
  uniqueness, ModelCardinality equal to sequence length, Foundation-bounded
  totality, and cardinality at least 2

AnalysisChallengeDomainId(S) =
  AnalysisId<"analysis.challenge-domain">(B, AnalysisChallengeDomainBody(S))

AuthenticatedChallengeModelValues(S) =
  authenticate AnalysisChallengeDomainId(S), require its exact body to equal
  AnalysisChallengeDomainBody(S), and return that body's canonical `model_values`

AFKFixedPublicSetupBody(S) = {
  exact_static_sources: [S.shared_core_id, S.transcript_construction_id,
                         AnalysisChallengeRefCoordinate(S),
                         S.fixed_setup_static_sources],
  exact_public_invocation_sources: S.public_setup_invocation_views,
  derived_projection:
    AnalysisLawTerm<AFKFixedPublicSetupProjection> that first requires both
    views' `run_established` sequences to be empty, then the Fresh and
    Fiat--Shamir `PublicSetupInvocationViewBody.entries` to be byte-identical,
    and then combines that common entry sequence with the
    CoreHeader, ConstructionHeader,
    ApplicationDomainHeader, scope/opening frames, public-parameter frames,
    challenge-condition framing schema, prefix-construction function, and
    ChallengeNamespace schema from those owner sources under the PIR
    construction law; the concrete DerivedPrefix additionally takes the later
    prover outputs Y and A and is not fixed setup,
  required_selection_schedule:
    AnalysisProfileLawRef<PreProverAndOracleFixedSelectionSchedule>,
  visibility_map:
    AnalysisLawTerm<CoordinateByCoordinatePublicVisibilityMap>
}

AFKFixedPublicSetupId(S) =
  AnalysisId<"analysis.fixed-public-setup">(B, AFKFixedPublicSetupBody(S))
```

Every leaf other than `analysis_challenge_values` is a typed owner semantic
coordinate or an exact owner-declared field projection; `relation_axis_ingress`,
`public_setup_invocation_views`, and `fixed_setup_static_sources` are closed
grouping records only. The
finite challenge-value sequence is an Analysis-owned model coordinate bound by
`AnalysisChallengeDomainId(S)`; formation proves only its canonical finite shape.
An ordinary hypothesis must relate the owner-qualified nominal-domain
coordinate and value type to that model. The separate AFK applicability
hypotheses relate the exact owner projections rooted at the sibling
`fresh_law`, `correlation`, prior-member, and `public_conditions` fields of
`challenges[S.challenge_ref]` in the authenticated `PublicCoinView` to the
required uniform process. They are not children or projections of the atomic
`AnalysisChallengeRefCoordinate(S)`. No nominal fresh-law
coordinate is inferred from the challenge-domain model. The
fixed-setup body and ID are an Analysis-owned exact projection of their listed
static owner coordinates and the two PIR-issued
`PublicSetupInvocationViewId` values; they do not copy caller-authored invocation
assignments, derived headers, or owner facts. Ordinary
applicability hypotheses establish its visibility, fixedness, and independence.
Formation authenticates both entries of `S.public_setup_invocation_views`
against their exact `PublicSetupInvocationViewBody` values. Both views'
`run_established` sequences must be empty: a fixed setup is one the
invocation determines entirely, so a view naming a run-established
`SessionContext` or `PublicParameter` binding (the Interaction page's Section
13.4) cannot form this fixed-setup ID, and no assignment is copied in its
place; that emptiness is this formation's own premise, not an owner fact. Their Protocol IDs
must equal `S.fresh_protocol_id` and `S.fiat_shamir_protocol_id` respectively;
both Core IDs must equal `S.shared_core_id`; and both entry sequences must be
byte-identical and contain exactly every `PublicParameter` and `SessionContext`
binding in owner `BindingRef` order. The views exclude Statement, Witness,
prover-private, and verifier-private assignments by owner construction. Each
matching `ExactPublicSetupInvocationViewAuthorityBinding` belongs to source
support and each fresh `PublicSetupInvocationViewCapability` belongs only to
the checking invocation. A copied assignment sequence, unequal Fresh/FS setup,
a subset of public bindings, or a view from another Core/Protocol is malformed
or refused and cannot form this fixed-setup ID.
Formation also evaluates `AnalysisFixedSetupStaticSourcesWellFormed`; a display
label, free path, interior subtree, field under another relation definition or
construction, or copied parameter value cannot occupy either static-source
field. Formation requires the two Protocols to name `shared_core_id`, both
relation-axis ingress records to satisfy their exact owner checks, and the
exact transcript construction and checked-result ref to name those Fresh/FS
subjects. The selected Fresh Statement edge for this exact property lane must
use `SameExactType`; a bridged or lossy Statement representation requires a
different property profile with its own quantified Statement carrier. The
selected terminal must have verdict `Accept`, must list `core_check_ref` in
`required_true_checks`, and both refs must have their unique PIR occurrence
backlinks. Each selected axis correspondence question must have its declared
tag and exact binding, Plan-binding, owner-ref, or grounding-equation operand.
`AnalysisChallengeDomainBody(S)` formation additionally rejects cardinality below
`2`; an empty pair domain cannot inhabit `KOutOfNSpecialSoundness(k = 2)`.
PIR consumes the concrete `CheckedFSConstruction` result binding and fresh
capability when it issues `FSConstructionView`. Analysis support retains only
the resulting exact view binding, and its invocation receives only the matching
view capability; no `CheckedFSConstructionId` exists and the consumed owner
capability is not forwarded. Replacing, omitting, or reordering a field changes
or malforms every dependent manifest, question, or derived setup/domain ID. In
the remaining displays, a bare
`...Id` whose body depends on subjects means `...Id(S)` under an explicitly
bound `S`; use outside that scope is malformed.

Owner-qualified view coordinates are derived, never supplied:

```text
AnalysisOwnerViewCoordinate(S, PublicBindingView) =
  CoreView(S.shared_core_id,PublicBindingView)
AnalysisOwnerViewCoordinate(S, StrategyDecisionView | PublicCoinView | EffectView |
                           ClaimReductionView) =
  CoreView(S.shared_core_id,the selected view kind)
AnalysisOwnerViewCoordinate(S, FreshExecutionView) =
  ProtocolView(S.fresh_protocol_id,ExecutionView)
AnalysisOwnerViewCoordinate(S, FiatShamirExecutionView) =
  ProtocolView(S.fiat_shamir_protocol_id,ExecutionView)
AnalysisOwnerViewCoordinate(S, TranscriptDeclarationView | RequiredInfluenceView |
                           ChallengeTransitionView) =
  ConstructionView(
    S.transcript_construction_id,
    CanonicalFramedConstructionViewKindRef(the selected construction-view kind))
AnalysisOwnerViewCoordinate(S, FSConstructionView) =
  FSResultView(
    S.checked_fs_construction_result_ref,
    CanonicalFramedFSResultViewKindRef)

AnalysisPublicSetupInvocationCoordinate(S,Fresh) =
  PublicSetupInvocationViewCoordinate(
    S.fresh_protocol_id,S.public_setup_invocation_views.fresh)
AnalysisPublicSetupInvocationCoordinate(S,FiatShamir) =
  PublicSetupInvocationViewCoordinate(
    S.fiat_shamir_protocol_id,S.public_setup_invocation_views.fiat_shamir)

SchnorrRelationSubjectProjection(S) = CanonicalSeq [
  S.fresh_protocol_id,
  S.shared_core_id,
  S.public_setup_invocation_views.fresh,
  S.relation_definition_id,
  S.relation_semantic_model_id,
  S.relation_interface_id,
  S.relation_instance_id,
  S.relation_axis_ingress.fresh.protocol_relation_binding_id,
  S.relation_axis_ingress.fresh.plan_witness_binding_id,
  QuestionIdOf(
    S.relation_axis_ingress.fresh.
      statement_correspondence_question_id_and_StatementEdgeRef),
  QuestionIdOf(
    S.relation_axis_ingress.fresh.
      claim_correspondence_question_id_and_ClaimMeaningRef),
  QuestionIdOf(
    S.relation_axis_ingress.fresh.
      witness_correspondence_question_id_and_PlanWitnessEdgeRef),
  S.relation_axis_ingress.fresh.grounding_equation_id,
  S.relation_axis_ingress.fresh.equation_grounding_question_id
]

AFKTargetSubjectProjection(S) = CanonicalSeq [
  every entry of SchnorrRelationSubjectProjection(S) in the same order,
  S.fiat_shamir_protocol_id,
  S.transcript_construction_id,
  S.public_setup_invocation_views.fiat_shamir,
  S.relation_axis_ingress.fiat_shamir.protocol_relation_binding_id,
  S.relation_axis_ingress.fiat_shamir.plan_witness_binding_id,
  QuestionIdOf(
    S.relation_axis_ingress.fiat_shamir.
      statement_correspondence_question_id_and_StatementEdgeRef),
  QuestionIdOf(
    S.relation_axis_ingress.fiat_shamir.
      claim_correspondence_question_id_and_ClaimMeaningRef),
  QuestionIdOf(
    S.relation_axis_ingress.fiat_shamir.
      witness_correspondence_question_id_and_PlanWitnessEdgeRef),
  S.relation_axis_ingress.fiat_shamir.grounding_equation_id,
  S.relation_axis_ingress.fiat_shamir.equation_grounding_question_id,
  AFKFixedPublicSetupId(S)
]
```

The two projections above are exact typed-semantic-subject constructors, not
prose set comprehensions. Their displayed field order is their identity order;
`QuestionIdOf` accepts only the declared pair carrier and returns its exact
owner question ID. Check/terminal/challenge refs and result-schema coordinates
remain selected fields of the identified Core or construction sources and are
not smuggled into `exact_subjects` as non-ID values. A missing field, a
different order, or an additional subject is malformed.

Subject formation evaluates `AnalysisRelationAxisIngressWellFormed` for both axes
and `AnalysisFreshFsRelationShapeAgrees`. The latter consumes the producer's exact
checked comparison; it does not make the two Protocol-qualified IDs equal.
Consequently the Fresh source identity contains only the Fresh axis, while the
AFK target identity contains both bindings, both Plan surfaces, both exact
correspondence sets, and both grounding coordinates. Replacing the
Fiat--Shamir binding with a same-Core Fresh binding is malformed even when all
unqualified occurrence shapes coincide.

The active slot catalogs use these exact ordered field projections:

```text
AnalysisFamilyRoleKindRef(name,signature_class) =
  the one exact AnalysisProfileDeclarationRef<"analysis.family-role-kind"> whose
  resolved body is AnalysisFamilyRoleKindDeclarationBody {
    name: MetaSymbol(name), signature_class
  }

SchnorrRelationSpecialSoundnessSource,
AFKAdaptiveFreshFsSource,
AFKAbstractFreshFamilySource, and
AFKAbstractFreshFsFamilySource
  = four pairwise-distinct exact declarations under
    AnalysisSourceFamilyCoordinate

Their complete declaration bodies and the exact active source-family catalog
are formed after the concrete and abstract slot catalogs below; these four
names alone are not admissible coordinates.

AnalysisPIRSourceSlot(view_kind,coordinate_schema,field_projection,purpose,
                 adequacy_evaluator_id,binding_schema,
                 required_authority_class) =
  ConcreteOwnerReadSlotSchema(
    PIR,view_kind,
    DependentForAll([subject : AnalysisSubjectTuple],coordinate_schema),purpose,
    field_projection,adequacy_evaluator_id,binding_schema,
    required_authority_class,
    CryptographicPropertyAttemptFailurePartitionRef)

AnalysisStaticViewFields(subject,view_kind,subtree_paths) =
  RequiredPIRViewReadClosure(
    AnalysisOwnerViewCoordinate(subject,view_kind),
    ExactPIRAtomicLeavesUnder(
      AnalysisOwnerViewCoordinate(subject,view_kind),subtree_paths))

AnalysisExecutionViewFields(subject,axis,subtree_paths) =
  RequiredPIRViewReadClosure(
    AnalysisOwnerViewCoordinate(subject,axis),
    ExactPIRAtomicLeavesUnder(
      AnalysisOwnerViewCoordinate(subject,axis),subtree_paths))

ExactPIRAtomicLeavesUnder(coordinate,subtree_paths) =
  the canonical sorted-unique sequence of every atomic
  `PIRStaticViewFieldCoordinate` below the exact ordinal subtree paths selected
  from the closed owner schema for coordinate; each displayed field name below
  is the owner body's own field name at the selected depth and denotes the
  ordinal path of that field in the closed owner schema, so a name the owner
  body does not declare selects nothing and the read is malformed under the
  field-projection law of `analysis-model.md` Section 2.1; the names do not
  enter a body

AnalysisPublicBindingAdequacy,
AnalysisFreshPublicSetupInvocationAdequacy,
AnalysisFiatShamirPublicSetupInvocationAdequacy,
AnalysisStrategyDecisionAdequacy,
AnalysisPublicCoinAdequacy,
AnalysisAcceptanceEffectAdequacy,
AnalysisClaimReductionAdequacy,
AnalysisFreshExecutionBoundaryAdequacy,
AnalysisFiatShamirExecutionBoundaryAdequacy,
AnalysisTranscriptDeclarationAdequacy,
AnalysisRequiredInfluenceAdequacy,
AnalysisChallengeTransitionAdequacy,
AnalysisFSConstructionAdequacy
  = pairwise-distinct exact AnalysisAdequacyEvaluatorId values in
    `AnalysisCryptographicPropertyLanguageProfileId`, each with the complete typed
    input schema implied by its slot below and the exact no-extra
    `supported_input_profile_ids` consisting of
    `AnalysisCryptographicPropertyLanguageProfileId` plus the owner profile selected
    by that slot

The bounded Analysis executable currently represents this list through generic
profile-level evaluator-schema rows and singleton Analysis-profile input sets.
It exercises the listed owner reads through host-side checks, but does not yet
authenticate one distinct evaluator body and the exact Analysis-plus-owner
profile set for every slot. Passing that instrument is not evidence for the
stronger evaluator identity and input-closure claims above.

CryptographicPropertyAttemptFailurePartitionRef =
  CommonAnalysisAttemptFailurePartitionRef<
    AnalysisCryptographicPropertyLanguageProfileId>

AnalysisPIRFreshSourceSlotFragment = CanonicalSeq [
  AnalysisPIRSourceSlot(PublicBindingView,
    AnalysisOwnerViewCoordinate(subject,PublicBindingView),
    AnalysisStaticViewFields(subject,PublicBindingView,
      [scopes,bindings]),SemanticMeaning,
    AnalysisPublicBindingAdequacy,
    ExactPIRStaticViewAuthorityBinding<PublicBindingView>,FreshSourceCapability),
  ConcreteOwnerReadSlotSchema(
    PIR,PublicSetupInvocationView,
    DependentForAll([subject : AnalysisSubjectTuple],
      AnalysisPublicSetupInvocationCoordinate(subject,Fresh)),OccurrenceEvidence,
    CompleteOwnerBodyProjection(PublicSetupInvocationViewBody),
    AnalysisFreshPublicSetupInvocationAdequacy,
    ExactPublicSetupInvocationViewAuthorityBinding,FreshSourceCapability,
    CryptographicPropertyAttemptFailurePartitionRef),
  AnalysisPIRSourceSlot(StrategyDecisionView,
    AnalysisOwnerViewCoordinate(subject,StrategyDecisionView),
    AnalysisStaticViewFields(subject,StrategyDecisionView,
      [decision_points,prover_view_formation_law,guaranteed_prover_reads,
       legal_move_types]),SemanticMeaning,
    AnalysisStrategyDecisionAdequacy,
    ExactPIRStaticViewAuthorityBinding<StrategyDecisionView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(PublicCoinView,
    AnalysisOwnerViewCoordinate(subject,PublicCoinView),
    AnalysisStaticViewFields(subject,PublicCoinView,
      [structural_public_coin_eligibility,
       verifier_private_predecessors,challenges]),SemanticMeaning,
    AnalysisPublicCoinAdequacy,
    ExactPIRStaticViewAuthorityBinding<PublicCoinView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(EffectView,
    AnalysisOwnerViewCoordinate(subject,EffectView),
    AnalysisAcceptanceProducerProjection(subject),SemanticMeaning,
    AnalysisAcceptanceEffectAdequacy,
    ExactPIRStaticViewAuthorityBinding<EffectView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(ClaimReductionView,
    AnalysisOwnerViewCoordinate(subject,ClaimReductionView),
    AnalysisStaticViewFields(subject,ClaimReductionView,
      [claims,reductions,terminal_dispositions]),
    SemanticMeaning,AnalysisClaimReductionAdequacy,
    ExactPIRStaticViewAuthorityBinding<ClaimReductionView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(ExecutionView,
    AnalysisOwnerViewCoordinate(subject,FreshExecutionView),
    AnalysisExecutionViewFields(subject,FreshExecutionView,
      [protocol_id,core_id,challenge_interpretation,visible_history_law,
       resolver_coordinates,generated_execution_law,run_record_schema,
       replay_qualification_law,relation_run_view_issuance_law]),
    SemanticMeaning,AnalysisFreshExecutionBoundaryAdequacy,
    ExactPIRStaticViewAuthorityBinding<ExecutionView>,FreshSourceCapability)
]

SchnorrSourceSlotCatalog = CanonicalConcat(
  AnalysisPIRFreshSourceSlotFragment,
  AnalysisSharedRelationsSourceSlotFragment,
  AnalysisProtocolRelationsSourceSlotFragment(Fresh))

AFKCanonicalFramedAdditionalSourceSlotCatalog = CanonicalConcat(CanonicalSeq [
  ConcreteOwnerReadSlotSchema(
    PIR,PublicSetupInvocationView,
    DependentForAll([subject : AnalysisSubjectTuple],
      AnalysisPublicSetupInvocationCoordinate(subject,FiatShamir)),
    OccurrenceEvidence,
    CompleteOwnerBodyProjection(PublicSetupInvocationViewBody),
    AnalysisFiatShamirPublicSetupInvocationAdequacy,
    ExactPublicSetupInvocationViewAuthorityBinding,FreshSourceCapability,
    CryptographicPropertyAttemptFailurePartitionRef),
  AnalysisPIRSourceSlot(ExecutionView,
    AnalysisOwnerViewCoordinate(subject,FiatShamirExecutionView),
    AnalysisExecutionViewFields(subject,FiatShamirExecutionView,
      [protocol_id,core_id,challenge_interpretation,visible_history_law,
       resolver_coordinates,generated_execution_law,run_record_schema,
       replay_qualification_law,relation_run_view_issuance_law]),
    SemanticMeaning,AnalysisFiatShamirExecutionBoundaryAdequacy,
    ExactPIRStaticViewAuthorityBinding<ExecutionView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(TranscriptDeclarationView,
    AnalysisOwnerViewCoordinate(subject,TranscriptDeclarationView),
    AnalysisStaticViewFields(subject,TranscriptDeclarationView,
      [transcript_construction_id,core_id,state_type,absorbed_bytes_type,
       initial_state,initialization_schedule_law,absorb,squeeze_bytes,
       advance_state,application_domain,sampling_failure_coordinate,
       frame_body_law,frame_schedule]),SemanticMeaning,
    AnalysisTranscriptDeclarationAdequacy,
    ExactPIRStaticViewAuthorityBinding<TranscriptDeclarationView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(RequiredInfluenceView,
    AnalysisOwnerViewCoordinate(subject,RequiredInfluenceView),
    AnalysisStaticViewFields(subject,RequiredInfluenceView,
      [transcript_construction_id,core_id,scope_bindings,
       required_influence,additions,exact_prefix_law]),SemanticMeaning,
    AnalysisRequiredInfluenceAdequacy,
    ExactPIRStaticViewAuthorityBinding<RequiredInfluenceView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(ChallengeTransitionView,
    AnalysisOwnerViewCoordinate(subject,ChallengeTransitionView),
    AnalysisStaticViewFields(subject,ChallengeTransitionView,
      [transcript_construction_id,core_id,namespace_derivation_law,
       exact_length_law,state_update_before_decode_law,retry_law,
       sampling_failure_law,challenge_rules]),SemanticMeaning,
    AnalysisChallengeTransitionAdequacy,
    ExactPIRStaticViewAuthorityBinding<ChallengeTransitionView>,FreshSourceCapability),
  AnalysisPIRSourceSlot(FSConstructionView,
    AnalysisOwnerViewCoordinate(subject,FSConstructionView),
    AnalysisStaticViewFields(subject,FSConstructionView,
      [result_schema,fresh_protocol_id,fiat_shamir_protocol_id,
       shared_core_id,transcript_construction_id,occurrence_map,value_map,
       challenge_map,structural_conclusion]),
    PremiseSupport,AnalysisFSConstructionAdequacy,
    ExactPIRStaticViewAuthorityBinding<FSConstructionView>,FreshSourceCapability)
],AnalysisProtocolRelationsSourceSlotFragment(FiatShamir))
```

This catalog is deliberately bound to
`PIRCanonicalFramedFSProfileId`. Its transcript declaration, frame schedule,
namespace, retry, and sampling-failure fields do not form against
`PIRDuplexSpongeFSProfileId`. Equal Core identity cannot substitute the duplex
family or manufacture absent canonical fields. A duplex theorem transport
requires a separate Analysis profile and the family-specific views defined by
the duplex PIR owner.

The closed source/profile bodies are:

```text
SchnorrRelationSourceProfileAdequacy and
AFKFreshFsSourceProfileAdequacy
  = pairwise-distinct exact AnalysisAdequacyEvaluatorId values in
    `AnalysisCryptographicPropertyLanguageProfileId`

AFKFamilyFreshSourceProfileAdequacy and
AFKFamilyTargetSourceProfileAdequacy
  = pairwise-distinct exact AnalysisAdequacyEvaluatorId values in
    `AnalysisAFKTransportLanguageProfileId`

SchnorrRelationSourceProfileBody = {
  family_tag: SchnorrRelationSpecialSoundnessSource,
  slot_schemas: SchnorrSourceSlotCatalog,
  closed_field_read_set: exact derived union of those owner schema fields,
  adequacy_evaluator_id: SchnorrRelationSourceProfileAdequacy
}

SchnorrRelationSemanticReadManifestBody(S) = {
  source_profile_id: SchnorrRelationSourceProfileId,
  exact_subjects: SchnorrRelationSubjectProjection(S),
  slots: exact canonical instantiation of every declared slot schema from S
}

AFKFreshFsSourceProfileBody = {
  family_tag: AFKAdaptiveFreshFsSource,
  slot_schemas:
    CanonicalAppend(SchnorrSourceSlotCatalog,AFKCanonicalFramedAdditionalSourceSlotCatalog),
  closed_field_read_set: exact derived union of those owner schema fields,
  adequacy_evaluator_id: AFKFreshFsSourceProfileAdequacy
}

AFKTargetSemanticReadManifestBody(S) = {
  source_profile_id: AFKFreshFsSourceProfileId,
  exact_subjects: AFKTargetSubjectProjection(S),
  slots: exact canonical instantiation of every declared slot schema from S
}
```

“Exact canonical instantiation” is a derived operation: for each source-profile
slot schema it inserts the unique matching coordinate from `S`, selects exactly
the owner-declared field set, and sorts by the common manifest rule. Callers do
not author a slot list or adequacy Boolean. A missing or non-unique match is
malformed.

The `canonical relation/Fresh projection of S` contains no transcript-
construction, FS Protocol, FS result-schema, target setup, or FS-map field.
Consequently one Fresh special-soundness judgment can be reused by more than one
later construction without changing its question identity. Those fields enter
only `AFKTargetSemanticReadManifestBody(S)` and AFK applicability.

The source property and its finite transcript-pair carrier are owned here; the
Fresh manifest imports `AnalysisSharedRelationsSourceSlotFragment` plus
`AnalysisProtocolRelationsSourceSlotFragment(Fresh)` from
[the relation-source boundary](semantic-relations.md#3-exact-relation-source-projection).
The AFK target additionally imports the exact Fiat--Shamir axis fragment. Its
source manifest binds:

```text
one admitted Fresh Protocol and PIR source views
one admitted relation definition, Interface, and instance
checked Statement, claim, and Witness-role edges
commitment, challenge, response, verifier check, and accepting event
the exact challenge set C with cardinality N >= k = 2
```

The AFK target extension additionally binds the exact Fiat--Shamir
`ProtocolRelationBinding`, Plan Witness binding, Statement/claim/Witness
correspondence results, grounding equation, and EquationGrounding result. It
requires the producer-checked Fresh/Fiat--Shamir shape agreement while retaining
both Protocol-qualified IDs. Neither the checked construction nor a shared
Core derives this target relation ingress.

The experiment and `Gamma_special(S)`, rather than the source manifest, bind the
quantified extractor profile, group laws, efficiency premises, and other
algebraic side conditions. A source manifest contains only owner-issued
semantic reads; it cannot acquire Analysis-owned quantifiers or hypotheses.

`PublicCoinView` establishes structural eligibility and the location of public
coin sinks; it does not establish a probability law. The deterministic source
property does not read one. The separate AFK applicability manifest retains the
truth and exact PIR-to-experiment correspondence of the Fresh uniform independent
challenge distribution as explicit premises unless exact accepted authority
discharges them.

The quantified source carrier is a finite Foundation value type owned on this page:

```text
SchnorrSpecialSoundnessTranscriptType(S) = RootRecord<[
  (0,AnalysisStatementType(S)),
  (1,AnalysisCommitmentType(S)),
  (2,S.challenge_value_type),
  (3,AnalysisResponseType(S))
]>

SchnorrSpecialSoundnessPair(S) = RootRecord<[
  (0,SchnorrSpecialSoundnessTranscriptType(S)),
  (1,SchnorrSpecialSoundnessTranscriptType(S))
]>

SelectedFreshStatementEdge(S) =
  the exact `StatementEdge` selected by
  S.relation_axis_ingress.fresh.
    statement_correspondence_question_id_and_StatementEdgeRef

SelectedRelationInstanceStatement(S) =
  Select(
    AuthenticatedRelationInstance(S.relation_instance_id).
      public_values[SelectedFreshStatementEdge(S).relation.ref],
    SelectedFreshStatementEdge(S).relation.selector)

FreshTranscriptStatementIsInstanceBound(S,t) iff
  SelectedFreshStatementEdge(S).value_relation = SameExactType and
  FoundationValueEqual(AnalysisStatementType(S),
    SelectedRelationInstanceStatement(S),Select(t,0))

SelectedFreshCommitmentOccurrence(S) =
  the unique prover `Message` occurrence before
  UniqueChallengeOccurrence(S.shared_core_id,S.challenge_ref) that the exact
  three-move property-profile law selects as the first-message input of
  AuthenticatedCheckDecl(S.shared_core_id,S.core_check_ref)

SelectedFreshResponseOccurrence(S) =
  the unique prover `Message` occurrence after
  UniqueChallengeOccurrence(S.shared_core_id,S.challenge_ref) that the same
  fixed law selects as the response input of that Check

FreshTranscriptRoleValueRefs(S) = {
  statement:
    ResolvedPublicBinding(
      SelectedFreshStatementEdge(S).protocol.binding).value,
  commitment:
    OccurrenceOutputValueRef(
      SelectedFreshCommitmentOccurrence(S),0),
  challenge:
    OccurrenceOutputValueRef(
      UniqueChallengeOccurrence(S.shared_core_id,S.challenge_ref),0),
  response:
    OccurrenceOutputValueRef(
      SelectedFreshResponseOccurrence(S),0)
}

FreshAcceptanceOwnerClosure(S) =
  AnalysisAcceptanceProducerProjection(S)

FreshAcceptanceValueRefClosure(S) =
  the canonical sequence of every `ValueRef` in
  FreshAcceptanceOwnerClosure(S) that feeds the selected Check inputs, the
  selected Check or Terminal occurrence guards, another check required by the
  selected terminal, or a deterministic derived value feeding one of those

FreshTupleOwnerSubstitution(S,t) =
  the unique total map on FreshAcceptanceValueRefClosure(S) obtained by:
    mapping the four exact refs in FreshTranscriptRoleValueRefs(S) to,
      respectively, Select(t,0), Select(t,1), Select(t,2), and Select(t,3);
    mapping each SessionContext or PublicParameter binding to its exact value
      in S.public_setup_invocation_views.fresh;
    mapping each TypedConstant to its authenticated Core value; and
    evaluating every remaining deterministic derived value in topological
      owner order with its exact PIR algorithm, evaluation contract, and
      already substituted ordered inputs

ExactFreshTranscriptAcceptance(S,t) iff
  let sigma = FreshTupleOwnerSubstitution(S,t) in
  Evaluate(
    AuthenticatedCheckDecl(S.shared_core_id,S.core_check_ref).algorithm,
    AuthenticatedCheckDecl(S.shared_core_id,S.core_check_ref).
      evaluation_contract,
    OrderedInputValues(
      AuthenticatedCheckDecl(S.shared_core_id,S.core_check_ref).inputs,sigma))
      = MetaBooleanTrue
  and ApplyAuthenticatedTerminalLaw(
    S.shared_core_id,S.core_accept_terminal_ref,
    FreshAcceptanceOwnerClosure(S),
    ExactCheckResultMapWithSelectedTrue(S,sigma),sigma) = Accept

admitted_pair_predicate(S,pair) iff
  pair is one CanonicalValue<SchnorrSpecialSoundnessPair(S)>,
  FreshTranscriptStatementIsInstanceBound(S,Select(pair,0)),
  FreshTranscriptStatementIsInstanceBound(S,Select(pair,1)),
  both transcript Statements are equal and both commitments are equal,
  both challenges inhabit AuthenticatedChallengeModelValues(S),
  the two canonical challenge values are unequal,
  CanonicalValueBody(Select(Select(pair,0),2)) is byte-lexicographically less
    than CanonicalValueBody(Select(Select(pair,1),2)), and
  ExactFreshTranscriptAcceptance(S,Select(pair,0)) and
  ExactFreshTranscriptAcceptance(S,Select(pair,1))
```

`RootRecord` is the exact Foundation root record type constructor, so neither the type
nor a value carries a `RunRecord`, live replay capability, owner handle, or
future Analysis ID. The complete subject tuple fixes the Protocol, relation,
check, terminal, and challenge model outside the value. A `CheckedReplayMatch`
may validate how one concrete tuple was obtained, but it is occurrence support
only and is neither pair membership nor universal property authority. Changing
any type, field ordinal, subject, or reconstructed acceptance predicate changes
the pair schema or its question; no undefined dependent-record constructor is
used.

The role-value references above are derived from authenticated owner bodies;
none is a caller-supplied `ValueRef`. Formation requires the four references to
be pairwise distinct, to have exactly the four displayed value types, and to
cover every tuple-varying leaf in `FreshAcceptanceValueRefClosure(S)`. Every
other leaf must resolve uniquely to an authenticated constant or to the exact
Fresh public-setup invocation view. A verifier-private input, an unrelated
public input, a second prover-controlled value, a missing setup entry, an
unsupported evaluator, or an ambiguous role match refuses this exact property
profile rather than leaving a partial predicate.

`ExactCheckResultMapWithSelectedTrue` is not an authored map. It evaluates every
check required by the selected terminal from the same closed substitution,
requires the selected check result to be true, and retains the exact owner
`CheckRef` keys. `ApplyAuthenticatedTerminalLaw` is the PIR terminal rule for
the selected declaration and occurrence: it evaluates the occurrence guard,
required-check set, claim dispositions, and `Accept` verdict from their
authenticated owner declarations. Thus `ExactFreshTranscriptAcceptance` is a
PIR predicate. It does not read a grounding equation, relation verifier,
correspondence result, or Analysis hypothesis.

The instance anchor is deliberately separate from acceptance. This exact lane
admits only a `SameExactType` Statement edge and fixes the one Statement
quantified by the concrete question to the selected admitted
`RelationInstance` by Foundation value equality; it does not say
that PIR acceptance implies relation membership. That implication remains
exactly `SchnorrAcceptanceRelationGoal(S)` in the hypothesis context. The
strict canonical-body ordering on the two challenge values gives every
unordered fork exactly one pair representation. Reversing a pair is a
nonmember, not a second quantified case.

The property is deterministic and multi-transcript: from two accepting
transcripts with the same Statement and first message, and two distinct legal
challenges, the exact extractor returns a Witness satisfying the selected
relation. It is not a probability bound and is not established by one honest
run. Its experiment universally quantifies over the exact accepted typed
`SchnorrSpecialSoundnessPair` domain above and applies
the deterministic extractor to every member; causal generation is not a
membership requirement.

The active source experiment body closes the common profile fields as follows:

```text
ExactSubjectSequenceUnion(left,right) =
  require each input to be a canonical sequence of exact typed semantic
  subject refs with no duplicate within that input; return `left` followed by
  exactly those entries of `right` whose complete ContentRefV0 is absent from
  `left`, preserving each input's order; require the output nonempty
```

Equality for this constructor is byte equality of complete typed content refs,
not display labels. It is the only union elaborator used for ordered
`AnalysisQuestionBody.exact_subjects`; it rejects an ill-typed input and never
sorts subjects behind the family contract's declared order.

```text
SchnorrDeterministicExtractorProfileBody(S: AnalysisSubjectTuple) = {
  input_and_output_types: {
    inputs: [SchnorrSpecialSoundnessPair(S)],
    outputs: [AnalysisWitnessType(S)]
  },
  private_state_and_randomness_types: [Unit, Unit],
  allowed_source_and_oracle_capabilities: [],
  counterfactual_rights: [],
  state_preservation_relation: deterministic stateless evaluation,
  output_distribution_preservation_relation: deterministic singleton law,
  witness_success_relation:
    output x satisfies the exact relation selected by the pair subjects,
  termination_and_asymptotic_resource_law:
    declared polynomial-time field/group law under separately supplied exact
    primitive and resource premise schemas; profile formation does not
    establish that law,
  counterfactual_capability_contract_and_property_family_scope: {
    counterfactual_capability_contract: none,
    property_family_scope: FixedExtractorUniversalCorrectness and
      KOutOfNSpecialSoundness(k = 2)
  }
}

SchnorrDeterministicExtractorProfileId(S: AnalysisSubjectTuple) =
  AnalysisExtractorProfileId(
    B, SchnorrDeterministicExtractorProfileBody(S))

SchnorrSpecialSoundnessExperimentProfile(S: AnalysisSubjectTuple) = {
  family: KOutOfNSpecialSoundness,
  source_profile_id: SchnorrRelationSourceProfileId,
  quantifier_prefix: [
    ExistsExtractor(
      binding_ordinal: 0,
      SchnorrDeterministicExtractorProfileId(S)),
    ForAllValue(
      binding_ordinal: 1,
      SchnorrSpecialSoundnessPair(S), admitted_pair_predicate(S))
  ],
  role_interfaces: [Ext: deterministic_extractor_abi],
  setup_and_input_sampling: none,
  randomness_ownership_and_independence: none,
  public_coin_or_oracle_model:
    exact Fresh public-coin structural profile and challenge set,
  scheduler: deterministic pair validation then extraction,
  generated_execution_relation:
    exact canonical pair membership using the instance Statement anchor and
    `ExactFreshTranscriptAcceptance`; acceptance itself is reconstructed only
    from the selected PIR Check and Terminal laws,
  observation_and_win_event:
    Ext output satisfies the bound relation for every member,
  failure_abort_and_noncompletion_law:
    malformed, refused, and nonmember inputs are outside the implication;
    failure of one candidate Ext on a member refutes only that fixed-Ext
    candidate and leaves the existential family unanswered unless a complete
    family refutation procedure is admitted,
  termination_law: source extractor polynomial-time premise,
  resource_basis: exact source extractor steps,
  output_type: deterministic universal property judgment
}

SchnorrSpecialSoundnessQuestion(S: AnalysisSubjectTuple) = AnalysisQuestionBody {
  family: KOutOfNSpecialSoundness,
  exact_subjects: ExactSubjectSequenceUnion(
    SchnorrRelationSubjectProjection(S), [AnalysisChallengeDomainId(S)]),
  context: SemanticExperimentContext {
    semantic_read_manifest_ids: [SchnorrRelationSemanticReadManifestId(S)],
    experiment_profile_ids: [SchnorrSpecialSoundnessExperimentProfileId(S)]
  },
  family_payload: {
    k = 2, AnalysisChallengeDomainId(S) and its exact cardinality N,
    exact accepted typed pair-domain schema,
    exact deterministic extractor ABI,
    exact relation-witness conclusion schema
  },
  named_premise_requirements: SchnorrNamedPremiseRequirements(S)
}

SchnorrSpecialSoundnessGoal(S: AnalysisSubjectTuple) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B, SchnorrSpecialSoundnessQuestion(S)),
  named_premise_bindings: SchnorrNamedPremiseBindings(S)
}

SchnorrFixedExtractorUniversalExperimentProfile(S: AnalysisSubjectTuple) = {
  family: FixedExtractorUniversalCorrectness,
  source_profile_id: SchnorrRelationSourceProfileId,
  quantifier_prefix: [
    ForAllValue(
      binding_ordinal: 0,
      SchnorrSpecialSoundnessPair(S), admitted_pair_predicate(S))
  ],
  role_interfaces: [
    candidate_extractor_subject: deterministic_extractor_abi
  ],
  setup_and_input_sampling: none,
  randomness_ownership_and_independence: none,
  public_coin_or_oracle_model:
    exact Fresh public-coin structural profile and challenge set,
  scheduler: deterministic pair validation then candidate extraction,
  generated_execution_relation:
    exact canonical pair membership using the instance Statement anchor and
    `ExactFreshTranscriptAcceptance`; acceptance itself is reconstructed only
    from the selected PIR Check and Terminal laws,
  observation_and_win_event:
    the candidate extractor output satisfies the bound relation for every
    member,
  failure_abort_and_noncompletion_law:
    malformed, refused, and nonmember inputs are outside the implication;
    candidate failure on a member is an exact counterexample,
  termination_law:
    total return on every quantified member; no polynomial-time conclusion,
  resource_basis: exact candidate extractor steps,
  output_type: deterministic fixed-extractor universal judgment
}

SchnorrFixedExtractorWorksQuestion(
  S: AnalysisSubjectTuple, Ext: PortableAlgorithmRef) =
AnalysisQuestionBody {
  family: FixedExtractorUniversalCorrectness,
  exact_subjects:
    CanonicalAppend(
      ExactSubjectSequenceUnion(SchnorrRelationSubjectProjection(S),
                     [AnalysisChallengeDomainId(S)]), [Ext]),
  context: SemanticExperimentContext {
    semantic_read_manifest_ids: [SchnorrRelationSemanticReadManifestId(S)],
    experiment_profile_ids: [
      SchnorrFixedExtractorUniversalExperimentProfileId(S)
    ]
  },
  family_payload: {
    candidate_extractor_ref: Ext,
    exact deterministic extractor ABI,
    exact accepted typed pair-domain schema,
    exact relation-witness conclusion schema
  },
  named_premise_requirements: SchnorrExtractorPremiseRequirements(S)
}

SchnorrFixedExtractorWorksGoal(
  S: AnalysisSubjectTuple, Ext: PortableAlgorithmRef) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(
    B, SchnorrFixedExtractorWorksQuestion(S, Ext)),
  named_premise_bindings: SchnorrExtractorPremiseBindings(S, Ext)
}

EmptyAnalysisHypothesisContextBody = AnalysisHypothesisContextBody {
  nodes: [],
  roots: [],
  exact_named_premise_ids: ContextPremiseIds(nodes, roots)
}

EmptyAnalysisHypothesisContextId =
  AnalysisHypothesisContextId(B,EmptyAnalysisHypothesisContextBody)

SchnorrFixedExtractorWorksPropositionBody(S,Ext) =
  AnalysisPropositionBody {
    goal_id: AnalysisGoalId(B,SchnorrFixedExtractorWorksGoal(S,Ext)),
    hypothesis_context_id: EmptyAnalysisHypothesisContextId
  }
```

### 3.1 Activated checked finite cover

The fixed-extractor subquestion names `Ext` as an exact subject and reuses the
same pair domain and experiment body with the existential removed. A member on
which `Ext` fails is an exact counterexample to that subquestion. The selected
property profile now admits one checked finite-cover rule for this family, and
the bounded executable instantiates it for exactly:

```text
p = 23, q = 11, g = 2, Statement = 8,
challenge carrier = {0,...,7},
Ext = the authenticated response-difference portable algorithm
```

The raw quantified value remains an ordered pair of transcripts with eight
`Nat64` leaves. Raw membership is evaluated first and requires the same exact
Statement and commitment, strictly ordered distinct challenges, and the
selected Fresh `Check` and accepting `Terminal` for both transcripts. The
checker never treats normalization as permission to repair a nonmember.

For an admitted pair, the selected normalization maps each transcript as:

```text
Statement  -> Statement mod 9
commitment -> commitment mod 23
challenge  -> challenge mod 8
response   -> response mod 11
```

Raw membership already fixes `Statement=8` and challenges in `{0,...,7}`, so
the first and third operations are identity on the admitted domain. Commitment
and response reduction remove exactly the distinctions that the selected
Fresh verifier and candidate cannot observe. The inverse embedding widens the
canonical representatives back into the raw `Nat64` carrier. Both algorithms,
the candidate, and the representative stream are portable algorithms over the
ordinary Foundation
[natural modular-arithmetic module](../foundation/natural-modular-arithmetic.md);
none is an opaque host-only `schnorr.extract` operation.

The representative stream contains the eleven subgroup commitment residues

```text
1, 2, 3, 4, 6, 8, 9, 12, 13, 16, 18
```

and all twenty-eight pairs `0 <= c0 < c1 < 8`, with the unique canonical
responses accepted by the verifier. It therefore has exactly `308` sorted,
duplicate-free representatives. Its selected ordered-stream digest is:

```text
1d9472a4470c26748e864ea0b4b7383ee17ee4e83210a70a90fb03081532a3dd
```

This count and digest are checked outputs of the authenticated stream, not a
replacement for semantic coverage. Three separate ordinary affirmative
Analysis judgments establish:

1. coverage of every admitted raw residue class and exact stream reachability;
2. universal quotient factorization and candidate-output congruence through
   normalization; and
3. transfer of representative success to the raw member relation.

The final rule requires all three judgment IDs in their exact goal order and
exactly nine operation bindings: representative stream, raw-domain predicate,
representative-domain predicate, normalization, representative embedding,
candidate, quotient factorization, representative success, and success
transfer. Its bounded stream rerun directly exercises the five operational
members of that set; the three certificate judgments bind the remaining
universal and transfer obligations. The rule then forms an ordinary affirmative
`FixedExtractorUniversalCorrectness` judgment with the empty hypothesis
context. The receipt records counts, digests, and consumed controls but carries
no independent proof authority.

This activation establishes only the exact fixed-candidate universal above. It
does not establish `SchnorrExtractorEfficiencyGoal(S,Ext)`, existential or
asymptotic special soundness, knowledge soundness, Fiat--Shamir security, ROM
security, or QROM security. `GammaSpecialBody(S,Ext)` therefore remains the
general conditional shape. For the exact selected `(S,Ext)`, its fixed-
extractor node may now be supported by this ordinary judgment; the current
bounded special-soundness fixture still retains its broader explicit theorem
assumption and does not claim that the other algebraic, correspondence, or
efficiency obligations have been discharged.

Failure of a proposed extractor supports rejection of that proposal, not
`Negative` for special soundness. The existential family may emit `Negative`
only if a separately admitted procedure completely refutes every extractor in
its exact quantified domain; no such procedure is selected.

An affirmative existential judgment records the exact admitted
`PortableAlgorithmRef` used for `Ext` as its quantified witness and binds it to
the extractor profile and ABI. That witness can serve only consumers of this
exact finite `KOutOfNSpecialSoundness` proposition. It cannot fill the distinct
uniform all-`n` `AsymptoticKOutOfNSpecialSoundness` source slot required by AFK
family transport; a generic special-soundness label cannot bridge the two.

There is no sampled challenge in this deterministic hyperproperty. The exact
Fresh challenge law is read separately when the AFK applicability question
matches the source Protocol to the theorem's public-coin model.

The initial executable inhabitant may use a prime-order-`11` group with a
challenge subset of cardinality `N = 8`. This makes every nonzero challenge
difference invertible modulo `11` and permits a one-octet, one-draw total
uniform decoder into the challenge set. These fixture parameters do not enter
the generic family definition.

The source proposition uses ordinary formed premise goals. This compact body
constructor does not mint a new premise language:

```text
SchnorrSourcePremiseQuestion(S, family, payload, extra_subjects) =
  AnalysisQuestionBody {
    family,
    exact_subjects: ExactSubjectSequenceUnion(
      SchnorrRelationSubjectProjection(S),
      CanonicalAppend([AnalysisChallengeDomainId(S)],extra_subjects)),
    context: SemanticExperimentContext {
      semantic_read_manifest_ids:
        [SchnorrRelationSemanticReadManifestId(S)],
      experiment_profile_ids:
        [SchnorrSpecialSoundnessExperimentProfileId(S)]
    },
    family_payload: payload
  ,
    named_premise_requirements: NamedPremiseRequirementsOf(family, exact_subjects)
}

SchnorrSourcePremiseGoal(S, family, payload, extra_subjects) =
  AnalysisGoalBody {
    question_id: AnalysisQuestionId(
      B, SchnorrSourcePremiseQuestion(S,family,payload,extra_subjects))
  ,
    named_premise_bindings: {}
}

SchnorrChallengeModelGoal(S) = SchnorrSourcePremiseGoal(
  S, ChallengeDomainCorrespondence, {
    owner_coordinates:
      [AnalysisChallengeRefCoordinate(S),
       AnalysisChallengeNominalDomainCoordinate(S)],
    analysis_model: AnalysisChallengeDomainId(S),
    exact_proposition:
      the nominal-domain coordinate denotes exactly the model value sequence
      at the declared value type; its cardinality is the model cardinality
  }, [])

SchnorrAcceptanceRelationGoal(S) = SchnorrSourcePremiseGoal(
  S, AcceptanceRelationCorrespondence, {
    protocol_source: AnalysisAcceptanceProducerProjection(S), including S.core_check_ref,
      its unique InvokeCheck occurrence, S.core_accept_terminal_ref, and every
      owner-derived producer/guard/scope/effect dependency,
    Relations_source: S.relation_instance_id,
      S.relation_axis_ingress.fresh.grounding_equation_id, and
      S.relation_axis_ingress.fresh.equation_grounding_question_id whose
      variant is exactly EquationGrounding(
        S.relation_axis_ingress.fresh.grounding_equation_id,...),
    exact_proposition:
      for every structurally complete instance-bound transcript projection,
      ExactFreshTranscriptAcceptance(S,t) holds iff the exact
      grounding/relation verifier predicate holds; the left side is the PIR-
      only Check/Terminal predicate and this premise is the sole bridge from
      that predicate to relation membership
  }, [])

SchnorrAlgebraEncodingGoal(S) = SchnorrSourcePremiseGoal(
  S, AlgebraAndCanonicalEncodingLaws, {
    exact relation/group/encoding coordinates wholly contained in
      S.relation_definition_id, S.relation_semantic_model_id, and
      AnalysisChallengeDomainId(S),
    exact_proposition:
      the selected relation is the stated prime-order cyclic-group relation,
      distinct admitted challenges have invertible differences, and every
      extractor arithmetic/encoding operation has its stated exact denotation
  }, [])

SchnorrRelationMembershipEfficiencyGoal(S) = SchnorrSourcePremiseGoal(
  S, PolynomialTimeRelationMembership, {
    exact relation semantic model and statement/witness types,
    exact asymptotic machine and length measure,
    exact_proposition: relation membership is polynomial time in that measure
  }, [])

SchnorrVerifierEfficiencyGoal(S) = SchnorrSourcePremiseGoal(
  S, PolynomialTimeSourceVerifier, {
    exact PIR CheckDecl algorithm/evaluation contract and terminal path,
    exact asymptotic machine and length measure,
    exact_proposition: the selected source verifier is polynomial time
  }, [])

SchnorrExtractorEfficiencyGoal(S,Ext) = SchnorrSourcePremiseGoal(
  S, PolynomialTimeExtractor, {
    exact extractor_ref: Ext,
    profile_id: SchnorrDeterministicExtractorProfileId(S),
    exact asymptotic machine and length measure,
    exact_proposition: Ext is total and polynomial time on every admitted pair
  }, [Ext])

GammaSpecialBody(S,Ext) = AnalysisHypothesisContextBody {
  nodes: [
    {0, AnalysisGoalId(B,SchnorrChallengeModelGoal(S)), [], premises(goal)},
    {1, AnalysisGoalId(B,SchnorrAcceptanceRelationGoal(S)), [], premises(goal)},
    {2, AnalysisGoalId(B,SchnorrAlgebraEncodingGoal(S)), [], premises(goal)},
    {3, AnalysisGoalId(B,SchnorrRelationMembershipEfficiencyGoal(S)), [], premises(goal)},
    {4, AnalysisGoalId(B,SchnorrVerifierEfficiencyGoal(S)), [], premises(goal)},
    {5, AnalysisGoalId(B,SchnorrExtractorEfficiencyGoal(S,Ext)), [], premises(goal)},
    {6, AnalysisGoalId(B,SchnorrFixedExtractorWorksGoal(S,Ext)), [], premises(goal)}
  ],
  roots: [0,1,2,3,4,5,6],
  exact_named_premise_ids: ContextPremiseIds(nodes, roots)
}

GammaSpecialId(S,Ext) =
  AnalysisHypothesisContextId(B, GammaSpecialBody(S,Ext))

SchnorrSpecialSoundnessProposition(S,Ext) = AnalysisPropositionBody {
  goal_id: AnalysisGoalId(B, SchnorrSpecialSoundnessGoal(S)),
  hypothesis_context_id: GammaSpecialId(S,Ext)
}
```

The algebra/encoding premise reads no `fixed_setup_static_sources` field. Its group
and encoding meaning is owned by the relation definition/model already present
in `SchnorrSourceSlotCatalog`; the Analysis challenge model supplies only its
finite challenge-value correspondence. The PIR public-setup invocation view is
already a Fresh source because it fixes the concrete public parameters under
which acceptance is interpreted; the Analysis-owned `AFKFixedPublicSetupId`
and transcript-construction additions enter only the target manifest and
applicability path.

The deterministic conclusion does not use a challenge probability law. Fresh
uniformity, independence, and their PIR-to-experiment correspondence are
separate AFK-applicability premises. The finite group-order-`11` extractor
execution establishes none of the asymptotic premise goals above.

The existential introduction and its source capability are also formed rather
than implied by the display:

```text
ExistentialExtractorIntroductionRuleRef,
ExactTheoremApplicabilityCheckRuleRef,
ConditionalFamilyInstanceCorrespondenceIntroductionRuleRef, and
DependentFamilyMemberSpecializationRuleRef
  = four pairwise-distinct exact declarations under
    AnalysisNativeRuleCoordinate

ExactInheritedConditionalQualificationRef =
  one exact AnalysisQualificationRequirementCoordinate declaration

FiniteSpecialSoundnessQualificationRef,
AssumedExternalAllNQualificationRef,
AssumedTheoremTruthQualificationRef,
AFKFamilyApplicabilityQualificationRef,
AFKFamilyInstanceCorrespondenceQualificationRef,
AFKFamilyTransportQualificationRef, and
AFKMemberSpecializationQualificationRef
  = seven pairwise-distinct exact AnalysisQualificationCoordinate declarations;
    finite special soundness and assumed all-length source truth are property-
    profiled, applicability and family-instance correspondence are transport-
    profiled, and assumed theorem truth plus the latter two results are source-
    validation-profiled

FiniteSpecialSoundnessConsumerRef,
AFKFamilyPropertyTransportConsumerRef, and
AFKMemberSpecializationConsumerRef
  = three pairwise-distinct exact AnalysisNamedConsumerCoordinate declarations

FiniteSpecialSoundnessPurposeRef,
AFKTheoremSourcePropertyPurposeRef,
AFKExactTheoremFamilyTransportPurposeRef,
AFKFamilyTargetSpecializationPurposeRef, and
AFKExactFamilyMemberSpecializationPurposeRef
  = five pairwise-distinct exact AnalysisTypedPurposeCoordinate declarations

AnalysisCryptographicNativeRuleProfileContracts contains exactly these active Analysis
entries in the directly selected cryptographic semantic-language profile:
  ExistentialExtractorIntroductionRuleRef ->
    AnalysisNativeRuleSemanticsContract<
      AnalysisCryptographicPropertyLanguageProfileId> {
      exact_payload_meta_schema: {
        experiment_profile_id: AnalysisExperimentProfileId,
        extractor_profile_id: AnalysisExtractorProfileId,
        extractor_quantifier_ordinal: Natural,
        conclusion_family: AnalysisFamilyCoordinate
      },
      allowed_conclusion_families: [KOutOfNSpecialSoundness],
      exact_premise_requirement_schema:
        AllReachableHypothesisNodeRequirements followed by exactly one
        ExactQuantifiedWitnessRequirement naming the payload profile/ordinal,
      exact_typed_transform_program_schema:
        introduce that same witness at that exact quantifier ordinal once,
      conclusion_reconstruction_law:
        reconstruct the source goal and preserve its complete context,
      failure_classification: CryptographicPropertyAttemptFailurePartitionRef
    },
  ExactTheoremApplicabilityCheckRuleRef ->
    AnalysisNativeRuleSemanticsContract<
      AnalysisCryptographicPropertyLanguageProfileId> {
      exact_payload_meta_schema: {
        theorem_schema_id: AnalysisTheoremSchemaId,
        family_definition_id: AnalysisAsymptoticProtocolFamilyDefinitionId,
        source_property_schema:
          TheoremSchemaComponent<"analysis.theorem-property-schema">,
        target_property_schema:
          TheoremSchemaComponent<"analysis.theorem-property-schema">,
        transform_program:
          TheoremSchemaComponent<"analysis.theorem-transform-program">,
        conclusion_law:
          TheoremSchemaComponent<"analysis.theorem-conclusion-law">
      },
      allowed_conclusion_families: [TheoremApplicability],
      exact_premise_requirement_schema:
        AllReachableHypothesisNodeRequirements of the exact family
        applicability context,
      exact_typed_transform_program_schema:
        exact theorem-component and local-template equality with no
        theorem-truth inference,
      conclusion_reconstruction_law:
        reconstruct only the exact structural applicability goal,
      failure_classification: CryptographicPropertyAttemptFailurePartitionRef
    },
  ConditionalFamilyInstanceCorrespondenceIntroductionRuleRef ->
    AnalysisNativeRuleSemanticsContract<
      AnalysisCryptographicPropertyLanguageProfileId> {
      exact_payload_meta_schema: ExactAFKFamilyMemberRulePayload,
      allowed_conclusion_families: [FamilyInstanceCorrespondence],
      exact_premise_requirement_schema:
        AllReachableHypothesisNodeRequirements of the exact pointwise context,
      exact_typed_transform_program_schema:
        complete role-table and quantitative-substitution checking,
      conclusion_reconstruction_law:
        reconstruct only the exact pointwise correspondence goal,
      failure_classification: CryptographicPropertyAttemptFailurePartitionRef
    },
  DependentFamilyMemberSpecializationRuleRef ->
    AnalysisNativeRuleSemanticsContract<
      AnalysisCryptographicPropertyLanguageProfileId> {
      exact_payload_meta_schema: ExactAFKFamilyMemberRulePayload,
      allowed_conclusion_families:
        [AdaptiveKnowledgeExtractionAtFixedLengthQltN],
      exact_premise_requirement_schema:
        AllReachableHypothesisNodeRequirements of the exact union context plus
        the exact family-target and pointwise-correspondence capability
        requirements,
      exact_typed_transform_program_schema:
        exact pointwise family-to-native formula reconstruction,
      conclusion_reconstruction_law:
        reconstruct only AFKMemberKnowledgeGoal(S,ell0),
      failure_classification: CryptographicPropertyAttemptFailurePartitionRef
    }.

ExactAFKFamilyMemberRulePayload = {
  family_definition_id: AnalysisAsymptoticProtocolFamilyDefinitionId,
  logical_index_id: AnalysisLogicalNatLiteralId,
  concrete_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  native_statement_length: StatementLength(exact statement-type coordinate),
  exact_role_catalog_ref:
    AnalysisProfileDeclarationRef<"analysis.afk-family-role-catalog">
}

AnalysisUseDeclarationBody(kind,tag) = MetaRecord {
  0: MetaSymbol(kind), 1: MetaSymbol(tag), 2: MetaNatural(0)
}
```

The closed use and active qualification coordinates above resolve exactly these
pairwise-distinct bodies in their stated direct profiles:

```text
ExactInheritedConditionalQualificationRef ->
  AnalysisUseDeclarationBody("qualification","exact-inherited-conditional")
FiniteSpecialSoundnessQualificationRef ->
  AnalysisUseDeclarationBody("qualification","finite-special-soundness-result")
AssumedExternalAllNQualificationRef ->
  AnalysisUseDeclarationBody(
    "qualification","conditional-assumed-external-all-n")
AssumedTheoremTruthQualificationRef ->
  AnalysisUseDeclarationBody(
    "qualification","conditional-assumed-theorem-truth")
AFKFamilyApplicabilityQualificationRef ->
  AnalysisUseDeclarationBody("qualification","afk-family-applicability-result")
AFKFamilyInstanceCorrespondenceQualificationRef ->
  AnalysisUseDeclarationBody(
    "qualification","afk-family-instance-correspondence-result")
AFKFamilyTransportQualificationRef ->
  AnalysisUseDeclarationBody("qualification","afk-family-transport-result")
AFKMemberSpecializationQualificationRef ->
  AnalysisUseDeclarationBody("qualification","afk-member-specialization-result")
FiniteSpecialSoundnessConsumerRef ->
  AnalysisUseDeclarationBody("consumer","finite-special-soundness")
AFKFamilyPropertyTransportConsumerRef ->
  AnalysisUseDeclarationBody("consumer","afk-family-property-transport")
AFKMemberSpecializationConsumerRef ->
  AnalysisUseDeclarationBody("consumer","afk-member-specialization")
FiniteSpecialSoundnessPurposeRef ->
  AnalysisUseDeclarationBody("purpose","finite-special-soundness")
AFKTheoremSourcePropertyPurposeRef ->
  AnalysisUseDeclarationBody("purpose","afk-theorem-source-property")
AFKExactTheoremFamilyTransportPurposeRef ->
  AnalysisUseDeclarationBody("purpose","afk-exact-theorem-family-transport")
AFKFamilyTargetSpecializationPurposeRef ->
  AnalysisUseDeclarationBody("purpose","afk-family-target-specialization")
AFKExactFamilyMemberSpecializationPurposeRef ->
  AnalysisUseDeclarationBody("purpose","afk-exact-family-member-specialization")
```

The actual-result qualification catalog is closed by fixed, profile-local
subject-parametric laws. Each law authenticates the candidate, calls
`DeriveQualificationSubjectContext`, and inverse-matches one exact constructor
case. The symbols `S`, `Ext`, `F`, `n0_literal`, and `ell0` below are outputs of
that match. They are invocation-local values and never bytes, IDs, or free
parameters in the profile law source:

```text
FiniteSpecialSoundnessQualificationAcceptanceLawRef =
  the exact property-profile law that accepts candidate iff its derived
  QualificationSubjectContext has:
    family = KOutOfNSpecialSoundness,
    polarity = Affirmative,
    candidate_proposition_id = AnalysisPropositionId(
      B,SchnorrSpecialSoundnessProposition(S,Ext)),
    candidate_goal_id = AnalysisGoalId(B,SchnorrSpecialSoundnessGoal(S)),
    inherited_hypothesis_context_id = GammaSpecialId(S,Ext), and
    exact_quantified_witness_coordinates = [Ext];
  the law derives S and Ext by authenticating and inverse-matching the exact
  question, proposition, semantic-basis rule payload, quantified-witness
  requirement, and support binding of the candidate

AssumedExternalAllNQualificationAcceptanceLawRef =
  the exact imported property-profile law that inverse-matches F and accepts
  exactly family = AsymptoticKOutOfNSpecialSoundness,
  polarity = Affirmative,
  candidate_proposition_id = AnalysisPropositionId(
    B,AFKFamilySpecialSoundnessPropositionBody(F)),
  candidate_goal_id = AnalysisGoalId(B,AFKFamilySpecialSoundnessGoal(F)),
  candidate_question_id = AnalysisQuestionId(
    B,AFKFamilySpecialSoundnessQuestion(F)),
  exact_subjects = [F],
  question_context = the exact context in
    AFKFamilySpecialSoundnessQuestion(F),
  inherited_hypothesis_context_id = GammaAFKFamilySpecialId(F), and
  exact_quantified_witness_coordinates =
    the exact uniform-extractor-family witness coordinate authenticated from
    the candidate semantic basis and support

AssumedTheoremTruthQualificationAcceptanceLawRef =
  the exact theorem-source-validation-profile law that accepts exactly
  family = TheoremTruth, polarity = Affirmative,
  candidate_proposition_id =
    TheoremTruthPropositionId(AFKV2TheoremSchemaId),
  candidate_goal_id = AnalysisGoalId(
    B,TheoremTruthGoal(AFKV2TheoremSchemaId)),
  candidate_question_id = AnalysisQuestionId(
    B,TheoremTruthQuestion(AFKV2TheoremSchemaId)),
  exact_subjects = [AFKV2TheoremSchemaId],
  question_context = SourceFree(TheoremTruthSourceFreeReasonRef),
  inherited_hypothesis_context_id =
    AnalysisHypothesisContextId(B,{nodes: [], roots: [], exact_named_premise_ids: []}), and
  exact_quantified_witness_coordinates = []

AFKFamilyApplicabilityQualificationAcceptanceLawRef =
  the exact transport-profile law that inverse-matches F and accepts exactly
  family = TheoremApplicability, polarity = Affirmative,
  candidate_proposition_id = AnalysisPropositionId(
    B,AFKFamilyApplicabilityPropositionBody(F)),
  candidate_goal_id = AnalysisGoalId(B,AFKFamilyApplicabilityGoal(F)),
  inherited_hypothesis_context_id = GammaAFKApplicabilityId(F), and
  exact_quantified_witness_coordinates = []

AFKFamilyInstanceCorrespondenceQualificationAcceptanceLawRef =
  the distinct exact transport-profile law that inverse-matches
  (F,n0_literal,S,ell0) and accepts exactly
  family = FamilyInstanceCorrespondence, polarity = Affirmative,
  candidate_proposition_id = AnalysisPropositionId(
    B,FamilyInstanceCorrespondencePropositionBody(
      F,n0_literal,S,ell0)),
  candidate_goal_id = AnalysisGoalId(
    B,FamilyInstanceCorrespondenceGoal(F,n0_literal,S,ell0)),
  inherited_hypothesis_context_id =
    GammaFamilyInstanceId(F,n0_literal,S,ell0), and
  exact_quantified_witness_coordinates = []

AFKFamilyTransportQualificationAcceptanceLawRef =
  the exact theorem-source-validation-profile law that inverse-matches F and
  accepts exactly family = AdaptiveKnowledgeSoundnessQltN,
  polarity = Affirmative,
  candidate_proposition_id = AnalysisPropositionId(
    B,AFKFamilyAdaptiveKnowledgePropositionBody(F)),
  candidate_goal_id = AnalysisGoalId(B,AFKFamilyAdaptiveKnowledgeGoal(F)),
  inherited_hypothesis_context_id = GammaAFKFamilyTargetId(F), and
  exact_quantified_witness_coordinates = []

AFKMemberSpecializationQualificationAcceptanceLawRef =
  the distinct exact theorem-source-validation-profile law that inverse-
  matches (F,n0_literal,S,ell0) and accepts exactly
  family = AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  polarity = Affirmative,
  candidate_proposition_id = AnalysisPropositionId(
    B,AFKMemberSpecializationPropositionBody(F,n0_literal,S,ell0)),
  candidate_goal_id = AnalysisGoalId(B,AFKMemberKnowledgeGoal(S,ell0)),
  inherited_hypothesis_context_id =
    GammaAFKMemberSpecializationId(F,n0_literal,S,ell0), and
  exact_quantified_witness_coordinates = []

Every law above also reconstructs the matching candidate_question_id,
exact_subjects, question_context, and exact_family_conclusion from that same
authenticated constructor match and requires byte equality with the derived
QualificationSubjectContext. It accepts no caller-supplied expected ID or
context and cannot consult a future judgment coordinate.

AnalysisQualificationProfileContracts = CanonicalKeySortedSeq [
  {FiniteSpecialSoundnessQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(FiniteSpecialSoundnessQualificationRef)> {
    subject_parametric_acceptance_law:
      FiniteSpecialSoundnessQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}},
  {AssumedExternalAllNQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(AssumedExternalAllNQualificationRef)> {
    subject_parametric_acceptance_law:
      AssumedExternalAllNQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}},
  {AssumedTheoremTruthQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(AssumedTheoremTruthQualificationRef)> {
    subject_parametric_acceptance_law:
      AssumedTheoremTruthQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}},
  {AFKFamilyApplicabilityQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(AFKFamilyApplicabilityQualificationRef)> {
    subject_parametric_acceptance_law:
      AFKFamilyApplicabilityQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}},
  {AFKFamilyInstanceCorrespondenceQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(AFKFamilyInstanceCorrespondenceQualificationRef)> {
    subject_parametric_acceptance_law:
      AFKFamilyInstanceCorrespondenceQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}},
  {AFKFamilyTransportQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(AFKFamilyTransportQualificationRef)> {
    subject_parametric_acceptance_law:
      AFKFamilyTransportQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}},
  {AFKMemberSpecializationQualificationRef,
   AnalysisQualificationSemanticsContract<
     ProfileOf(AFKMemberSpecializationQualificationRef)> {
    subject_parametric_acceptance_law:
      AFKMemberSpecializationQualificationAcceptanceLawRef,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef}}
]
```

The property profile owns finite special soundness and the assumed all-`n`
source declaration; the semantic transport profile owns applicability and
family-instance correspondence; the source-validation child owns assumed
theorem truth, family transport, and fixed-member specialization. The exact
declaration body and resolved contract are both authenticated before a result
may name a qualification. An absent row, duplicate tag, wrong-profile row, or
qualification whose family, polarity, or inherited context differs from the
resolved judgment refuses formation. `ExactInheritedConditionalQualificationRef`
is a requirement declaration only and cannot be substituted for any of these
seven actual-result qualifications. The deferred finite-extractor discharge
is inactive, so no actual-result qualification row is admitted for it.

The requirement declaration resolves separately:

```text
ExactInheritedConditionalAcceptanceLawRef =
  the exact property-profile
  AnalysisProfileLawRef<SubjectParametricQualificationAcceptanceLaw> that:
    authenticates the candidate's actual qualification through
      ResolvedAnalysisQualificationContract;
    requires that qualification's own subject-parametric law to accept the
      same candidate body, authenticated proposition, and derived
      QualificationSubjectContext;
    requires polarity = Affirmative; and
    rederives the exact family conclusion, inherited hypothesis context, and
      quantified-witness coordinates from that candidate, accepting no
      qualification law that erases a hypothesis or strengthens its conclusion

ExactInheritedConditionalRequirementResolverRef =
  the exact property-profile
  AnalysisProfileLawRef<QualificationRequirementToAcceptanceLawResolver> that
  maps only the complete declaration coordinate and body of
  ExactInheritedConditionalQualificationRef to
  ExactInheritedConditionalAcceptanceLawRef

CryptographicQualificationRequirementProfileContracts = CanonicalKeySortedSeq [
  {ExactInheritedConditionalQualificationRef,
   AnalysisQualificationRequirementSemanticsContract<
     ProfileOf(ExactInheritedConditionalQualificationRef)> {
     requirement_to_law_resolver:
       ExactInheritedConditionalRequirementResolverRef,
     failure_classification: CryptographicPropertyAttemptFailurePartitionRef
   }}
]
```

No actual-result qualification coordinate is accepted by tag equality with
the requirement. `QualificationRequirementAccepts` rederives the candidate
context and runs both the actual qualification law and this independently
resolved requirement law. The surrounding exact premise binding and paired
consumer/purpose contracts separately require the candidate proposition,
semantic basis, support, policy, consumer, and purpose expected by that use;
the requirement law does not receive or predict those future coordinates.

```text
AnalysisUseContract(P,accepted_kinds,qualification_requirement,attenuation,policy) =
  AnalysisUseSemanticsContract<P> {
    accepted_subject_and_result_kinds: accepted_kinds,
    required_qualification: qualification_requirement,
    capability_attenuation_law: attenuation,
    operation_policy_compatibility_law: policy,
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef
  }

AnalysisPropertyUseProfileContracts = CanonicalKeySortedSeq [
  {FiniteSpecialSoundnessConsumerRef,
   AnalysisUseContract(
     AnalysisCryptographicPropertyLanguageProfileId,
     [KOutOfNSpecialSoundness with FiniteSpecialSoundnessPurposeRef],
     ExactInheritedConditionalQualificationRef,
     one exact finite-property use only,exact finite-analysis policy)},
  {FiniteSpecialSoundnessPurposeRef,
   AnalysisUseContract(
     AnalysisCryptographicPropertyLanguageProfileId,
     [KOutOfNSpecialSoundness by FiniteSpecialSoundnessConsumerRef],
     ExactInheritedConditionalQualificationRef,
     no family or theorem transport,exact finite-analysis policy)}
]

AnalysisTransportUseProfileContracts = CanonicalKeySortedSeq [
  {AFKFamilyPropertyTransportConsumerRef,
   AnalysisUseContract(
     AnalysisAFKTransportLanguageProfileId,
     [
       AsymptoticKOutOfNSpecialSoundness with
         AFKTheoremSourcePropertyPurposeRef,
       TheoremApplicability with AFKExactTheoremFamilyTransportPurposeRef],
     ExactInheritedConditionalQualificationRef,
     single use by one exact `(AFKV2TheoremSchemaId,F)` transport,
     exact family-transport policy)},
  {AFKMemberSpecializationConsumerRef,
   AnalysisUseContract(
     AnalysisAFKTransportLanguageProfileId,
     [
       AdaptiveKnowledgeSoundnessQltN with
         AFKFamilyTargetSpecializationPurposeRef,
       FamilyInstanceCorrespondence with
         AFKExactFamilyMemberSpecializationPurposeRef],
     ExactInheritedConditionalQualificationRef,
     single use by one exact `(F,n0_literal,S,ell0)` specialization,
     exact member-specialization policy)},
  {AFKTheoremSourcePropertyPurposeRef,
   AnalysisUseContract(
     AnalysisAFKTransportLanguageProfileId,
     [
       AsymptoticKOutOfNSpecialSoundness by
         AFKFamilyPropertyTransportConsumerRef],
     ExactInheritedConditionalQualificationRef,
     source-property input only,exact family-transport policy)},
  {AFKExactTheoremFamilyTransportPurposeRef,
   AnalysisUseContract(
     AnalysisAFKTransportLanguageProfileId,
     [
       TheoremApplicability by AFKFamilyPropertyTransportConsumerRef],
     ExactInheritedConditionalQualificationRef,
     structural-applicability input only,exact family-transport policy)},
  {AFKFamilyTargetSpecializationPurposeRef,
   AnalysisUseContract(
     AnalysisAFKTransportLanguageProfileId,
     [
       AdaptiveKnowledgeSoundnessQltN by AFKMemberSpecializationConsumerRef],
     ExactInheritedConditionalQualificationRef,
     family-target input at one index only,exact member-specialization policy)},
  {AFKExactFamilyMemberSpecializationPurposeRef,
   AnalysisUseContract(
     AnalysisAFKTransportLanguageProfileId,
     [
       FamilyInstanceCorrespondence by AFKMemberSpecializationConsumerRef],
     ExactInheritedConditionalQualificationRef,
     pointwise-correspondence input only,exact member-specialization policy)}
]

The cryptographic property semantic-language profile contains exactly
`AnalysisPropertyUseProfileContracts`. The AFK semantic-transport profile contains
exactly `AnalysisTransportUseProfileContracts` and imports the property profile, so
it resolves `ExactInheritedConditionalQualificationRef` without copying or
reissuing that declaration. The theorem-source-validation child imports the
transport profile and may therefore resolve the member-specialization
consumer and purposes without a reverse import into the property profile.
Each entry is keyed by the complete resolved coordinate and declaration body,
not its display tag. Its fields are exact `AnalysisProfileLawRef` values in the
profile that owns the entry, not the explanatory phrases in the display. A
missing, extra supplied profile, cross-consumer, cross-purpose, cross-family,
weakened-qualification, or body-mismatched entry refuses use.

AnalysisNativeRule(rule_coordinate,payload) =
  NativeRuleSource(NativeRuleSchema {
    rule_coordinate: rule_coordinate,
    canonical_rule_payload:
      CanonicalValue<resolved and lifted payload type of rule_coordinate>(
        payload)
  })

ConcreteManifestReadPurposeRequirements(manifest_id) =
  CanonicalSeq [
    ConcreteReadPurpose {
      semantic_read_manifest_id: manifest_id,
      semantic_read_slot_ordinal: slot_ordinal,
      exact_purpose:
        AuthenticatedSemanticReadManifest(manifest_id).
          slots[slot_ordinal].read_purpose
    }
    for every slot_ordinal in the exact manifest slot order
  ]

FamilyManifestReadPurposeRequirements(manifest_schema_id) =
  CanonicalSeq [
    FamilyReadPurpose {
      family_read_manifest_schema_id: manifest_schema_id,
      family_read_slot_ordinal: slot_ordinal,
      exact_purpose:
        AuthenticatedAnalysisSourceProfile(
          AuthenticatedFamilyReadManifestSchema(manifest_schema_id).
            member_source_profile_id).
          slot_schemas[slot_ordinal].read_purpose
    }
    for every slot_ordinal in the exact abstract role-slot order
  ]

ExactCryptographicReadPurposes(concrete_manifests,family_manifest_schemas) =
  NormalizeReadPurposeRequirements(CanonicalConcat(
    ConcreteManifestReadPurposeRequirements(m)
      for each m in concrete_manifests,
    FamilyManifestReadPurposeRequirements(f)
      for each f in family_manifest_schemas))

SchnorrSpecialSoundnessSemanticBasisBody(S,Ext) =
  AnalysisSemanticBasisBody {
    family: KOutOfNSpecialSoundness,
    exact_question_id:
      AnalysisQuestionId(B,SchnorrSpecialSoundnessQuestion(S)),
    rule_source: AnalysisNativeRule(
      ExistentialExtractorIntroductionRuleRef,{
        experiment_profile_id:
          SchnorrSpecialSoundnessExperimentProfileId(S),
        extractor_profile_id: SchnorrDeterministicExtractorProfileId(S),
        extractor_quantifier_ordinal: 0,
        conclusion_family: KOutOfNSpecialSoundness
      }),
    exact_premise_schemas: CanonicalAppend(
      AllReachableHypothesisNodeRequirements(
        GammaSpecialId(S,Ext),GammaSpecialBody(S,Ext)),
      [ExactQuantifiedWitnessRequirement {
        witness_coordinate: Ext,
        exact_profile_id: SchnorrDeterministicExtractorProfileId(S),
        quantified_role: AnalysisQuantifiedWitnessRole {
          experiment_profile_id:
            SchnorrSpecialSoundnessExperimentProfileId(S),
          quantifier_ordinal: 0,
          expected_quantifier_kind: ExistsExtractor
        }
      }]),
    source_read_purposes: ExactCryptographicReadPurposes(
      [SchnorrRelationSemanticReadManifestId(S)],[]),
    conclusion_schema: SchnorrSpecialSoundnessGoal(S) with witness Ext,
    typed_transform_program:
      introduce the same Ext into the extractor existential and inherit
      GammaSpecialId(S,Ext) exactly once
  }

SchnorrSpecialSoundnessSemanticBasisId(S,Ext) =
  AnalysisSemanticBasisId(
    B, SchnorrSpecialSoundnessSemanticBasisBody(S,Ext))

SchnorrSpecialSoundnessSupportBody(
  S,Ext,exact_witness_binding,established_node_bindings,
  assumed_node_bindings,source_support) =
  AnalysisSupportInstantiationBody {
    semantic_basis_id: SchnorrSpecialSoundnessSemanticBasisId(S,Ext),
    proposition_id: AnalysisPropositionId(
      B, SchnorrSpecialSoundnessProposition(S,Ext)),
    exact_named_premise_ids: PremiseIdsOfProposition(proposition_id),
    non_hypothesis_premise_bindings:
      ExactNonHypothesisPremiseBindingMap(
        SchnorrSpecialSoundnessSemanticBasisId(S,Ext),
        SchnorrSpecialSoundnessSemanticBasisBody(S,Ext),
        [exact_witness_binding]),
    established_hypothesis_node_bindings: established_node_bindings,
    assumed_hypothesis_node_bindings: assumed_node_bindings,
    source_support_bindings: [ExactManifestSupportBinding {
      semantic_read_manifest_id:
        SchnorrRelationSemanticReadManifestId(S),
      source_support_coordinate: source_support
    }]
  }

SchnorrSpecialSoundnessSupportId(
    S,Ext,exact_witness_binding,established_node_bindings,
    assumed_node_bindings,source_support) =
  AnalysisId<"analysis.support-instantiation">(B,
    SchnorrSpecialSoundnessSupportBody(
      S,Ext,exact_witness_binding,established_node_bindings,
      assumed_node_bindings,source_support))

SchnorrSpecialSoundnessValidationBasisBody(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  ExactAnalysisValidationBasisBody(
    checker_contracts,translations,finite_controls,[],residual_trust_roots)

SchnorrSpecialSoundnessValidationBasisId(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  AnalysisId<"analysis.validation-basis">(B,
    SchnorrSpecialSoundnessValidationBasisBody(
      checker_contracts,translations,finite_controls,residual_trust_roots))

SchnorrSpecialSoundnessOperationPolicyBody(S,Ext) =
  ExactAnalysisOperationPolicyBody(
    AnalysisPropositionId(B,SchnorrSpecialSoundnessProposition(S,Ext)),
    CanonicalMap {
      FiniteSpecialSoundnessConsumerRef:
        CanonicalSingleton(FiniteSpecialSoundnessPurposeRef)
    },
    SchnorrSpecialSoundnessPolicyLawBundleRef)

SchnorrSpecialSoundnessOperationPolicyId(S,Ext) =
  AnalysisId<"analysis.operation-policy">(
    B,SchnorrSpecialSoundnessOperationPolicyBody(S,Ext))

SchnorrSpecialSoundnessJudgmentBody(
    S,Ext,support_id,validation_basis_id) =
  ExactAffirmativeAnalysisJudgmentBody(
    AnalysisPropositionId(B,SchnorrSpecialSoundnessProposition(S,Ext)),
    NoQuantitativeResult,
    SchnorrSpecialSoundnessSemanticBasisId(S,Ext),
    support_id,validation_basis_id,
    FiniteSpecialSoundnessQualificationRef,
    SchnorrSpecialSoundnessOperationPolicyId(S,Ext))

SchnorrSpecialSoundnessJudgmentId(
    S,Ext,support_id,validation_basis_id) =
  AnalysisId<"analysis.judgment-record">(B,
    SchnorrSpecialSoundnessJudgmentBody(
      S,Ext,support_id,validation_basis_id))

SchnorrSpecialSoundnessJudgmentSchema(S,Ext) = {
  exact_judgment_constructor: SchnorrSpecialSoundnessJudgmentId,
  exact_quantified_witness: Ext,
  result: Affirmative conditional KOutOfNSpecialSoundness inheriting exactly
    GammaSpecialId(S,Ext),
  live_capability_permission:
    FiniteSpecialSoundnessConsumerRef -> FiniteSpecialSoundnessPurposeRef
}
```

`SchnorrSpecialSoundnessPolicyLawBundleRef` is the one exact property-profile
`AnalysisOperationPolicyLawBundle` admitted for this result class. It requires
fresh single-invocation capabilities, conditional-result disclosure, refusal
of unknown questions, portable persistence only when every source coordinate
is portable, and exact cold replay. None of those explanatory phrases is
encoded; the five exact law refs in the bundle are.

The established and assumed hypothesis-node maps must be disjoint and their
domains must partition every and only the seven reachable DAG nodes. Each established entry supplies an
exact affirmative premise capability; each assumed entry names the same goal
ID without pretending to establish it. The native rule may therefore produce a
conditional source judgment even when fixed-extractor correctness remains an
explicit assumption; it never mints an affirmative universal-correctness
judgment from finite evaluation. Failure of one candidate still refutes only
that candidate, never the existential family.

### 3.2 Named premises of the relation-bound Fresh question

The [Analysis model](analysis-model.md#41-one-identity-algebra) gives every
assumption a question consumes a named, identity-bearing body. This profile
owns the concrete bodies below: what a Fresh challenge is drawn from, how a
provider's outcome carrier maps the PIR outcome partition and which of its
lanes the provider does not model, the completion premise a statement over
the whole partition then needs, and the relation and Plan premises of the
finite Schnorr question.

```text
NamedHypothesisArgumentSchema<AnalysisCryptographicPropertyLanguageProfileId, K> =
    [ coordinate: PIRPublicCoinLawCoordinate,
      distribution_model: AnalysisDistributionProfileId ]
        when K = FreshPublicCoinDistribution
  | [ coordinate: PIRConstructionPremiseCoordinate(_, SamplerAdequacy),
      oracle_model: AnalysisDistributionProfileId,
      form: SamplerAdequacyForm ]
        when K = FiatShamirSamplerAdequacy
  | [ coordinate: PIRConstructionPremiseCoordinate(_, OracleProcess),
      oracle_model: AnalysisDistributionProfileId ]
        when K = FiatShamirOracleProcess
  | [ coordinate: PIRProtocolOutcomePartitionCoordinate,
      provider: AnalysisProviderDeclaration<AnalysisCryptographicPropertyLanguageProfileId> ]
        when K = OperationalCompletion
  | [ coordinate: PIRPlanRecipeCoordinate ]
        when K = HonestCommit or K = HonestRespond

PremiseIdOf(body: AnalysisNamedPremiseBody<P,K>) =
  AnalysisNamedPremiseId<P,K>(B, body)

FreshSamplingHypothesis =
  ExactNamedHypothesis<AnalysisCryptographicPropertyLanguageProfileId,
                       FreshPublicCoinDistribution> whose canonical
  arguments are [ coordinate: PIRPublicCoinLawCoordinate(
  ProtocolDeclarationRef<"pir.public-coin-law">),
  distribution_model: AnalysisDistributionProfileId ]: the challenge at that
  coordinate is drawn from that model, fresh at each occurrence and
  independent of the prior prover view

FreshPublicCoinDistributionPremise(
    law_coordinate: ProtocolDeclarationRef<"pir.public-coin-law">,
    distribution_model: AnalysisDistributionProfileId,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId,
                           FreshPublicCoinDistribution> {
    kind: exactly FreshPublicCoinDistribution,
    coordinate: PIRPublicCoinLawCoordinate(law_coordinate),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's FreshSamplingHypothesis declaration,
      canonical_arguments: [PIRPublicCoinLawCoordinate(law_coordinate),
                            distribution_model]
    }),
    source,
    evidence_depth,
    model_scope: FreshChallengeOnly
  }

ProviderOutcomeCarrierPremise(
    P: ProtocolId,
    provider: AnalysisProviderDeclaration<AnalysisCryptographicPropertyLanguageProfileId>,
    carrier: AnalysisProfileLawRef<AnalysisCryptographicPropertyLanguageProfileId,
                                   ClosedProviderCarrier>,
    total_map: CanonicalMap<ProtocolOutcomeLane(P),
                            AnalysisProviderLaneImage<carrier>>,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId,
                           ProviderOutcomeCarrierMap> {
    kind: exactly ProviderOutcomeCarrierMap,
    coordinate: PIRProtocolOutcomePartitionCoordinate(P),
    bound_model_or_hypothesis: BoundProviderOutcomeCarrierMap {
      provider,
      protocol_outcome_partition: PIRProtocolOutcomePartitionCoordinate(P),
      provider_carrier: carrier,
      total_lane_map: total_map
    },
    source,
    evidence_depth,
    model_scope: ExactSubjectsOnly([P])
  }

OperationalCompletionHypothesis =
  ExactNamedHypothesis<AnalysisCryptographicPropertyLanguageProfileId,
                       OperationalCompletion> whose canonical arguments are
  [ coordinate: PIRProtocolOutcomePartitionCoordinate(P),
    provider: AnalysisProviderDeclaration<AnalysisCryptographicPropertyLanguageProfileId> ]:
  every run of P in the environment of the question ends in a lane of
  provider.modelled_lanes

OperationalCompletionPremise(
    P: ProtocolId,
    provider: AnalysisProviderDeclaration<AnalysisCryptographicPropertyLanguageProfileId>,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId,
                           OperationalCompletion> {
    kind: exactly OperationalCompletion,
    coordinate: PIRProtocolOutcomePartitionCoordinate(P),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's OperationalCompletionHypothesis declaration,
      canonical_arguments: [PIRProtocolOutcomePartitionCoordinate(P), provider]
    }),
    source,
    evidence_depth,
    model_scope: ExactSubjectsOnly([P])
  }

PlanOf(S: AnalysisSubjectTuple) = S.fresh_prover_plan_id

SchnorrNamedPremiseRequirements(S: AnalysisSubjectTuple) =
  CanonicalSortedUniqueSeq [
    { slot: "fresh-coin", kind: FreshPublicCoinDistribution,
      coordinate: PIRPublicCoinLawCoordinate(SchnorrFreshLawRef(S)) },
    { slot: "relation", kind: RelationPredicate,
      coordinate:
        RelationsModelEvaluatorCoordinate(S.relation_semantic_model_id) },
    { slot: "witness", kind: WitnessType,
      coordinate: RelationsWitnessPlanJoinCoordinate(
        S.relation_interface_id, 0,
        S.relation_axis_ingress.fresh.plan_witness_binding_id, 0) },
    { slot: "prover-state", kind: ProverPrivateState,
      coordinate: PIRPlanStateCoordinate(PlanOf(S), StrategyStateSlotRef 0) },
    { slot: "commit", kind: HonestCommit,
      coordinate: PIRPlanRecipeCoordinate(
        PlanOf(S), ProverDecisionPointRef 0, RecipeNodeRef 0) },
    { slot: "respond", kind: HonestRespond,
      coordinate: PIRPlanRecipeCoordinate(
        PlanOf(S), ProverDecisionPointRef 2, RecipeNodeRef 0) }
  ]

ProviderJudgmentRequirements(P: ProtocolId) =
  CanonicalSortedUniqueSeq [
    { slot: "provider-outcome", kind: ProviderOutcomeCarrierMap,
      coordinate: PIRProtocolOutcomePartitionCoordinate(P) }
  ]

SchnorrExtractorPremiseRequirements(S: AnalysisSubjectTuple) =
  the "relation" and "witness" entries of SchnorrNamedPremiseRequirements(S)

RelationPredicateBindingLaw =
  ExactModelBindingLaw<AnalysisCryptographicPropertyLanguageProfileId, RelationPredicate>:
  the relation semantic model at the coordinate is the predicate the named
  subject evaluates

WitnessTypeBindingLaw =
  ExactModelBindingLaw<AnalysisCryptographicPropertyLanguageProfileId, WitnessType>:
  the witness type at the join coordinate is the named subject's private
  witness type

ProverPrivateStateBindingLaw =
  ExactModelBindingLaw<AnalysisCryptographicPropertyLanguageProfileId, ProverPrivateState>:
  the Plan's persistent state slot at the coordinate is the named subject's
  private state

HonestCommitHypothesis =
  ExactNamedHypothesis<AnalysisCryptographicPropertyLanguageProfileId, HonestCommit> whose
  canonical arguments are [ coordinate: PIRPlanRecipeCoordinate ]: the honest
  prover's commitment is computed by the recipe node at that coordinate

HonestRespondHypothesis =
  ExactNamedHypothesis<AnalysisCryptographicPropertyLanguageProfileId, HonestRespond> whose
  canonical arguments are [ coordinate: PIRPlanRecipeCoordinate ]: the honest
  prover's response is computed by the recipe node at that coordinate

SchnorrPremiseScope(S: AnalysisSubjectTuple) =
  ExactSubjectsOnly(SchnorrSpecialSoundnessQuestion(S).exact_subjects)

SchnorrExtractorPremiseScope(S: AnalysisSubjectTuple, Ext: PortableAlgorithmRef) =
  ExactSubjectsOnly(SchnorrFixedExtractorWorksQuestion(S, Ext).exact_subjects)

RelationPredicatePremise(
    S: AnalysisSubjectTuple,
    scope: AnalysisPremiseModelScope,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId, RelationPredicate> {
    kind: exactly RelationPredicate,
    coordinate: RelationsModelEvaluatorCoordinate(S.relation_semantic_model_id),
    bound_model_or_hypothesis: BoundModel(S.relation_semantic_model_id,
      AnalysisLawTerm {
        law_ref: the profile's RelationPredicateBindingLaw declaration,
        canonical_arguments:
          [RelationsModelEvaluatorCoordinate(S.relation_semantic_model_id),
           S.relation_semantic_model_id]
      }),
    source,
    evidence_depth,
    model_scope: scope
  }

WitnessJoinCoordinate(S: AnalysisSubjectTuple) =
  RelationsWitnessPlanJoinCoordinate(
    S.relation_interface_id, 0,
    S.relation_axis_ingress.fresh.plan_witness_binding_id, 0)

WitnessTypePremise(
    S: AnalysisSubjectTuple,
    scope: AnalysisPremiseModelScope,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId, WitnessType> {
    kind: exactly WitnessType,
    coordinate: WitnessJoinCoordinate(S),
    bound_model_or_hypothesis: BoundModel(S.relation_interface_id,
      AnalysisLawTerm {
        law_ref: the profile's WitnessTypeBindingLaw declaration,
        canonical_arguments: [WitnessJoinCoordinate(S), S.relation_interface_id]
      }),
    source,
    evidence_depth,
    model_scope: scope
  }

ProverPrivateStatePremise(
    S: AnalysisSubjectTuple,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId, ProverPrivateState> {
    kind: exactly ProverPrivateState,
    coordinate: PIRPlanStateCoordinate(PlanOf(S), StrategyStateSlotRef 0),
    bound_model_or_hypothesis: BoundModel(PlanOf(S),
      AnalysisLawTerm {
        law_ref: the profile's ProverPrivateStateBindingLaw declaration,
        canonical_arguments:
          [PIRPlanStateCoordinate(PlanOf(S), StrategyStateSlotRef 0), PlanOf(S)]
      }),
    source,
    evidence_depth,
    model_scope: SchnorrPremiseScope(S)
  }

HonestCommitPremise(
    S: AnalysisSubjectTuple,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId, HonestCommit> {
    kind: exactly HonestCommit,
    coordinate: PIRPlanRecipeCoordinate(
      PlanOf(S), ProverDecisionPointRef 0, RecipeNodeRef 0),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's HonestCommitHypothesis declaration,
      canonical_arguments: [PIRPlanRecipeCoordinate(
        PlanOf(S), ProverDecisionPointRef 0, RecipeNodeRef 0)]
    }),
    source,
    evidence_depth,
    model_scope: SchnorrPremiseScope(S)
  }

HonestRespondPremise(
    S: AnalysisSubjectTuple,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId, HonestRespond> {
    kind: exactly HonestRespond,
    coordinate: PIRPlanRecipeCoordinate(
      PlanOf(S), ProverDecisionPointRef 2, RecipeNodeRef 0),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's HonestRespondHypothesis declaration,
      canonical_arguments: [PIRPlanRecipeCoordinate(
        PlanOf(S), ProverDecisionPointRef 2, RecipeNodeRef 0)]
    }),
    source,
    evidence_depth,
    model_scope: SchnorrPremiseScope(S)
  }

ConstructionSamplerAdequacyHypothesis =
  ExactNamedHypothesis<AnalysisCryptographicPropertyLanguageProfileId,
                       FiatShamirSamplerAdequacy> whose canonical arguments
  are [ coordinate: PIRConstructionPremiseCoordinate(T, SamplerAdequacy),
  oracle_model: AnalysisDistributionProfileId, form: SamplerAdequacyForm ]:
  the construction's challenge sampler over that oracle model is adequate in
  the named form

ConstructionOracleProcessHypothesis =
  ExactNamedHypothesis<AnalysisCryptographicPropertyLanguageProfileId,
                       FiatShamirOracleProcess> whose canonical arguments are
  [ coordinate: PIRConstructionPremiseCoordinate(T, OracleProcess),
  oracle_model: AnalysisDistributionProfileId ]: the oracle process the
  experiment assumes over that model is the one the construction realizes

SamplerAdequacyFormOf(T: TranscriptConstructionId) =
    ExactTotal
      when every rule in T's challenge_rules has maximum_draws = 1
  | RetryWithExhaustion(the maximum of maximum_draws over T's challenge_rules)
      otherwise;
  the form is read from the construction's identity-bearing challenge rules
  (docs-next/pir/fiat-shamir.md), and under ExactTotal the hypothesis asserts
  that every one-shot rule's acceptance holds on its single draw

SamplerAdequacyForm =
    ExactTotal
  | RetryWithExhaustion(maximum_draws: Natural)

FiatShamirConstructionSamplerPremise(
    T: TranscriptConstructionId,
    oracle_model: AnalysisDistributionProfileId,
    form: SamplerAdequacyForm,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId,
                           FiatShamirSamplerAdequacy> {
    kind: exactly FiatShamirSamplerAdequacy,
    coordinate: PIRConstructionPremiseCoordinate(T, SamplerAdequacy),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's ConstructionSamplerAdequacyHypothesis declaration,
      canonical_arguments: [PIRConstructionPremiseCoordinate(T, SamplerAdequacy),
                            oracle_model, form]
    }),
    source,
    evidence_depth,
    model_scope: OracleModelOnly(oracle_model)
  }

FiatShamirConstructionOracleProcessPremise(
    T: TranscriptConstructionId,
    oracle_model: AnalysisDistributionProfileId,
    source: AnalysisNamedPremiseSource<AnalysisCryptographicPropertyLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisCryptographicPropertyLanguageProfileId,
                           FiatShamirOracleProcess> {
    kind: exactly FiatShamirOracleProcess,
    coordinate: PIRConstructionPremiseCoordinate(T, OracleProcess),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's ConstructionOracleProcessHypothesis declaration,
      canonical_arguments: [PIRConstructionPremiseCoordinate(T, OracleProcess),
                            oracle_model]
    }),
    source,
    evidence_depth,
    model_scope: OracleModelOnly(oracle_model)
  }

FiatShamirConstructionPremiseRequirements(T, oracle_model) =
  CanonicalSortedUniqueSeq [
    { slot: "sampler", kind: FiatShamirSamplerAdequacy,
      coordinate: PIRConstructionPremiseCoordinate(T, SamplerAdequacy) },
    { slot: "oracle-process", kind: FiatShamirOracleProcess,
      coordinate: PIRConstructionPremiseCoordinate(T, OracleProcess) }
  ]

SchnorrNamedPremiseBindings(S: AnalysisSubjectTuple) =
  the binding map IntakeAnalysisNamedPremises(
    SchnorrSpecialSoundnessQuestion(S), supplied) forms, where supplied
  binds each slot to PremiseIdOf of the exact body below:
    "fresh-coin"   -> FreshPublicCoinDistributionPremise(
                        SchnorrFreshLawRef(S), AnalysisChallengeDomainId(S)'s
                        exact finite uniform model,
                        CandidateOwnerCoordinate(S.fresh_protocol_id),
                        SourceGroundedMapping),
    "relation"     -> RelationPredicatePremise(S, SchnorrPremiseScope(S),
                        CandidateOwnerCoordinate(S.relation_semantic_model_id),
                        FrozenExecutableFalsification),
    "witness"      -> WitnessTypePremise(S, SchnorrPremiseScope(S),
                        CandidateOwnerCoordinate(S.relation_interface_id),
                        FrozenExecutableFalsification),
    "prover-state" -> ProverPrivateStatePremise(S,
                        CandidateOwnerCoordinate(PlanOf(S)),
                        FrozenExecutableFalsification),
    "commit"       -> HonestCommitPremise(S,
                        CandidateOwnerCoordinate(PlanOf(S)),
                        FrozenExecutableFalsification),
    "respond"      -> HonestRespondPremise(S,
                        CandidateOwnerCoordinate(PlanOf(S)),
                        FrozenExecutableFalsification)

SchnorrExtractorPremiseBindings(S: AnalysisSubjectTuple, Ext: PortableAlgorithmRef) =
  the binding map IntakeAnalysisNamedPremises(
    SchnorrFixedExtractorWorksQuestion(S, Ext), supplied) forms, where
  supplied binds each slot to PremiseIdOf of the exact body below; the
  bodies differ from the relation question's only in their scope, because an
  ExactSubjectsOnly premise admits exactly the question whose subjects it
  names and the extractor question adds Ext to its subjects:
    "relation"     -> RelationPredicatePremise(S,
                        SchnorrExtractorPremiseScope(S, Ext),
                        CandidateOwnerCoordinate(S.relation_semantic_model_id),
                        FrozenExecutableFalsification),
    "witness"      -> WitnessTypePremise(S,
                        SchnorrExtractorPremiseScope(S, Ext),
                        CandidateOwnerCoordinate(S.relation_interface_id),
                        FrozenExecutableFalsification)

FiatShamirConstructionPremiseBindings(
    S: AnalysisSubjectTuple,
    ell0: StatementLength(AnalysisStatementType(S))) =
  the binding map IntakeAnalysisNamedPremises(
    AFKMemberKnowledgeQuestion(S, ell0), supplied) forms, where supplied binds
    each slot to PremiseIdOf of the exact body below:
    "sampler"        -> FiatShamirConstructionSamplerPremise(
                          S.transcript_construction_id,
                          AFKClassicalRandomOracleProfileId(S),
                          SamplerAdequacyFormOf(S.transcript_construction_id),
                          CandidateOwnerCoordinate(S.transcript_construction_id),
                          SourceGroundedMapping),
    "oracle-process" -> FiatShamirConstructionOracleProcessPremise(
                          S.transcript_construction_id,
                          AFKClassicalRandomOracleProfileId(S),
                          CandidateOwnerCoordinate(S.transcript_construction_id),
                          SourceGroundedMapping)
```

A question over a Fresh Protocol requires exactly one
`FreshPublicCoinDistribution` premise for every `pir.public-coin-law`
coordinate it selects; the nominal declaration is the hook, and the premise
is what binds a distribution to it. A question over a Fiat--Shamir Protocol
selects no such premise: its challenge value is fixed operationally by the
construction, and what it consumes are the family premises of
[Section 7.3](#73-family-premises). A `ProviderOutcomeCarrierMap` premise
requires `total_map` to have exactly the profile-qualified partition of `P` as
its domain: five lanes for a Fresh or duplex-sponge Protocol, six for a
canonical-framed one. Its value at a lane is `Image(v)` exactly when the
provider declaration lists the lane in `modelled_lanes` and `Unmodelled`
otherwise; a lane absent from the map, an `Image` at a lane the provider
does not model, or `Unmodelled` at one it does is `Malformed`. A lane is
never collapsed onto the image of another: a provider whose verifier returns
a Boolean and whose execution cannot fail to complete models `Accepted` and
`Rejected` and no other lane, and its map says so rather than sending
noncompletion to `false`. The provider is an exact profile law declaration
naming one external formal system at one pinned source, published by this
profile's declaration catalog; until one is published no provider-map
premise can be formed. A provider statement transports to the PIR event that
is the union of the lanes whose images lie in the statement's event, and to
nothing outside `modelled_lanes`; a question whose stated PIR event is not
such a union, one that says every run is accepted, for instance, carries an
`OperationalCompletion` requirement in its family's requirement sequence,
and forms without it only as `CannotAnswer`. Transport preserves measure as
well as events: the transported statement's probability is the mass that the
run's subdistribution of Section 3.3 of the Analysis model gives the PIR
event, with the mass of `Unmodelled` lanes and of missing runs left where it
is; a provider statement stated as a probability conditional on completion,
or on the modelled lanes, transports only when the conditioning event is
itself a lane union whose mass the statement also fixes or when an
`OperationalCompletion` premise makes that mass one, and never by
renormalizing over the lanes the provider models.

`SchnorrNamedPremiseRequirements(S)` is the exact premise requirement
sequence of the relation-bound Fresh question over `S`, fixed by
`NamedPremiseRequirementsOf` for that family; the fixed-extractor question
carries its relation and witness entries, the concrete adaptive
Fiat--Shamir question carries the construction premises of Section 3.2, and
every other family of this profile and of the transport profile, the source
premise families, asymptotic special soundness, theorem truth, theorem
applicability, and family-instance correspondence, fixes the empty
requirement sequence, because their assumptions are hypothesis nodes. The relation predicate, the
witness type, and the Prover's private state bind by `BoundModel` to the
exact owner coordinate each names: the semantic model's evaluator, the join
of the relation interface's first private witness with the Plan witness
binding's first edge, and the Plan's first persistent state slot. The honest
commit and respond bind by `BoundHypothesis` to the recipe nodes of the
Plan's first and third decisions: that the provider's operations correspond
to those recipes is an assumption, not a model coordinate. Their evidence
depth records the reproducible selection and mutation evidence that
accompanies the binding and establishes no relation truth, algorithm honesty,
or provider correspondence. A provider judgment over a Protocol adds
`ProviderJudgmentRequirements(P)` to its family's requirement sequence; the
relation-bound Fresh question does not carry it, so it forms before any
provider is declared.

## 4. Classical adaptive Fiat--Shamir experiment

### 4.1 Adversary and quantifier order

The theorem target is classical and adaptive in the Statement. Its native AFK
quantifiers range over one asymptotic protocol family, not over the finitely
many lengths admitted by one Foundation `ValueType`. The exact family profile is formed
in Section 4.4. Sections 4.1--4.3 first define the member-level types,
probability spaces, oracle law, maps, and fixed-length specialization reused by
that family. The selected family uses one theorem-local finite cardinality `N`,
requires `N_F(n) = N` for every `n`, and selects the explicit `0 <= Q < N`
query subprofile so its knowledge-error term inhabits `[0,1]` without a silent
cap; it does not claim the full all-`Q` property. Its native coupling shape is:

```text
there exists one positive polynomial q_KS
there exists one uniform black-box extractor algorithm E
for every statement length/security parameter n
for every admitted hard query bound Q
for every adaptive Q-query random-oracle prover P^a
  whose output Statement x has |x| = n:

  prover experiment:
    in its own probability space, sample the coins of P^a, V, and RO
    run input-free P^a through only the typed RO-query interface
    P^a outputs (Statement x, proof pi, arbitrary auxiliary output aux)
    compute verifier output v from the exact FS verifier

  extractor experiment:
    in a separate probability space, run E with input n and black-box oracle
      access to P^a, using only the theorem-granted lazy-sampling,
      programming, rerun, and oracle interfaces
    output (x, pi, aux, v, Witness w)

  Law_prover(x, pi, aux, v) = Law_extractor(x, pi, aux, v)
  epsilon(P^a) = Pr_prover[v = Accept]
  Pr_extractor[v = Accept and R(x, w)]
    >= (epsilon(P^a) - kappa_FS(n, Q, N)) / q_KS(n)
```

The Statement and `aux` are prover outputs, not outer inputs or samples. The
positive polynomial and extractor algorithm are fixed before `n`, `Q`, the
prover, either probability space, and either oracle are selected. `E` is one
uniform algorithm receiving black-box access to whichever `P^a` is quantified;
this is not `for all P^a, there exists E_P`. The algorithm may not take `Q`,
`epsilon`, prover code, or a hidden oracle table as advice. Its proven resource
bound may nevertheless be expressed in `n` and the actual hard query bound
`Q`. AFK places no running-time restriction on `P^a`; each black-box invocation
is counted as one extractor step. This absence of a time bound does not admit a
partial, nonreturning prover: the selected strategy ABI must return one
well-typed `(x, pi, aux)` on every admitted run. A module that can diverge or
leave missing probability mass is outside this AFK prover class. No bound is
placed on how much computation a returning invocation performs.

`P^a` may be randomized in the outer Definition-10 experiment. For one exact
theorem-granted extractor invocation, its initially sampled coin tape is fixed
before extractor interaction, yielding one deterministic next-message
strategy. Each authorized sibling run starts again from the authenticated root
frame with that same tape. A new extractor invocation receives a fresh tape
and a fresh lazy-function table; neither lineage may be imported from an older
invocation. Resampling prover coins among siblings, or retaining a table across
extractor invocations, is outside this profile. This is a restricted root-rerun
law, not ambient authority to rewind an arbitrary intermediate state.

The full distribution equality across the two probability spaces,
failure/abort treatment, input-length coordinate, and native success inequality
are part of the target `AnalysisExperimentProfile` and proposition identity,
not an uninterpreted citation field. An adversary gets only the typed random-
oracle query capability, never the hidden table. The theorem-granted extractor
may receive exactly the programming, lazy-sampling, and rerun capabilities
stated by that schema; those capabilities are not PIR replay and are unavailable
to ordinary strategies.

The resource basis separately counts adversary random-oracle queries,
extractor/prover invocations, verifier invocations, and expected time. The
query parameter `Q` is an exact natural with a declared scope; a counter with a
different owner or scope cannot substitute.

The dependent prover domain and the two probability spaces are explicit:

```text
AFKAdversaryRandomOracleQueryOperationRef,
AFKAdversaryBlackBoxInvocationOperationRef,
AFKFamilyAdversaryRandomOracleQueryOperationRef, and
AFKFamilyAdversaryBlackBoxInvocationOperationRef
  = four pairwise-distinct exact declarations under
    AnalysisProfileDeclarationRef<"analysis.resource-operation">

AFKClassicalRandomOracleProfileBody(S: AnalysisSubjectTuple) = {
  output_type: ModelValue(AnalysisChallengeDomainId(S)),
  exact_support_predicate:
    membership in AnalysisChallengeDomainId(S),
  exact_probability_mass_or_measure_law:
    repeated indices return the same value and every first query at a new index
    returns a jointly independent uniform model value, including adaptively
    chosen and off-image indices,
  parameter_and_security_parameter_coordinates:
    [S,StatementLength(AnalysisStatementType(S))],
  independence_and_correlation_declarations:
    hidden table belongs to the experiment; ordinary P^a and V receive only
    query capability; E receives exactly the selected simulation/programming
    capability,
  sampling_or_oracle_denotation:
    one total lazy function from every admitted AFKRandomOracleIndex(S) to the
    exact finite model values with query ABI
    `Query(AFKRandomOracleIndex(S)) -> ModelValue(AnalysisChallengeDomainId(S))`,
  failure_and_nontermination_law: total and failure-free
}

AFKClassicalRandomOracleProfileId(S: AnalysisSubjectTuple) =
  AnalysisDistributionProfileId(
    B, AFKClassicalRandomOracleProfileBody(S))

AFKRandomOracleQueryABI(S) =
  QueryCapabilityABI(AFKClassicalRandomOracleProfileId(S))

AFKAdversaryROQueryResourceDimension(S) = ResourceDimension {
  operation_role: AFKAdversaryRandomOracleQueryOperationRef,
  value_sort: Nat,
  owner_subjects: CanonicalAppend(
    AFKTargetSubjectProjection(S),[AFKClassicalRandomOracleProfileId(S)]),
  dependent_parameter_schema: [],
  capability_abi_or_algorithm_schema: AFKRandomOracleQueryABI(S),
  lifetime_scope: one exact prover experiment probability-space instance,
  aggregation: Sum,
  exact_counter_event:
    every invocation of that capability, including repeats and off-image calls
}

AFKAdversaryROQueryCount(S) =
  QueryCount<AFKAdversaryROQueryResourceDimension(S)>

AFKAdaptiveQQueryProverProfileBody(S: AnalysisSubjectTuple) = {
  role: adaptive Fiat--Shamir prover,
  dependent_parameter_schema: [
    n: StatementLength(AnalysisStatementType(S)),
    Q: AFKAdversaryROQueryCount(S) with 0 <= Q <
      ModelCardinality(AnalysisChallengeDomainId(S))
  ],
  strategy_abi: input-free total-output module parameterized by prior n and Q,
  private_state_type: opaque prover-owned state,
  initial_advice_type: Unit,
  allowed_views:
    exact coordinate projection declared by AFKFixedPublicSetupBody(S),
  allowed_oracles_and_capabilities: [AFKRandomOracleQueryABI(S)],
  legal_move_relation: typed RO queries followed by one (x,pi,aux) output,
  stop_and_noncompletion_law: exactly one well-typed output; divergence absent,
  resource_dimensions: [AFKAdversaryROQueryResourceDimension(S)]
}

AFKFixedAdversaryInvocationCapabilityABILawRef and
AFKFixedROSimulationProgrammingCapabilityABILawRef
  = two pairwise-distinct exact
    `AnalysisProfileLawRef<AnalysisCryptographicPropertyLanguageProfileId,
                           CapabilityABI>` values. Their profile-local
    ordinals, and therefore their canonical encoded order, are the displayed
    order. The first declaration owns the black-box invocation ABI for the
    already selected fixed prover strategy; the second owns the exact lazy
    random-oracle simulation and programming ABI. Neither ref is a
    subject-authored ID or a Protocol replay capability.

AFKExtractorProfileBody(S: AnalysisSubjectTuple) = {
  input_and_output_types: {
    inputs: [StatementLength(AnalysisStatementType(S))],
    outputs: [AnalysisStatementType(S), AFKProofType(S), BitString,
              TerminalVerdict, AnalysisWitnessType(S)]
  },
  private_state_and_randomness_types:
    [extractor state, extractor coins, lazy random-function state],
  allowed_source_and_oracle_capabilities:
    [AFKFixedAdversaryInvocationCapabilityABILawRef,
     AFKFixedROSimulationProgrammingCapabilityABILawRef],
  counterfactual_rights: [ProgramSibling, Rerun],
  state_preservation_relation:
    same-index consistency except exact programmed points under the contract,
  output_distribution_preservation_relation:
    IdenticalMarginalLaw on (x,pi,aux,v),
  witness_success_relation:
    v = Accept and RelationHolds(S.relation_instance_id,x,w),
  termination_and_asymptotic_resource_law:
    for a concrete member, only the exact expected-call/resource proposition;
    this profile makes no asymptotic-uniformity claim,
  counterfactual_capability_contract_and_property_family_scope: {
    counterfactual_capability_contract:
      Analysis-owned classical lazy-RO programming and root-rerun interface;
      an accepted sibling pair is derived and never granted as a capability,
    property_family_scope: AdaptiveKnowledgeExtractionAtFixedLengthQltN
  }
}
```

The counterfactual interface is the following closed transition algebra. Its
capability preimage contains these operational laws and no paper locator,
theorem citation, or source-validation metadata:

```text
BeginExtractorExperiment(N,Q,strategy_root,invocation_nonce,tape_nonce)
  requires N >= 2 and 0 <= Q < N
  derives a nonrecursive ExperimentId committing the capability contract,
    invocation nonce, independent strategy-root and tape commitments, N, and Q
  derives experiment-qualified strategy-root, tape, and table lineages
  creates an empty immutable shared table and no baseline

Baseline(state,calls,fresh_draws,source,profile,correspondence,transcript)
  records exactly one supplied finite call trace under the committed root and
    tape lineages; it does not execute or authenticate a generic strategy
  counts every adaptive-prover oracle call, including repeat and off-image
  requires the completed adaptive-prover call count to remain at most Q and,
    once Q calls have completed, refuses the next attempted prover call before
    executing it; verifier-owned calls do not spend this Q
  derives the unique PIR-owned challenge-query carrier from the Statement and
    commitment and requires its observed answer to equal transcript.challenge
  internally evaluates the exact bounded Schnorr Check and Terminal rules
  only then registers immutable acceptance and run receipts and issues
    ProgramSibling authority for this experiment

ProgramSibling(state,program_capability,c')
  requires state to be the process-local current occurrence for ExperimentId
  requires c' in C_N and distinct from every value already tried
  programs only the baseline target and does not mutate the shared base table
  spends neither an adversary query nor an adversary invocation
  produces one immutable programmed frame and authority for its exact Rerun
  supersedes the prior state occurrence after the transition succeeds

Rerun(state,rerun_capability,calls,fresh_draws,
      source,profile,correspondence,transcript)
  records another supplied finite call trace under the same committed root and
    tape lineages; it does not execute or authenticate a generic strategy
  requires and then supersedes the process-local current state occurrence
  overlays c' only at the programmed target
  preserves every existing non-target answer, lazily extends the shared
    non-target table, and globally consumes its process-local rerun authority
    after success so even an older immutable state cannot reuse it
  resets Q accounting for this complete adversary invocation and records its
    exact before/after table-state identities and invocation ordinal
  derives the same exact query carrier, joins c' to transcript.challenge, and
    internally registers acceptance only after exact bounded Check and Terminal

AcceptedSiblingPair(source,profile,baseline,rerun)
  authenticates both process-local run and verifier-acceptance receipts
  requires the same experiment, root, tape lineage, table lineage, and exact
    query target, then applies the exact admitted Schnorr pair predicate to
    both retained full transcripts
  canonicalizes the two full transcripts and corresponding frame identities
  grants no further counterfactual-transition or replay authority
```

The shared table is scoped to one exact extractor invocation. It may grow as
successive sibling reruns encounter new non-target indices, so later siblings
must see those answers, but a new `BeginExtractorExperiment` starts a distinct
lineage. Exactly one state occurrence per ExperimentId is process-locally
current; every successful transition supersedes its predecessor, so an older
immutable value cannot fork or revert the persistent lazy table. Capabilities
and receipts are process-local authenticated occurrences; they are not
portable evidence. Strategy-root and tape commitments express
lineage only: this finite instrument accepts caller-supplied call traces and
does not establish that they came from one adaptive prover strategy. The
adaptive-process correspondence therefore remains an external premise. The
transition algebra is classical and finite. It makes no generic adversary-
execution, rewinding, quantum-random-oracle, concrete-hash, or PIR `ReplayRun`
claim. Changing only source locators rotates source validation and its
consumers; changing any operational law above rotates the capability, process,
experiment, and all downstream semantic identities. Neither change rotates the
imported theorem statement digest, theorem-truth goal, or theorem proposition.

```text
AdaptiveQQueryProver(S, n, Q, RO_ABI) = {
  ordinary_inputs: [],
  ambient_instance: AFKFixedPublicSetupId(S),
  capabilities: [AFKRandomOracleQueryABI(S)],
  output: (x: AnalysisStatementType(S), pi: AFKProofType(S), aux: BitString),
  output_refinement: StatementLength(x) = n,
  query_refinement: AllROQueriesIncludingOffImage(P^a) <= Q,
  extractor_rerun_refinement:
    one initially sampled prover coin tape is fixed into a deterministic
    next-message strategy and retained across every extractor rerun,
  completion: total-output with probability mass 1,
  runtime_bound: none
}

AFKProverExperimentBody(S, n, Q, P^a) = {
  probability_space: ProverSpace,
  owned_randomness: [P^a coins, verifier coins, lazy-sampled RO table],
  run: input-free P^a then exact verification by S.fiat_shamir_protocol_id,
  output: (x: AnalysisStatementType(S),
           pi: AFKProofType(S), aux: BitString,
           v: TerminalVerdict),
  total_mass: 1
}

AFKExtractorExperimentBody(S, n, Q, P^a, E) = {
  probability_space: ExtractorSpace distinct from ProverSpace,
  owned_randomness: [E coins, one initially sampled and then fixed P^a coin
                     tape, verifier coins,
                     extractor-owned lazy-sampled/programmed RO state],
  run: E(n) with black-box access to P^a and theorem-granted interfaces,
  output: (x: AnalysisStatementType(S),
           pi: AFKProofType(S), aux: BitString,
           v: TerminalVerdict, w: AnalysisWitnessType(S)),
  total_mass: 1
}

AFKAdversaryRunningAlgorithmSchema(S) = {
  parameter_schema: [
    n: StatementLength(AnalysisStatementType(S)),
    Q: AFKAdversaryROQueryCount(S),
    P^a: AdaptiveQQueryProver(S,n,Q,AFKRandomOracleQueryABI(S))],
  ordinary_inputs: [],
  ambient_setup: AFKFixedPublicSetupId(S),
  black_box_subject:
    AdaptiveQQueryProver(S,n,Q,AFKRandomOracleQueryABI(S)),
  output: exact prover output plus FS verifier outcome and AFK extractor view,
  counted_resource: one complete black-box invocation
}

AFKAdversaryInvocationResourceDimension(S) = ResourceDimension {
  operation_role: AFKAdversaryBlackBoxInvocationOperationRef,
  value_sort: Nat,
  owner_subjects: CanonicalAppend(
    AFKTargetSubjectProjection(S),[AFKExtractorProfileId(S)]),
  dependent_parameter_schema: [],
  capability_abi_or_algorithm_schema: AFKAdversaryRunningAlgorithmSchema(S),
  lifetime_scope: one exact extractor experiment probability-space instance,
  aggregation: Expected,
  exact_counter_event:
    completion of one instantiation of AFKAdversaryRunningAlgorithmSchema(S)
    at any admitted `(n,Q,P^a)` arguments
}

AFKAdversaryRunningAlgorithmA(S, n, Q, P^a) =
  Instantiate(AFKAdversaryRunningAlgorithmSchema(S), n, Q, P^a) {
  run P^a under the exact lazy-sampled RO interface derived from S,
  perform exact verification by S.fiat_shamir_protocol_id,
  expose the queried logical index, transcript, and verifier outcome required
    by the AFK extractor
}

epsilon(S,n,Q,P^a) =
  EventProbability(
    AFKProverExperimentBody(S,n,Q,P^a), v = Accept)

extractor_witness_success(S,n,Q,P^a,E) =
  EventProbability(
    AFKExtractorExperimentBody(S,n,Q,P^a,E),
    v = Accept and
      RelationHolds(S.relation_instance_id,x,w))

IdenticalMarginalLaw(
  AFKProverExperimentBody(S,n,Q,P^a),
  Marginal(AFKExtractorExperimentBody(S,n,Q,P^a,E), [x,pi,aux,v]),
  exact tuple codec and equality)
```

`EventProbability` takes an identified experiment body and a typed measurable
event; it is not a free numeric variable. The two space identities rotate if
their coin ownership, oracle state, scheduler, output, or total-mass law
changes. Fixed public setup is ambient theorem-instance state and visible under
its declared policy, not an ordinary input to `P^a`. A module returning a
wrong-length Statement or making more than `Q` logical queries is outside the
dependent quantified domain.

The target experiment body closes the common profile fields as follows:

```text
AnalysisConstantOnePolynomialProfileBody(S: AnalysisSubjectTuple) = {
  input_sort: StatementLength(AnalysisStatementType(S)),
  coefficient_domain: Nat,
  value_shape: exactly coefficients_low_to_high = [1],
  canonical_degree_rule: degree = 0,
  evaluation: exact checked-natural constant function returning 1,
  positivity_rule: value is 1 for every admitted Statement length,
  admitted_coefficient_and_degree_bounds: coefficient = 1 and degree = 0
}

AnalysisConstantOnePolynomialProfileId(S: AnalysisSubjectTuple) =
  AnalysisPositivePolynomialProfileId(
    B, AnalysisConstantOnePolynomialProfileBody(S))

AnalysisConstantOnePolynomialId(S: AnalysisSubjectTuple) =
  AnalysisPositivePolynomialId(B, {
    profile_id: AnalysisConstantOnePolynomialProfileId(S),
    coefficients_low_to_high: [1]
  })

AFKMemberKnowledgeExperimentProfile(
    S: AnalysisSubjectTuple,
    ell0: StatementLength(AnalysisStatementType(S))) = {
  family: AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  source_profile_id: AFKFreshFsSourceProfileId,
  quantifier_prefix: [
    ExistsUniformBlackBoxExtractor(
      binding_ordinal: 0,AFKExtractorProfileId(S)),
    ForAllQuantitativeValue(
      binding_ordinal: 1,
      AFKAdversaryROQueryCount(S),
      0 <= CurrentQuantifiedValue <
        ModelCardinality(AnalysisChallengeDomainId(S))),
    ForAllStrategy(
      binding_ordinal: 2,
      AFKAdaptiveQQueryProverProfileId(S),
      AdaptiveQQueryProver(
        S,ell0,EarlierQuantifierRef(1),exact RO ABI))
  ],
  role_interfaces: [P^a_random_oracle_query, V_random_oracle_query,
                    E_black_box_prover, E_programmable_random_oracle],
  setup_and_input_sampling:
    AFKFixedPublicSetupId(S) followed by input-free P^a output,
  randomness_ownership_and_independence:
    two separate probability spaces with their own E/P^a/V/RO coins and the
    exact required marginal-law equality,
  public_coin_or_oracle_model:
    one total classical uniform random oracle into the challenge set,
  scheduler:
    exact prover/verifier experiment and exact AFK extractor experiment,
  generated_execution_relation:
    exact AFKProverExperimentBody(S,ell0,Q,P^a) and
      AFKExtractorExperimentBody(S,ell0,Q,P^a,E),
  observation_and_win_event:
    IdenticalMarginalLaw(x,pi,aux,v) and the two bound EventProbability terms,
  failure_abort_and_noncompletion_law:
    explicit abort and rejection are typed completed outputs; missing P^a
    output or nontermination is outside the admitted prover strategy class,
  termination_law:
    the exact expected-call inequality selected below; no asymptotic conclusion
    follows from this fixed-length member profile; P^a is total-output but has
    no running-time bound,
  resource_basis:
    adversary RO queries, black-box P^a calls, verifier calls, expected E time,
  output_type:
    fixed-length adaptive extraction judgment with typed bounds
}

AFKMemberKnowledgeQuestion(
    S: AnalysisSubjectTuple,
    ell0: StatementLength(AnalysisStatementType(S))) = AnalysisQuestionBody {
  family: AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  exact_subjects: ExactSubjectSequenceUnion(
    AFKTargetSubjectProjection(S),
    [AnalysisChallengeDomainId(S), AFKFixedPublicSetupId(S)]),
  context: SemanticExperimentContext {
    semantic_read_manifest_ids: [AFKTargetSemanticReadManifestId(S)],
    experiment_profile_ids: [AFKMemberKnowledgeExperimentProfileId(S,ell0)]
  },
  family_payload: {
    exact classical-ROM and adaptive-statement coordinates,
    exact fixed statement length ell0, q_KS(ell0) = 1 substitution, and
      hard-Q range,
    AFKKnowledgeErrorFormulaId(S), AFKKnowledgeSuccessFormulaId(S),
      and AFKExpectedCallsFormulaId(S),
    epsilon bound to the exact prover acceptance EventProbability,
    inequality left side bound to the exact extractor witness-success
      EventProbability,
    exact IdenticalMarginalLaw and relation-witness conclusion schema
  },
  named_premise_requirements: FiatShamirConstructionPremiseRequirements(
    S.transcript_construction_id, AFKClassicalRandomOracleProfileId(S))
}

AFKMemberKnowledgeGoal(
    S: AnalysisSubjectTuple,
    ell0: StatementLength(AnalysisStatementType(S))) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B, AFKMemberKnowledgeQuestion(S,ell0)),
  named_premise_bindings: FiatShamirConstructionPremiseBindings(S, ell0)
}
```

`AFKTranscriptExtractionFormulaId(S)` is an applicability/proof-intermediate
formula corresponding to AFK Lemma 4. It is checked when the theorem template
is instantiated, but it is not a fourth result of the Definition-10 target
property and therefore does not enter this question or goal.

The active nominal spellings are aliases for the common Foundation constructors, not
additional identity formulas:

```text
SchnorrRelationSourceProfileId =
  AnalysisSourceProfileId(B, SchnorrRelationSourceProfileBody)
SchnorrRelationSemanticReadManifestId(S: AnalysisSubjectTuple) =
  AnalysisSemanticReadManifestId(
    B, SchnorrRelationSemanticReadManifestBody(S))
SchnorrSpecialSoundnessExperimentProfileId(S: AnalysisSubjectTuple) =
  AnalysisExperimentProfileId(
    B, SchnorrSpecialSoundnessExperimentProfile(S))
SchnorrFixedExtractorUniversalExperimentProfileId(S: AnalysisSubjectTuple) =
  AnalysisExperimentProfileId(
    B, SchnorrFixedExtractorUniversalExperimentProfile(S))

AFKFreshFsSourceProfileId =
  AnalysisSourceProfileId(B, AFKFreshFsSourceProfileBody)
AFKTargetSemanticReadManifestId(S: AnalysisSubjectTuple) =
  AnalysisSemanticReadManifestId(B, AFKTargetSemanticReadManifestBody(S))
AFKAdaptiveQQueryProverProfileId(S: AnalysisSubjectTuple) =
  AnalysisStrategyClassProfileId(B, AFKAdaptiveQQueryProverProfileBody(S))
AFKExtractorProfileId(S: AnalysisSubjectTuple) =
  AnalysisExtractorProfileId(B, AFKExtractorProfileBody(S))
AFKMemberKnowledgeExperimentProfileId(
    S: AnalysisSubjectTuple,
    ell0: StatementLength(AnalysisStatementType(S))) =
  AnalysisExperimentProfileId(B,AFKMemberKnowledgeExperimentProfile(S,ell0))
```

Each body is the exact closed field selection on this page and the relation
seam. A label alone cannot form one of these aliases.

The exact active prefix is part of the profile identity. A profile with
`ForAllStrategy` before the extractor existential, an auxiliary-input sampler,
a PPT-only adversary, extractor advice `Q` or `epsilon`, shared probability
spaces, or a different failure law is not this theorem target.

The AFK efficiency coordinate is also semantic identity:

```text
AFKEfficiencyProfile = {
  security_parameter_and_input_length_measure,
  exact machine_and_step model,
  hard adversary random-oracle query bound and its scope,
  unit-cost accounting for one black-box invocation of P^a,
  extractor input restricted to n plus black-box access to P^a,
  prohibition on Q, epsilon, prover code, or hidden-table advice,
  positive-polynomial witness q_KS,
  source extractor polynomial-time law,
  source verifier and relation-membership polynomial-time laws,
  theorem-owned target expected-time transformer,
  exact polynomial witnesses and range thresholds
}
```

The `Q + 2` black-box-call expression below is one resource component, not by
itself a proof of expected polynomial time. Missing or mismatched relation,
verifier, source-extractor, or target-extractor efficiency laws keep the theorem
application conditional or prevent applicability according to the selected
policy.

### 4.2 Exact transcript and Statement correspondence

Applicability consumes the current PIR views:

```text
PublicBindingView
StrategyDecisionView
PublicCoinView
EffectView
ClaimReductionView
ExecutionView
TranscriptDeclarationView
RequiredInfluenceView
ChallengeTransitionView
FSConstructionView
```

For the three-move profile, the challenge oracle index must contain the exact
application/domain separator, the exact Statement, and the exact preceding
commitment in their PIR-defined order and framing. The Statement and commitment
maps come from the checked Relations/PIR sources. An omitted, late, reordered, or
different occurrence refuses applicability.

The initial lane makes one explicit Statement-boundary choice rather than ambiguously
extending the relation Statement. The AFK Statement is the raw Schnorr relation
Statement `Y`. Group parameters, session/application domain, Core and
construction headers, scope path, framing law, challenge-condition schema, and
challenge namespace are one `FixedPublicSetup`. They are selected before and
independently of `P^a` and the random oracle, are visible through the declared
coordinate-by-coordinate visibility map, and remain fixed for one theorem
instance under an explicit Analysis correspondence premise. Applicability refuses if
the session or another setup coordinate is adversary-selected, oracle-
correlated, or changes within the instance. A future profile may instead use an
extended Statement and lifted relation, but that is a different theorem
application.

The correspondence is value-level, not merely the coordinate pair
`(Statement, commitment)`. It defines and checks:

```text
AFKRandomOracleIndex(S) =
  CanonicalByteString under the exact Foundation family bound

AFKLogicalQuery_FixedSetup(Y, A) =
  CanonicalEncode(
    exact PIR DerivedPrefix at the challenge for this setup, Y, and A,
    exact PIR ChallengeNamespace at draw zero)

AFKLogicalImageClassify(S,index) =
    ImageOfExactVerifierQuery(Y,A)
  | OpaqueOffImage(index)
```

The derived prefix includes the public binding for `Y`, the prover commitment,
and the exact challenge-condition frame (including its repeated typed `Y`
value), as well as every fixed header/setup frame. For each admitted fixed
setup, this encoder must be total, canonical, and injective in `(Y,A)`. The
algorithm-to-random-oracle correspondence is a full adaptive-oracle-process
law, not a marginal-output claim. `P^a` may query any admitted
`AFKRandomOracleIndex(S)`; every image and off-image call counts toward `Q`.
For every admitted adaptive query strategy within that hard bound, the joint
law of the complete oracle interaction must equal the law of one lazily sampled
AFK random function over the complete index domain. On the exact verifier-query
image, that process must additionally agree with the PIR construction's encoded
query. In particular, it preserves same-index repeat consistency, the joint
independent-uniform law at distinct indices even when later indices are chosen
adaptively, exact logical-query counting, and every theorem-authorized
rerun/programming operation used by the extractor, including off-image points.
One PIR squeeze/decoder invocation corresponds to one first query at its
injectively encoded verifier-image index; a repeat observes the same sampled
value and does not silently create a new logical point. Coordinate order,
equality of one finite output, pointwise
uniform marginals, or a familiar hash construction does not establish this
proposition.

The theorem model has one uniform random function into the exact finite
challenge set, exposed through its adaptive random-oracle interface. A
concrete hash or duplex algorithm is not thereby proven to implement that
process. The target retains the full algorithm-to-logical-oracle process
correspondence as a model assumption unless established independently.

### 4.3 Sampler adequacy

PIR supports bounded rejection and an explicit `SamplingExhausted` outcome.
That general construction is not definitionally equal to AFK's total uniform
challenge oracle.

The initial profile therefore closes only when one of these exact conditions
is selected and justified:

1. the admitted decoder is total and exactly uniform for the declared
   challenge set, such as one octet reduced into a power-of-two cardinality
   with one draw; or
2. a separate admitted theorem/correspondence handles rejection, retry
   namespaces, exhaustion, query accounting, and its exact quantitative term.

A biased decoder, an unmodeled exhaustion branch, or an unsupported reverse-
sampling/programming operation prevents applicability. A finite SHA-256 run is
neither sampler proof nor ROM evidence.

<!-- zkc-profile-source:analysis-property-semantics:end -->

<!-- zkc-profile-source:analysis-transport-family-semantics:start -->

### 4.4 Asymptotic family profile and concrete-member split

The Definition-10 subject is a mathematical family. It is not an infinite
sequence of native Foundation/PIR objects. The family ID therefore authenticates only
one finite language reference and one finite payload:

```text
AFKSchnorrFamilyLanguageDeclarationBody =
  AnalysisAsymptoticFamilyLanguageDeclarationBody(
    MetaSymbol("afk-v2-three-move-public-coin-family"),Unit,0)

AFKSchnorrFamilyLanguageRef =
  the one exact AnalysisProfileDeclarationRef<
    "analysis.asymptotic-family-language"> in
  AnalysisAFKTransportLanguageProfileId whose complete declaration body is
  AFKSchnorrFamilyLanguageDeclarationBody and whose resolved contract is the
  exact abstract-member signature and denotation law on this page

AFKSchnorrFamilyPayloadV0 = CanonicalValue<Unit>(Unit)

AFKSchnorrFamilyDefinitionBody =
  AnalysisAsymptoticProtocolFamilyDefinitionBody(
    AFKSchnorrFamilyLanguageRef,AFKSchnorrFamilyPayloadV0)

AFKSchnorrFamilyDefinitionId =
  AnalysisAsymptoticProtocolFamilyDefinitionId(
    B,AFKSchnorrFamilyLanguageRef,AFKSchnorrFamilyPayloadV0)

AFKAbstractMember(F,n:LogicalNat) = FamilyMember(F,n) with abstract fields {
  Statement_F(n), Witness_F(n), Relation_F(n),
  PublicSetup_F(n), Commitment_F(n), ChallengeSet_F(n), Response_F(n),
  Fresh_F(n), FiatShamir_F(n), Proof_F(n), Aux_F(n), Verifier_F(n),
  VerifierOutput_F(n),
  RandomOracleIndex_F(n), statement_length_F, resource_measures_F
}

N_F(n) = MathematicalCardinality(ChallengeSet_F(n))

AFKFamilyConstantChallengeCardinality(F) =
  the canonical nominal value of sort FamilyConstantChallengeCardinality(F)
  derived from F; its equality to every N_F(n) is an explicit applicability
  proposition and is not established by family formation

AFKSpecialSoundnessPair_F(n) = {
  one Statement in Statement_F(n), one commitment in Commitment_F(n),
  two responses in Response_F(n), two distinct members of ChallengeSet_F(n),
  and two Fresh_F(n) records both accepted by Verifier_F(n), with exact
  role-coordinate equality on the shared Statement and commitment
}

admitted_pair_F(n,pair) =
  the exact abstract pair-membership predicate above

AFKAbstractSourceRole(tag,ordinal,dependent_signature,adequacy) =
  AbstractFamilyRoleReadSlotSchema(
    LocalAnalysisSourceFamilyRoleRef {
      local_role_ordinal: ordinal,
      exact_role_tag: tag
    },SemanticMeaning,
    DependentForAll([n : LogicalNat],dependent_signature),adequacy,
    AFKTransportAttemptFailurePartitionRef)

AFKFamilyFreshAbstractSlotCatalog = CanonicalSeq [
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("statement",ValueCarrier),
    0,Statement_F(n),
    exact Statement projection of one member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("witness",ValueCarrier),
    1,Witness_F(n),
    exact Witness projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("relation",Predicate),2,
    Relation_F(n): Statement_F(n) * Witness_F(n) -> Bool,
    exact relation projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("commitment",ValueCarrier),
    3,Commitment_F(n),
    exact first-message projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("challenge-set",ValueCarrier),
    4,ChallengeSet_F(n),
    exact finite nonempty challenge-set projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("response",ValueCarrier),
    5,Response_F(n),
    exact response projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "fresh-experiment",ExperimentProcess),6,Fresh_F(n),
    exact Fresh experiment projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("verifier",VerifierProcess),
    7,Verifier_F(n),
    exact verifier projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "verifier-output",ValueCarrier),8,VerifierOutput_F(n),
    exact verifier-output projection of that member)
]

AFKFamilyTargetAdditionalAbstractSlotCatalog = CanonicalSeq [
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("public-setup",ValueCarrier),
    9,PublicSetup_F(n),
    exact public-setup projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "fiat-shamir-experiment",ExperimentProcess),10,FiatShamir_F(n),
    exact Fiat--Shamir experiment projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef("proof",ValueCarrier),
    11,Proof_F(n),
    exact proof projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "auxiliary-output",ValueCarrier),12,Aux_F(n),
    exact auxiliary-output projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "random-oracle-index",ValueCarrier),13,RandomOracleIndex_F(n),
    exact random-oracle-index projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "statement-length",QuantitativeValue),14,statement_length_F(n),
    exact statement-length projection of that member),
  AFKAbstractSourceRole(AnalysisFamilyRoleKindRef(
      "resource-measures",ResourceMeasure),15,resource_measures_F(n),
    exact resource-measure projection of that member)
]

AFKFamilyFreshSourceProfileBody = {
  family_tag: AFKAbstractFreshFamilySource,
  slot_schemas: AFKFamilyFreshAbstractSlotCatalog,
  closed_field_read_set:
    exact projections of those roles from one abstract family member,
  adequacy_evaluator_id: AFKFamilyFreshSourceProfileAdequacy
}

AFKFamilyTargetSourceProfileBody = {
  family_tag: AFKAbstractFreshFsFamilySource,
  slot_schemas:
    CanonicalConcat(AFKFamilyFreshAbstractSlotCatalog,
                    AFKFamilyTargetAdditionalAbstractSlotCatalog),
  closed_field_read_set:
    exact projections of those roles from one abstract family member,
  adequacy_evaluator_id: AFKFamilyTargetSourceProfileAdequacy
}

AFKFamilyFreshSourceProfileId =
  AnalysisSourceProfileId(B,AFKFamilyFreshSourceProfileBody)
AFKFamilyTargetSourceProfileId =
  AnalysisSourceProfileId(B,AFKFamilyTargetSourceProfileBody)

RequiredAnalysisLanguageProfile(AFKFamilyFreshSourceProfileBody) =
  AnalysisAFKTransportLanguageProfileId
RequiredAnalysisLanguageProfile(AFKFamilyTargetSourceProfileBody) =
  AnalysisAFKTransportLanguageProfileId

SchnorrRelationSpecialSoundnessSourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody<
    AnalysisCryptographicPropertyLanguageProfileId> {
    allowed_slot_variant: ConcreteOwnerSource,
    exact_slot_and_field_schema: SchnorrSourceSlotCatalog,
    exact_adequacy_evaluator_schema:
      SchemaOf(SchnorrRelationSourceProfileAdequacy),
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef
  }

AFKAdaptiveFreshFsSourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody<
    AnalysisCryptographicPropertyLanguageProfileId> {
    allowed_slot_variant: ConcreteOwnerSource,
    exact_slot_and_field_schema:
      CanonicalConcat(SchnorrSourceSlotCatalog,AFKCanonicalFramedAdditionalSourceSlotCatalog),
    exact_adequacy_evaluator_schema:
      SchemaOf(AFKFreshFsSourceProfileAdequacy),
    failure_classification: CryptographicPropertyAttemptFailurePartitionRef
  }

AFKAbstractFreshFamilySourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody<
    AnalysisAFKTransportLanguageProfileId> {
    allowed_slot_variant: AbstractFamilyRole,
    exact_slot_and_field_schema: AFKFamilyFreshAbstractSlotCatalog,
    exact_adequacy_evaluator_schema:
      SchemaOf(AFKFamilyFreshSourceProfileAdequacy),
    failure_classification: AFKTransportAttemptFailurePartitionRef
  }

AFKAbstractFreshFsFamilySourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody<
    AnalysisAFKTransportLanguageProfileId> {
    allowed_slot_variant: AbstractFamilyRole,
    exact_slot_and_field_schema:
      CanonicalConcat(AFKFamilyFreshAbstractSlotCatalog,
                      AFKFamilyTargetAdditionalAbstractSlotCatalog),
    exact_adequacy_evaluator_schema:
      SchemaOf(AFKFamilyTargetSourceProfileAdequacy),
    failure_classification: AFKTransportAttemptFailurePartitionRef
  }

SchnorrRelationSpecialSoundnessSource =
  the one exact AnalysisSourceFamilyCoordinate resolved by
  AnalysisCryptographicPropertyLanguageProfileId whose body is
  SchnorrRelationSpecialSoundnessSourceDeclarationBody
AFKAdaptiveFreshFsSource =
  the one exact AnalysisSourceFamilyCoordinate resolved by that same profile
  whose body is AFKAdaptiveFreshFsSourceDeclarationBody
AFKAbstractFreshFamilySource =
  the one exact AnalysisSourceFamilyCoordinate resolved by
  AnalysisAFKTransportLanguageProfileId
  whose body is AFKAbstractFreshFamilySourceDeclarationBody
AFKAbstractFreshFsFamilySource =
  the one exact AnalysisSourceFamilyCoordinate resolved by that same transport
  profile
  whose body is AFKAbstractFreshFsFamilySourceDeclarationBody

AnalysisSourceFamilyContract(P,body) =
  AnalysisSourceFamilySemanticsContract<P> {
  allowed_slot_variant: body.allowed_slot_variant,
  exact_slot_and_field_schema: body.exact_slot_and_field_schema,
  exact_adequacy_evaluator_schema: body.exact_adequacy_evaluator_schema,
  failure_classification: body.failure_classification
}

AnalysisPropertySourceFamilyProfileContracts = CanonicalKeySortedSeq [
  {SchnorrRelationSpecialSoundnessSource,
   SchnorrRelationSpecialSoundnessSourceDeclarationBody,
   AnalysisSourceFamilyContract(
     AnalysisCryptographicPropertyLanguageProfileId,
     SchnorrRelationSpecialSoundnessSourceDeclarationBody)},
  {AFKAdaptiveFreshFsSource,AFKAdaptiveFreshFsSourceDeclarationBody,
   AnalysisSourceFamilyContract(
     AnalysisCryptographicPropertyLanguageProfileId,
     AFKAdaptiveFreshFsSourceDeclarationBody)}
]

AnalysisTransportSourceFamilyProfileContracts = CanonicalKeySortedSeq [
  {AFKAbstractFreshFamilySource,
   AFKAbstractFreshFamilySourceDeclarationBody,
   AnalysisSourceFamilyContract(
     AnalysisAFKTransportLanguageProfileId,
     AFKAbstractFreshFamilySourceDeclarationBody)},
  {AFKAbstractFreshFsFamilySource,
   AFKAbstractFreshFsFamilySourceDeclarationBody,
   AnalysisSourceFamilyContract(
     AnalysisAFKTransportLanguageProfileId,
     AFKAbstractFreshFsFamilySourceDeclarationBody)}
]

AnalysisCryptographicPropertyLanguageProfileId =
  the exact profile defined in `analysis-model.md` whose authenticated inline
  catalogs and law source contain exactly
  AnalysisPropertySourceFamilyProfileContracts plus the bounded property,
  concrete-source/body, experiment, quantitative, native-rule, use, and
  adequacy contracts in this page

AnalysisAFKTransportLanguageProfileId =
  the exact importing profile defined in `analysis-model.md` whose
  authenticated inline catalogs and law source contain exactly
  AnalysisTransportSourceFamilyProfileContracts plus the AFK asymptotic-family,
  abstract-source/body, F-dependent experiment and quantitative,
  theorem-transport, specialization, native-rule, use, and adequacy contracts
  in this page
```

Each profile's imports are exactly those fixed in the Analysis profile bundle. A
missing, unused, extra, duplicate, reverse, or body-mismatched entry rejects
profile support. Ordinary algorithm and owner-module roots are authenticated
separately by their exact subject-specific dependency closures.

The selected language declaration resolves under the exact three-field grammar
in [`analysis-model.md`](analysis-model.md#23-asymptotic-family-ingress), its
lifted payload type admits exactly `AFKSchnorrFamilyPayloadV0`, and its contract
denotes the abstract fields above. There is no caller label, binder spelling,
law string, or alternative payload in this constructor. None of those fields is a `AnalysisSubjectTuple`,
`ValueType`, `ProtocolId`, `RelationInstanceId`, or `PortableAlgorithmRef`.
Formation of `F` authenticates the description but proves neither that the
denotation is total and single-valued nor that its members satisfy any law.

The two dependent source projections are finite symbolic bodies derived from
the one denotation; callers do not author parallel member fields:

```text
AFKFamilyFreshReadManifestSchemaBody(F) = {
  family_definition_id: F,
  member_source_profile_id: AFKFamilyFreshSourceProfileId
}

AFKFamilyTargetReadManifestSchemaBody(F) = {
  family_definition_id: F,
  member_source_profile_id: AFKFamilyTargetSourceProfileId
}

AFKFamilyFreshReadManifestSchemaId(F) =
  AnalysisFamilyReadManifestSchemaId(
    B,AFKFamilyFreshReadManifestSchemaBody(F))
AFKFamilyTargetReadManifestSchemaId(F) =
  AnalysisFamilyReadManifestSchemaId(
    B,AFKFamilyTargetReadManifestSchemaBody(F))
```

The common derived-projection rule maps the Fresh profile, in slot order, to
exactly `Statement_F`, `Witness_F`, `Relation_F`, `Commitment_F`,
`ChallengeSet_F`, `Response_F`, `Fresh_F`, `Verifier_F`, and
`VerifierOutput_F`. It maps the target profile to that canonical list followed
by `PublicSetup_F`, `FiatShamir_F`, `Proof_F`, `Aux_F`,
`RandomOracleIndex_F`, `statement_length_F`, and `resource_measures_F`.
Agreement with one denoted member and same-interaction Fresh/FS coherence are
propositions, not extra fields in either ID preimage. The derived list and the
profile's declared slot sequence MUST be byte-for-byte equal; a missing,
additional, or reordered role is malformed.

The family random oracle is one lazy random function for each member execution,
over the complete abstract query domain. It is not a concrete hash and not the
finite PIR sampler:

```text
AFKFamilyRandomOracleProfileBody(F) = {
  output_type: ChallengeSet_F(n),
  exact_support_predicate: membership in ChallengeSet_F(n),
  exact_probability_mass_or_measure_law:
    independent uniform first answers and consistent repeated answers,
  parameter_and_security_parameter_coordinates: [F,n : LogicalNat],
  independence_and_correlation_declarations:
    one fresh table per probability space; no cross-space shared state,
  sampling_or_oracle_denotation:
    initially empty lazy total function over all RandomOracleIndex_F(n),
    including off-verifier-image indices,
  failure_and_nontermination_law:
    every query returns one challenge; no sampler failure or divergence
}

AFKFamilyRandomOracleProfileId(F) =
  AnalysisDistributionProfileId(B,AFKFamilyRandomOracleProfileBody(F))

AFKFamilyROQueryCallSchema(F) = {
  dependent_parameter_schema: [n : LogicalNat],
  input_type_at_parameter: RandomOracleIndex_F(n),
  output_type_at_parameter: ChallengeSet_F(n),
  operation_semantics:
    one total lookup invocation; repeated indices are still invocations,
  profile_or_capability_binding: none
}

AFKFamilyROQueryDimension(F) = ResourceDimension {
  operation_role: AFKFamilyAdversaryRandomOracleQueryOperationRef,
  value_sort: Nat,
  owner_subjects: [F,AFKFamilyRandomOracleProfileId(F)],
  dependent_parameter_schema: [],
  capability_abi_or_algorithm_schema:
    AFKFamilyROQueryCallSchema(F),
  lifetime_scope:
    one member execution probability-space instance selected at use time,
  aggregation: Sum,
  exact_counter_event:
    every query invocation, including repeats and off-image queries
}

AFKFamilyRandomOracleQueryABI(F,n) = {
  call_schema: instantiate AFKFamilyROQueryCallSchema(F) at n,
  distribution_profile_id: AFKFamilyRandomOracleProfileId(F),
  resource_dimension: AFKFamilyROQueryDimension(F),
  capability:
    one query right bound to the profile, n, resource dimension, and current
    probability-space instance,
  accounting:
    increment the exact resource dimension before every lookup,
  completion: total, with repeats returning the existing lazy-table value
}

AFKFamilyAdversaryCallSchema(F) = {
  dependent_parameter_schema: [
    n : LogicalNat,
    Q : QueryCount<AFKFamilyROQueryDimension(F)> with
      0 <= Q < AFKFamilyConstantChallengeCardinality(F)],
  black_box_module_schema:
    one input-free total-output strategy with the exact F-owned Statement,
    proof, auxiliary-output, and AFKFamilyRandomOracleQueryABI(F,n) roles and
    at most Q counted calls,
  invocation_input: Unit,
  invocation_output:
    (Statement_F(n),Proof_F(n),Aux_F(n)) plus exact query/answer traffic,
  completion: one returned output for every admitted invocation
}

AFKFamilyAdversaryInvocationDimension(F) = ResourceDimension {
  operation_role: AFKFamilyAdversaryBlackBoxInvocationOperationRef,
  value_sort: Nat,
  owner_subjects: [F],
  dependent_parameter_schema: [],
  capability_abi_or_algorithm_schema:
    AFKFamilyAdversaryCallSchema(F),
  lifetime_scope:
    one target extractor experiment probability-space instance selected at
    use time,
  aggregation: Expected,
  exact_counter_event: one complete black-box invocation of P^a
}

AFKFamilyAdversaryInvocationCapabilityABILawRef and
AFKFamilyROSimulationProgrammingCapabilityABILawRef
  = two pairwise-distinct exact
    `AnalysisProfileLawRef<AnalysisAFKTransportLanguageProfileId,CapabilityABI>`
    values. Their profile-local ordinals, and therefore their canonical
    encoded order, are the displayed order. The first declaration owns the
    `AFKFamilyAdversaryCallSchema` invocation ABI; the second owns the
    independent lazy family-random-oracle simulation and programming ABI.
    Neither ref grants access to hidden table entries or Protocol replay.
```

The uniform algorithm profiles are logical algorithm schemas. They are not Foundation
portable algorithms and do not inherit Foundation's finite iteration limit:

```text
AFKFamilySourceExtractorProfileBody(F) = {
  input_and_output_types: {
    inputs: [n : LogicalNat, AFKSpecialSoundnessPair_F(n)],
    outputs: [Witness_F(n)]
  },
  private_state_and_randomness_types: [Unit,Unit],
  allowed_source_and_oracle_capabilities: [],
  counterfactual_rights: [],
  state_preservation_relation: deterministic stateless evaluation,
  output_distribution_preservation_relation: deterministic singleton law,
  witness_success_relation:
    every admitted pair maps to a Witness satisfying Relation_F(n),
  termination_and_asymptotic_resource_law:
    total and polynomial in the exact family length measure,
  counterfactual_capability_contract_and_property_family_scope: {
    counterfactual_capability_contract: none,
    property_family_scope: AsymptoticKOutOfNSpecialSoundness(k=2)
  }
}

AFKFamilyAdaptiveProverProfileBody(F) = {
  role: input-free adaptive prover P^a,
  dependent_parameter_schema: [
    n : LogicalNat,
    Q : QueryCount<AFKFamilyROQueryDimension(F)> with
      0 <= Q < AFKFamilyConstantChallengeCardinality(F)
  ],
  strategy_abi:
    Unit -> (Statement_F(n),Proof_F(n),Aux_F(n)) with
      statement_length_F(Statement)=n; the prover coin tape is sampled once at
      the outer experiment boundary and fixed into the resulting deterministic
      next-message strategy for every extractor rerun,
  private_state_type: family-declared prover state,
  initial_advice_type: family-declared private advice quantified with P^a,
  allowed_views: own private state, advice, randomness, and prior query answers,
  allowed_oracles_and_capabilities:
    only AFKFamilyRandomOracleQueryABI(F,n),
  legal_move_relation:
    every query inhabits RandomOracleIndex_F(n), at most Q counted calls occur
    including repeats and off-image calls, and the final output has length n,
  stop_and_noncompletion_law:
    exactly one total output; no polynomial-time requirement,
  resource_dimensions:
    [AFKFamilyROQueryDimension(F)] with parameters n and Q
}

AFKFamilyTargetExtractorProfileBody(F) = {
  input_and_output_types: {
    inputs: [n : LogicalNat],
    outputs:
      [(Statement_F(n),Proof_F(n),Aux_F(n),VerifierOutput_F(n),Witness_F(n))]
  },
  private_state_and_randomness_types:
    [family extractor state,fresh extractor coins],
  allowed_source_and_oracle_capabilities:
    [AFKFamilyAdversaryInvocationCapabilityABILawRef,
     AFKFamilyROSimulationProgrammingCapabilityABILawRef],
  counterfactual_rights: [ProgramSibling, Rerun],
  state_preservation_relation:
    the theorem-local adaptive construction and lazy-table state relation,
  output_distribution_preservation_relation:
    exact equality of the `(Statement,Proof,Aux,VerifierOutput)` distribution
    with the separate prover experiment,
  witness_success_relation:
    VerifierOutput = Accept and Relation_F(n)(Statement,Witness),
  termination_and_asymptotic_resource_law:
    expected polynomial in n and actual Q, counting one P^a invocation as one
    step in AFKFamilyAdversaryInvocationDimension(F),
  counterfactual_capability_contract_and_property_family_scope: {
    counterfactual_capability_contract:
      exact classical lazy-RO simulation/programming contract for restricted
      adaptive knowledge soundness and the exact root-rerun interface required
      by `Rerun`; the input ABI excludes Q, epsilon, prover code, and the
      oracle table,
    property_family_scope:
      AdaptiveKnowledgeSoundnessQltN; QROM and generic restoration are unsupported
  }
}

AFKFamilySourceExtractorProfileId(F) =
  AnalysisExtractorProfileId(B,AFKFamilySourceExtractorProfileBody(F))
AFKFamilyAdaptiveProverProfileId(F) =
  AnalysisStrategyClassProfileId(B,AFKFamilyAdaptiveProverProfileBody(F))
AFKFamilyTargetExtractorProfileId(F) =
  AnalysisExtractorProfileId(B,AFKFamilyTargetExtractorProfileBody(F))
```

The source and target questions now carry the actual asymptotic prefixes:

```text
AFKFamilySpecialSoundnessExperimentProfileBody(F) = {
  family: AsymptoticKOutOfNSpecialSoundness,
  source_profile_id: AFKFamilyFreshSourceProfileId,
  quantifier_prefix: [
    ExistsUniformExtractorFamily(
      binding_ordinal: 0,AFKFamilySourceExtractorProfileId(F)),
    ForAllLogicalNat(binding_ordinal: 1,true),
    ForAllFamilyValue(
      binding_ordinal: 2,F,
      AFKSpecialSoundnessPair_F(EarlierQuantifierRef(1)),
      admitted_pair_F(EarlierQuantifierRef(1)))
  ],
  role_interfaces: [Ext_F: AFKFamilySourceExtractorProfileId(F)],
  setup_and_input_sampling: none,
  randomness_ownership_and_independence: none,
  public_coin_or_oracle_model:
    abstract Fresh public-coin structure with no sampled coin in this
    deterministic pair experiment,
  scheduler: validate pair, then run Ext_F,
  generated_execution_relation:
    the two records satisfy the exact same-Statement, same-commitment,
    distinct-challenge, accepting-pair predicate,
  observation_and_win_event:
    Ext_F(n,pair) satisfies Relation_F(n),
  failure_abort_and_noncompletion_law:
    malformed/nonmember pairs are outside the implication; extractor failure
    on a member violates the candidate universal conclusion,
  termination_law:
    the uniform source-extractor totality premise,
  resource_basis:
    the exact family source-extractor measure,
  output_type:
    conditional asymptotic two-special-soundness judgment
}

AFKFamilyAdaptiveKnowledgeExperimentProfileBody(F) = {
  family: AdaptiveKnowledgeSoundnessQltN,
  source_profile_id: AFKFamilyTargetSourceProfileId,
  quantifier_prefix: [
    ExistsPositivePolynomial(
      binding_ordinal: 0,AFKLogicalNatPositivePolynomialProfileId),
    ExistsUniformBlackBoxExtractor(
      binding_ordinal: 1,AFKFamilyTargetExtractorProfileId(F)),
    ForAllLogicalNat(binding_ordinal: 2,true),
    ForAllQuantitativeValue(
      binding_ordinal: 3,
      QueryCount<AFKFamilyROQueryDimension(F)>,
      0 <= CurrentQuantifiedValue <
        AFKFamilyConstantChallengeCardinality(F)),
    ForAllStrategy(
      binding_ordinal: 4,
      AFKFamilyAdaptiveProverProfileId(F),
      exact total-output adaptive EarlierQuantifierRef(3)-query member strategy)
  ],
  role_interfaces: [
    P^a: AFKFamilyAdaptiveProverProfileId(F),
    E: AFKFamilyTargetExtractorProfileId(F)
  ],
  setup_and_input_sampling:
    PublicSetup_F(n) fixed before the quantified strategy and both spaces;
    P^a receives no ordinary input,
  randomness_ownership_and_independence:
    prover and extractor spaces use separate coins and independently sampled
    family random functions,
  public_coin_or_oracle_model: AFKFamilyRandomOracleProfileId(F),
  scheduler:
    run each space under its own oracle while the extractor obtains only n and
    black-box P^a access,
  generated_execution_relation: {
    prover_space:
    one fresh P^a coin tape for the top-level experiment, verifier coins, and
      one family random oracle; fix that tape for the resulting deterministic
      next-message strategy, then run P^a and
      the exact FiatShamir_F(n) verifier to obtain (x,pi,aux,v),
    extractor_space:
    independent coins and oracle; run E on n with black-box P^a to obtain
      (x,pi,aux,v,w)
  },
  observation_and_win_event: {
    required_marginal_law:
    the two `(x,pi,aux,v)` distributions are identical,
    required_success_law:
    Pr_extractor[v=Accept and Relation_F(n)(x,w)] is at least
      AFKFamilyKnowledgeSuccessFormulaId(F)(epsilon,n,Q),
    required_resource_law:
    expected P^a invocations are at most
      AFKFamilyExpectedCallsFormulaId(F)(Q)
  },
  failure_abort_and_noncompletion_law:
    oracle calls are total; P^a is quantified only over total-output
    strategies; E must satisfy the stated expected-time law,
  termination_law:
    P^a has no polynomial-time requirement but returns; E has expected
    polynomial time in n and actual Q,
  resource_basis: [
    AFKFamilyROQueryDimension(F),
    AFKFamilyAdversaryInvocationDimension(F),
    the exact family machine and length measures
  ],
  output_type:
    restricted-query adaptive knowledge-soundness family judgment
}

AFKFamilySpecialSoundnessExperimentProfileId(F) =
  AnalysisExperimentProfileId(
    B,AFKFamilySpecialSoundnessExperimentProfileBody(F))
AFKFamilyAdaptiveKnowledgeExperimentProfileId(F) =
  AnalysisExperimentProfileId(
    B,AFKFamilyAdaptiveKnowledgeExperimentProfileBody(F))

AFKFamilySpecialSoundnessQuestion(F) = AnalysisQuestionBody {
  family: AsymptoticKOutOfNSpecialSoundness,
  exact_subjects: [F],
  context: FamilySemanticExperimentContext {
    family_definition_id: F,
    family_read_manifest_schema_ids: [AFKFamilyFreshReadManifestSchemaId(F)],
    family_experiment_profile_ids:
      [AFKFamilySpecialSoundnessExperimentProfileId(F)]
  },
  family_payload:
    exact `exists uniform Ext_F; forall n; forall pair` relation conclusion,
  named_premise_requirements: []
}

AFKFamilySpecialSoundnessGoal(F) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B,AFKFamilySpecialSoundnessQuestion(F)),
  named_premise_bindings: {}
}

AFKFamilyAdaptiveKnowledgeQuestion(F) = AnalysisQuestionBody {
  family: AdaptiveKnowledgeSoundnessQltN,
  exact_subjects: [F],
  context: FamilySemanticExperimentContext {
    family_definition_id: F,
    family_read_manifest_schema_ids: [AFKFamilyTargetReadManifestSchemaId(F)],
    family_experiment_profile_ids:
      [AFKFamilyAdaptiveKnowledgeExperimentProfileId(F)]
  },
  family_payload: {
    exact Definition-10 marginal and success-event schemas,
    AFKFamilyKnowledgeErrorFormulaId(F),
    AFKFamilyKnowledgeSuccessFormulaId(F),
    AFKFamilyExpectedCallsFormulaId(F),
    exact q_KS = AFKLogicalNatConstantOnePolynomialId
  },
  named_premise_requirements: FiatShamirNamedPremiseRequirements(F, AFKFamilyRandomOracleProfileId(F))
}

AFKFamilyAdaptiveKnowledgeGoal(F) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B,AFKFamilyAdaptiveKnowledgeQuestion(F)),
  named_premise_bindings: FiatShamirFamilyPremiseBindings(F)
}
```

The source proposition retains all mathematical obligations rather than
turning family formation into a proof:

```text
AFKFamilyPremiseQuestion(F,family,payload,extra_subjects) =
  AnalysisQuestionBody {
    family,
    exact_subjects: CanonicalAppend([F],extra_subjects),
    context: FamilySemanticExperimentContext {
      family_definition_id: F,
      family_read_manifest_schema_ids:
        [AFKFamilyFreshReadManifestSchemaId(F)],
      family_experiment_profile_ids:
        [AFKFamilySpecialSoundnessExperimentProfileId(F)]
    },
    family_payload: payload
  ,
    named_premise_requirements: NamedPremiseRequirementsOf(family, exact_subjects)
}

AFKFamilyPremiseGoal(F,family,payload,extra_subjects) =
  AnalysisGoalBody {
    question_id: AnalysisQuestionId(
      B,AFKFamilyPremiseQuestion(F,family,payload,extra_subjects))
  ,
    named_premise_bindings: {}
}

AFKFamilyDenotationGoal(F) = AFKFamilyPremiseGoal(
  F,TotalSingleValuedFamilyDenotation,{
    exact_proposition:
      `for every LogicalNat n, F denotes exactly one member of the declared
       abstract signature`
  },[])

AFKFamilyProjectionCoherenceGoal(F) = AFKFamilyPremiseGoal(
  F,FamilyProjectionCoherence,{
    exact_proposition:
      `every source/target role is derived from that one member and the Fresh
       and FS experiments share its exact interaction, relation, and setup`
  },[])

AFKFamilyChallengeAndAlgebraGoal(F) = AFKFamilyPremiseGoal(
  F,UniformPrimeOrderSchnorrFamily,{
    exact_proposition:
      `N_F(n)>=2; challenges are distinct/invertible as required; the
       relation, encoding, verifier, and deterministic extractor equations
       hold for all n`
  },[])

AFKFamilyRelationEfficiencyGoal(F) = AFKFamilyPremiseGoal(
  F,UniformPolynomialTimeRelationMembership,{
    exact_proposition:
      `one family algorithm decides Relation_F(n) in polynomial time`
  },[])

AFKFamilyVerifierEfficiencyGoal(F) = AFKFamilyPremiseGoal(
  F,UniformPolynomialTimeVerifier,{
    exact_proposition:
      `one family verifier implements Verifier_F(n) in polynomial time`
  },[])

GammaAFKFamilySpecialBody(F) = AnalysisHypothesisContextBody {
  nodes: [
    {0,AnalysisGoalId(B,AFKFamilyDenotationGoal(F)),[], premises(goal)},
    {1,AnalysisGoalId(B,AFKFamilyProjectionCoherenceGoal(F)),[0], premises(goal)},
    {2,AnalysisGoalId(B,AFKFamilyChallengeAndAlgebraGoal(F)),[0,1], premises(goal)},
    {3,AnalysisGoalId(B,AFKFamilyRelationEfficiencyGoal(F)),[0,1], premises(goal)},
    {4,AnalysisGoalId(B,AFKFamilyVerifierEfficiencyGoal(F)),[0,1], premises(goal)}
  ],
  roots: [2,3,4],
  exact_named_premise_ids: ContextPremiseIds(nodes, roots)
}

GammaAFKFamilySpecialId(F) =
  AnalysisHypothesisContextId(B,GammaAFKFamilySpecialBody(F))

AFKFamilySpecialSoundnessPropositionBody(F) = AnalysisPropositionBody {
  goal_id: AnalysisGoalId(B,AFKFamilySpecialSoundnessGoal(F)),
  hypothesis_context_id: GammaAFKFamilySpecialId(F)
}
```

The five-node context states the family-side conditions under which the exact
source goal is asked; its outward root frontier is `[2,3,4]`. The existential
extractor variable remains locally bound inside the source experiment and
goal. It never escapes as a free portable subject or parameter of a question,
proposition, basis, support, or transport identity.

Analysis deliberately defines no native semantic basis that mints an affirmative
`AFKFamilySpecialSoundnessPropositionBody(F)` capability. The admitted family
language supplies role carriers and relations, not authenticated field/group
operations or a family-logic program denotation. An independently checked
proof authority may establish this exact proposition in the future; until
then, property transport must return `CannotAnswer` for the missing source
capability. The finite instrument may form the proposition and reject a forged
or wrong-family capability, but it cannot manufacture the asymptotic source
theorem from the finite Schnorr extractor fixture.

The concrete `AFKMemberKnowledgeGoal(S,ell0)` above is not Definition 10. It is
reconstructed only after both a family target judgment and the checked
conditional `FamilyInstanceCorrespondence(F,n0_literal,S,ell0)` in Section 8
are available. No fixed
`S`, finite value range, or test corpus can fill `ForAllLogicalNat`.

## 5. AFK theorem profile

The imported theorem schema is global: it does not name a concrete subject
`S`, an asymptotic family `F`, a property result, or an Analysis formula ID.
It authenticates one exact theorem statement and local typed transform
templates:

```text
AFKV2IACREPrintPDFSourceKindRef =
  the exact AnalysisProfileDeclarationRef<"analysis.theorem-source-kind">
  for an IACR ePrint archive PDF in
  AnalysisAFKTheoremSourceValidationLanguageProfileId

ASCIIBytes(s) =
  the exact byte sequence of the displayed ASCII literal `s`; formation
  rejects a non-ASCII code point and the display delimiters are not bytes

Bytes32FromLowerHex(s) =
  the exact 32-byte value decoded from a 64-character lowercase hexadecimal
  ASCII literal `s`; a wrong length, uppercase character, non-hex character,
  or trailing byte is malformed

AFKV2SelectedSourceAuthority = {
  publication_kind: AFKV2IACREPrintPDFSourceKindRef,
  stable_source_id: ASCIIBytes("iacr-eprint:2021/1377"),
  bibliographic_revision: {
    version: ASCIIBytes("2"),
    date: ASCIIBytes("2022-02-16")
  },
  artifact_media_type: ASCIIBytes("application/pdf"),
  artifact_sha256: Bytes32FromLowerHex(
    "93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c"),
  exact_locators: [
    ASCIIBytes("Definition 4"),
    ASCIIBytes("Definition 10"),
    ASCIIBytes("Definition 11"),
    ASCIIBytes(
      "Section 4 Figure 3 and consistency prose immediately before Lemma 4"),
    ASCIIBytes("Lemma 4"),
    ASCIIBytes(
      "Section 6.3 adaptive construction immediately before Theorem 4"),
    ASCIIBytes("Remark 2"),
    ASCIIBytes("Remark 6"),
    ASCIIBytes("Theorem 4")]
}

AFKV2SelectedStatementTemplateSummary = {
  source:
    one uniform polynomial-time 2-special-sound extractor for an asymptotic
    three-move public-coin protocol family,
  target:
    classical-ROM adaptive knowledge soundness in the exact Definition-10
    experiment, restricted to one fixed finite N and 0 <= Q < N,
  quantifiers:
    source `exists Ext_ss; forall n; forall accepting distinct pair` and
    target `exists q; exists E; forall n; forall Q<N; forall P^a`,
  conclusion:
    identical `(x,pi,aux,v)` marginals, relation-witness success at least
    `epsilon-(Q+1)/N`, and at most `Q+2` black-box P^a invocations,
  statement_scope:
    exact k=2 restricted-query implication; not an all-Q target profile
}

AFKV2LocalDenotationSchemaRef(i) =
  the unique AnalysisAFKTransportLanguageProfileId-local
  AnalysisProfileLawRef<TheoremLocalDenotationSchema> at ordinal i; its
  authenticated law-source row is keyed by the complete binding kind and
  dependency sequence at ordinal i below and admits exactly that typed AFK-v2
  local denotation, with no display binder or prose payload

AFKV2LocalBindingCatalog = CanonicalSeq [
  {0,AsymptoticFamilyParameter,[],AFKV2LocalDenotationSchemaRef(0)},
  {1,LogicalNatParameter(LocalTheoremBindingRef(0)),[0],
    AFKV2LocalDenotationSchemaRef(1)},
  {2,PositivePolynomialParameter(LogicalNat),[],
    AFKV2LocalDenotationSchemaRef(2)},
  {3,QuantifiedStrategyParameter(UniformSourceExtractor),[0],
    AFKV2LocalDenotationSchemaRef(3)},
  {4,SemanticRole(AcceptingDistinctTranscriptPair),[0,1],
    AFKV2LocalDenotationSchemaRef(4)},
  {5,QuantifiedStrategyParameter(UniformBlackBoxTargetExtractor),[0],
    AFKV2LocalDenotationSchemaRef(5)},
  {6,SemanticRole(Statement),[0,1],AFKV2LocalDenotationSchemaRef(6)},
  {7,SemanticRole(RelationWitness),[0,1],AFKV2LocalDenotationSchemaRef(7)},
  {8,SemanticRole(Commitment),[0,1],AFKV2LocalDenotationSchemaRef(8)},
  {9,SemanticRole(Challenge),[0,1],AFKV2LocalDenotationSchemaRef(9)},
  {10,SemanticRole(Response),[0,1],AFKV2LocalDenotationSchemaRef(10)},
  {11,SemanticRole(Acceptance),[0,1],AFKV2LocalDenotationSchemaRef(11)},
  {12,SemanticRole(FixedPublicSetup),[0,1],
    AFKV2LocalDenotationSchemaRef(12)},
  {13,SemanticRole(FreshInteraction),[0,1],
    AFKV2LocalDenotationSchemaRef(13)},
  {14,SemanticRole(FiatShamirInteraction),[0,1],
    AFKV2LocalDenotationSchemaRef(14)},
  {15,SemanticRole(FullRandomOracleProcess),[0,1],
    AFKV2LocalDenotationSchemaRef(15)},
  {16,SemanticRole(Proof),[0,1],AFKV2LocalDenotationSchemaRef(16)},
  {17,SemanticRole(AuxiliaryOutput),[0,1],
    AFKV2LocalDenotationSchemaRef(17)},
  {18,SemanticRole(VerifierOutput),[0,1],
    AFKV2LocalDenotationSchemaRef(18)},
  {19,SemanticRole(Relation),[0,1],AFKV2LocalDenotationSchemaRef(19)},
  {20,SemanticRole(RandomOracleIndex),[0,1],
    AFKV2LocalDenotationSchemaRef(20)},
  {21,SemanticRole(RandomOracleStatementIndex),[0,1],
    AFKV2LocalDenotationSchemaRef(21)},
  {22,SemanticRole(RandomOracleCommitmentIndex),[0,1],
    AFKV2LocalDenotationSchemaRef(22)},
  {23,SemanticRole(Verifier),[0,1],AFKV2LocalDenotationSchemaRef(23)},
  {24,SemanticRole(ChallengeSampler),[0,1],
    AFKV2LocalDenotationSchemaRef(24)},
  {25,SemanticRole(BoundedBitStringIndexContract),[0,1,20],
    AFKV2LocalDenotationSchemaRef(25)},
  {26,ChallengeCardinalityRole(LocalTheoremBindingRef(0)),[0],
    AFKV2LocalDenotationSchemaRef(26)},
  {27,ResourceRole(QueryCount),[0,15,20,25],
    AFKV2LocalDenotationSchemaRef(27)},
  {28,ResourceRole(ExpectedCount),[0],AFKV2LocalDenotationSchemaRef(28)},
  {29,QuantitativeParameter(QueryCount(LocalTheoremBindingRef(27))),
    [0,1,26,27],AFKV2LocalDenotationSchemaRef(29)},
  {30,QuantifiedStrategyParameter(InputFreeAdaptiveOracleProver),
    [0,1,20,27,29],AFKV2LocalDenotationSchemaRef(30)}
]

AFKLocalFamilyRef =
  LocalTheoremBindingRef<AsymptoticFamilyParameter>(0)
AFKLocalLogicalNatRef =
  LocalTheoremBindingRef<LogicalNatParameter>(1)
AFKLocalPositivePolynomialRef =
  LocalTheoremBindingRef<PositivePolynomialParameter>(2)
AFKLocalSourceExtractorRef =
  LocalTheoremBindingRef<QuantifiedStrategyParameter>(3)
AFKLocalAcceptingPairRef =
  LocalTheoremBindingRef<SemanticRole<AcceptingDistinctTranscriptPair>>(4)
AFKLocalTargetExtractorRef =
  LocalTheoremBindingRef<QuantifiedStrategyParameter>(5)
AFKLocalStatementRef = LocalTheoremBindingRef<SemanticRole<Statement>>(6)
AFKLocalWitnessRef =
  LocalTheoremBindingRef<SemanticRole<RelationWitness>>(7)
AFKLocalCommitmentRef = LocalTheoremBindingRef<SemanticRole<Commitment>>(8)
AFKLocalChallengeRef = LocalTheoremBindingRef<SemanticRole<Challenge>>(9)
AFKLocalResponseRef = LocalTheoremBindingRef<SemanticRole<Response>>(10)
AFKLocalAcceptanceRef = LocalTheoremBindingRef<SemanticRole<Acceptance>>(11)
AFKLocalPublicSetupRef =
  LocalTheoremBindingRef<SemanticRole<FixedPublicSetup>>(12)
AFKLocalFreshRef =
  LocalTheoremBindingRef<SemanticRole<FreshInteraction>>(13)
AFKLocalFiatShamirRef =
  LocalTheoremBindingRef<SemanticRole<FiatShamirInteraction>>(14)
AFKLocalRandomOracleProcessRef =
  LocalTheoremBindingRef<SemanticRole<FullRandomOracleProcess>>(15)
AFKLocalProofRef = LocalTheoremBindingRef<SemanticRole<Proof>>(16)
AFKLocalAuxiliaryOutputRef =
  LocalTheoremBindingRef<SemanticRole<AuxiliaryOutput>>(17)
AFKLocalVerifierOutputRef =
  LocalTheoremBindingRef<SemanticRole<VerifierOutput>>(18)
AFKLocalRelationRef = LocalTheoremBindingRef<SemanticRole<Relation>>(19)
AFKLocalRandomOracleIndexRef =
  LocalTheoremBindingRef<SemanticRole<RandomOracleIndex>>(20)
AFKLocalRandomOracleStatementIndexRef =
  LocalTheoremBindingRef<SemanticRole<RandomOracleStatementIndex>>(21)
AFKLocalRandomOracleCommitmentIndexRef =
  LocalTheoremBindingRef<SemanticRole<RandomOracleCommitmentIndex>>(22)
AFKLocalVerifierRef = LocalTheoremBindingRef<SemanticRole<Verifier>>(23)
AFKLocalChallengeSamplerRef =
  LocalTheoremBindingRef<SemanticRole<ChallengeSampler>>(24)
AFKLocalBoundedIndexContractRef =
  LocalTheoremBindingRef<SemanticRole<BoundedBitStringIndexContract>>(25)
AFKLocalChallengeCardinalityRef =
  LocalTheoremBindingRef<ChallengeCardinalityRole>(26)
AFKLocalROQueryResourceRef =
  LocalTheoremBindingRef<ResourceRole<QueryCount>>(27)
AFKLocalAdversaryInvocationResourceRef =
  LocalTheoremBindingRef<ResourceRole<ExpectedCount>>(28)
AFKLocalQueryBoundRef =
  LocalTheoremBindingRef<QuantitativeParameter<QueryCount>>(29)
AFKLocalAdaptiveProverRef =
  LocalTheoremBindingRef<QuantifiedStrategyParameter>(30)

AFKV2TheoremComponentDeclarationCatalog = {
  property:
    AFKV2PropertySchemaContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-property-schema">,
  experiment:
    AFKV2ExperimentSchemaContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-experiment-schema">,
  source_view:
    AFKV2SourceViewSchemaContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-source-view-schema">,
  map:
    AFKV2MapSchemaContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-map-schema">,
  side_condition:
    AFKV2SideConditionSchemaContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-side-condition-schema">,
  transform:
    AFKV2TransformProgramContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-transform-program">,
  conclusion:
    AFKV2ConclusionLawContractRef :
      AnalysisProfileDeclarationRef<"analysis.theorem-conclusion-law">
}

The semantic transport profile supports `analysis.theorem-schema`. The narrow
`AnalysisAFKTheoremSourceValidationLanguageProfileId` imports it and supports
`analysis.theorem-source-validation`; only that child profile's inline catalogs
include `AFKV2IACREPrintPDFSourceKindRef` and the exact closed validation body
schema. Source-kind declarations are not theorem-schema components and no
source authority or proof-status field occurs in the theorem semantic body.

AFKV2TheoremLanguageProfileContracts contains exactly these active Analysis
entries in the exact AFK-v2 theorem semantic-language profile, keyed by the
complete declaration references above:

  AFKV2PropertySchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-property-schema"> {
      exact_component_payload_meta_schema:
        the closed two-variant canonical union of exactly the source-property
        and target-property record shapes displayed below, including every
        typed local binding, quantifier ordinal, premise DAG, operator ref,
        output role, success law, and resource law,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the typed refs appearing in those two variants,
      exact_component_interpretation_law:
        the source variant denotes uniform all-n two-special soundness and the
        target variant denotes the restricted Definition-10 classical-ROM goal,
      cross_component_coherence_law:
        both variants share AFKLocalFamilyRef and AFKLocalLogicalNatRef and the
        target operator refs resolve in the enclosing schema,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    },

  AFKV2ExperimentSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-experiment-schema"> {
      exact_component_payload_meta_schema:
        the closed two-variant canonical union of exactly the source and target
        experiment records displayed below,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the typed strategy, pair, semantic-role, logical-nat, and query
        refs in those records,
      exact_component_interpretation_law:
        the source is the three-move Fresh pair experiment and the target is the
        two-space Definition-10 adaptive classical-ROM experiment,
      cross_component_coherence_law:
        experiment quantifier ordinals and roles equal the property components'
        local bindings,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    },

  AFKV2SourceViewSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-source-view-schema"> {
      exact_component_payload_meta_schema: CanonicalRecord {
        role: LocalTheoremBindingRef<SemanticRole>
      },
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the eleven refs in AFKV2RequiredSourceViewComponents,
      exact_component_interpretation_law:
        require that exact semantic role from the application source view,
      cross_component_coherence_law:
        every role is declared once in AFKV2LocalBindingCatalog,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    },

  AFKV2MapSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-map-schema"> {
      exact_component_payload_meta_schema:
        the closed union of one bounded-bitstring injective-encoding record and
        one exact typed-equality role-pair record as displayed below,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the source, target, index-domain, bounded-index-contract, and
        equality-role refs in AFKV2MapComponents,
      exact_component_interpretation_law:
        require the selected total maps without creating correspondence truth,
      cross_component_coherence_law:
        every map endpoint equals the corresponding source-view or experiment
        role and every table operation uses AFKLocalROQueryResourceRef,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    },

  AFKV2SideConditionSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-side-condition-schema"> {
      exact_component_payload_meta_schema:
        the closed tagged union of exactly the eight side-condition record
        variants in AFKV2SideConditionComponents, with no payload-less alias,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the family, fixed-cardinality, bounded-index, index, query-
        resource, and query-bound refs used by those variants,
      exact_component_interpretation_law:
        each variant creates one applicability premise and establishes none,
      cross_component_coherence_law:
        the fixed N and query domain equal the operator and experiment bindings,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    },

  AFKV2TransformProgramContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-transform-program"> {
      exact_component_payload_meta_schema:
        exactly the closed transform record displayed below, including all
        typed family, n, q, N, Q, resource, and operator refs,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly those refs and no schema-local shadow catalog,
      exact_component_interpretation_law:
        instantiate all four typed templates and preserve the marginal law,
      cross_component_coherence_law:
        source/target property, experiment, and operator refs match exactly,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    },

  AFKV2ConclusionLawContractRef ->
    AnalysisTheoremComponentSemanticsContract<
      AnalysisAFKTransportLanguageProfileId,
      "analysis.theorem-conclusion-law"> {
      exact_component_payload_meta_schema:
        exactly the closed conclusion-reconstruction record displayed below,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the local operator refs selected by that record,
      exact_component_interpretation_law:
        reconstruct only AFKV2TargetPropertyComponent and retain every listed
        obligation,
      cross_component_coherence_law:
        the reconstructed target and operators equal the enclosing components,
      failure_classification: AFKTransportAttemptFailurePartitionRef
    }.

The phrase “displayed below” in this profile-law display is a same-page grammar
reference: the profile's exact law-source bytes encode the corresponding
`AnalysisProfileLawRef` schemas and laws, and admission expands the referenced
canonical record fields and tags before hashing or comparison. It is not a
label accepted in place of the body. A missing,
extra, reordered, differently typed, or payload-less variant is malformed; a
different complete declaration coordinate is unsupported.

AFKV2Component<C>(contract_ref:AnalysisProfileDeclarationRef<C>,payload) =
  TheoremSchemaComponent<C> {
    contract_ref: contract_ref,
    canonical_payload:
      CanonicalValue<resolved and lifted payload type of contract_ref>(payload)
  }

AFKV2SourcePropertyComponent = AFKV2Component(
  AFKV2PropertySchemaContractRef,{
    local_family_binder: AFKLocalFamilyRef,
    property_family: AsymptoticKOutOfNSpecialSoundness,
    k: 2,
    quantifier_prefix:
      ExistsUniformExtractor_Then_ForAllLogicalNat_Then_ForAllAcceptingPair,
    exact_local_quantifier_bindings: [
      {0,AFKLocalSourceExtractorRef},
      {1,AFKLocalLogicalNatRef},
      {2,AFKLocalAcceptingPairRef}
    ],
    experiment_observation:
      exact AFKLocalWitnessRef relation success for AFKLocalAcceptingPairRef at
      AFKLocalLogicalNatRef,
    exact_premise_schema:
      CanonicalSeq [
        {0,TotalSingleValuedFamilyDenotation,[]},
        {1,FamilyProjectionCoherence,[0]},
        {2,UniformPrimeOrderSchnorrFamily,[0,1]},
        {3,UniformPolynomialTimeRelationMembership,[0,1]},
        {4,UniformPolynomialTimeVerifier,[0,1]}
      ] with outward root frontier [2,3,4]
  })

AFKV2TargetPropertyComponent = AFKV2Component(
  AFKV2PropertySchemaContractRef,{
    local_family_binder: AFKLocalFamilyRef,
    property_family: AdaptiveKnowledgeSoundnessQltN,
    model: ClassicalRandomOracleModel,
    quantifier_prefix:
      ExistsPositivePolynomial_Then_ExistsUniformBlackBoxExtractor_Then_
      ForAllLogicalNat_Then_ForAllQltN_Then_ForAllInputFreeAdaptiveProver,
    exact_local_quantifier_bindings: [
      {0,AFKLocalPositivePolynomialRef},
      {1,AFKLocalTargetExtractorRef},
      {2,AFKLocalLogicalNatRef},
      {3,AFKLocalQueryBoundRef},
      {4,AFKLocalAdaptiveProverRef}
    ],
    output_law:
      exact equality of the (AFKLocalStatementRef,AFKLocalProofRef,
      AFKLocalAuxiliaryOutputRef,AFKLocalVerifierOutputRef) marginals,
    success_law:
      relation-witness success is at least LocalTheoremOperatorRef(1),
    resource_law:
      expected adversary invocations are at most
      LocalTheoremOperatorRef(3)
  })

AFKV2SourceExperimentComponent = AFKV2Component(
  AFKV2ExperimentSchemaContractRef,{
    experiment_family: ThreeMovePublicCoinFreshFamily,
    interaction_order: [AFKLocalStatementRef,AFKLocalCommitmentRef,
      AFKLocalChallengeRef,AFKLocalResponseRef],
    verifier_observations: [AFKLocalPublicSetupRef,AFKLocalStatementRef,
      AFKLocalCommitmentRef,AFKLocalChallengeRef,AFKLocalResponseRef],
    extractor_interface:
      AFKLocalSourceExtractorRef receives AFKLocalAcceptingPairRef and returns
      one AFKLocalWitnessRef satisfying AFKLocalRelationRef
  })

AFKV2TargetExperimentComponent = AFKV2Component(
  AFKV2ExperimentSchemaContractRef,{
    experiment_family: AFKDefinition10AdaptiveClassicalROM,
    prover_interface:
      AFKLocalAdaptiveProverRef with query limit AFKLocalQueryBoundRef,
    extractor_interface:
      AFKLocalTargetExtractorRef has uniform black-box access to
      AFKLocalAdaptiveProverRef and no prover description,
    probability_spaces:
      two distinct classical lazy-random-function spaces with the exact AFK
      marginal-law comparison,
    outputs: [AFKLocalStatementRef,AFKLocalProofRef,
      AFKLocalAuxiliaryOutputRef,AFKLocalVerifierOutputRef]
  })

AFKV2RequiredSourceViewComponents = CanonicalSeq [
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalStatementRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalWitnessRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalCommitmentRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalChallengeRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalResponseRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalAcceptanceRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalPublicSetupRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalFreshRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{role: AFKLocalFiatShamirRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{
    role: AFKLocalRandomOracleProcessRef}),
  AFKV2Component(AFKV2SourceViewSchemaContractRef,{
    role: AFKLocalBoundedIndexContractRef})
]

AFKV2MapComponents = CanonicalSeq [
  AFKV2Component(AFKV2MapSchemaContractRef,{
    source_role: AFKLocalStatementRef,
    target_role: AFKLocalRandomOracleStatementIndexRef,
    index_domain_role: AFKLocalRandomOracleIndexRef,
    bounded_index_contract_role: AFKLocalBoundedIndexContractRef,
    map_kind: ExactEfficientInjectiveBoundedBitStringEncoding
  }),
  AFKV2Component(AFKV2MapSchemaContractRef,{
    source_role: AFKLocalCommitmentRef,
    target_role: AFKLocalRandomOracleCommitmentIndexRef,
    index_domain_role: AFKLocalRandomOracleIndexRef,
    bounded_index_contract_role: AFKLocalBoundedIndexContractRef,
    map_kind: ExactEfficientInjectiveBoundedBitStringEncoding
  }),
  AFKV2Component(AFKV2MapSchemaContractRef,{
    role_pairs: [
      (AFKLocalChallengeRef,AFKLocalChallengeRef),
      (AFKLocalResponseRef,AFKLocalResponseRef),
      (AFKLocalProofRef,AFKLocalProofRef),
      (AFKLocalVerifierOutputRef,AFKLocalVerifierOutputRef),
      (AFKLocalRelationRef,AFKLocalRelationRef),
      (AFKLocalWitnessRef,AFKLocalWitnessRef),
      (AFKLocalPublicSetupRef,AFKLocalPublicSetupRef)
    ],
    map_kind: ExactTypedEquality
  })
]

AFKV2SideConditionComponents = CanonicalSeq [
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: TotalSingleValuedCoherentFamilyDenotation
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: FixedFiniteChallengeCardinality,
    family_ref: AFKLocalFamilyRef,
    cardinality_ref: AFKLocalChallengeCardinalityRef,
    exact_domain: AFKLocalChallengeCardinalityRef >= 2
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: PublicCoinUniformityAndIndependence
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: UniformEfficientSourceExtractorRelationAndVerifier
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: ExactClassicalLazyRandomFunctionProcess
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: FiniteBoundedBitStringRandomOracleIndexAndEfficientOperations,
    exact_contract_role: AFKLocalBoundedIndexContractRef,
    exact_index_role: AFKLocalRandomOracleIndexRef,
    exact_query_resource_role: AFKLocalROQueryResourceRef
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: FramingSamplingProgrammingAndRerunAdequacy
  }),
  AFKV2Component(AFKV2SideConditionSchemaContractRef,{
    condition: RestrictedQueryDomain,
    exact_query_ref: AFKLocalQueryBoundRef,
    exact_domain:
      0 <= AFKLocalQueryBoundRef and
      AFKLocalQueryBoundRef < AFKLocalChallengeCardinalityRef
  })
]

AFKV2LocalQuantitativeOperatorCatalog = CanonicalSeq [
  LocalTheoremOperatorDeclaration {
    local_ordinal: 0,
    operand_sorts: [LocalQueryCount(AFKLocalROQueryResourceRef),
      LocalChallengeCardinality(AFKLocalChallengeCardinalityRef)],
    result_sort: ConcreteAnalysisSort(Probability),
    exact_template:
      BoundedCountRatioAsProbability(
        AddSameSort(LocalOperand(0),
          CountConstant<LocalQueryCount(AFKLocalROQueryResourceRef)>(1)),
        LocalOperand(1),LocalMagnitudeMap(
          AFKLocalROQueryResourceRef,AFKLocalChallengeCardinalityRef),
        exact domain 0 <= LocalOperand(0) < LocalOperand(1))
  },
  LocalTheoremOperatorDeclaration {
    local_ordinal: 1,
    operand_sorts: [
      ConcreteAnalysisSort(Probability),ConcreteAnalysisSort(LogicalNat),
      LocalQueryCount(AFKLocalROQueryResourceRef),
      LocalChallengeCardinality(AFKLocalChallengeCardinalityRef),
      LocalPositivePolynomial(AFKLocalPositivePolynomialRef)],
    result_sort: ConcreteAnalysisSort(SignedProbabilityLowerBound),
    exact_template:
      DivideSignedLowerBoundByLocalPositivePolynomial(
        ProbabilityDifferenceAsSignedLowerBound(
          LocalOperand(0),LocalTheoremOperatorRef(0)(
            LocalOperand(2),LocalOperand(3))),
        LocalOperand(4),LocalOperand(1))
  },
  LocalTheoremOperatorDeclaration {
    local_ordinal: 2,
    operand_sorts: [
      ConcreteAnalysisSort(Probability),
      LocalQueryCount(AFKLocalROQueryResourceRef),
      LocalChallengeCardinality(AFKLocalChallengeCardinalityRef)],
    result_sort: ConcreteAnalysisSort(SignedProbabilityLowerBound),
    exact_template:
      ScaleSignedLowerBoundByPositiveCountRatio(
        LocalOperand(2),PredecessorCount(LocalOperand(2),
          exact domain LocalOperand(2) >= 2),
        LocalMagnitudeMap(AFKLocalChallengeCardinalityRef,
          AFKLocalChallengeCardinalityRef),
        ProbabilityDifferenceAsSignedLowerBound(
          LocalOperand(0),LocalTheoremOperatorRef(0)(
            LocalOperand(1),LocalOperand(2))))
  },
  LocalTheoremOperatorDeclaration {
    local_ordinal: 3,
    operand_sorts: [LocalQueryCount(AFKLocalROQueryResourceRef)],
    result_sort: LocalExpectedCount(AFKLocalAdversaryInvocationResourceRef),
    exact_template:
      QueryBoundPlusOverheadAsExpectedCount(
        LocalOperand(0),2,
        LocalExpectedCount(AFKLocalAdversaryInvocationResourceRef))
  }
]

AFKV2TransformProgramComponent = AFKV2Component(
  AFKV2TransformProgramContractRef,{
    local_family_binding: AFKLocalFamilyRef,
    local_logical_nat_binding: AFKLocalLogicalNatRef,
    local_resource_roles: [
      AFKLocalROQueryResourceRef,AFKLocalAdversaryInvocationResourceRef
    ],
    local_challenge_role: AFKLocalChallengeCardinalityRef,
    local_query_bound: AFKLocalQueryBoundRef,
    local_operator_ordinals: [0,1,2,3],
    positive_polynomial_binder: {
      target_experiment_quantifier_ordinal: 0,
      expected_quantifier_kind: ExistsPositivePolynomial,
      required_profile_shape:
        exactly the singleton LogicalNat polynomial [1],
      theorem_local_binding: AFKLocalPositivePolynomialRef,
      theorem_local_operand:
        LocalPositivePolynomial(AFKLocalPositivePolynomialRef)
    },
    positive_polynomial_substitution:
      AFKLocalPositivePolynomialRef is target quantifier ordinal 0 and its exact
      singleton-profile value fills that theorem-local operand,
    source_premise_schema: AFKV2SourcePropertyComponent,
    theorem_local_transform:
      bind each local operator exactly once, import no ambient loss, and retain
      the exact output-marginal equality obligation
  })

AFKV2ConclusionLawComponent = AFKV2Component(
  AFKV2ConclusionLawContractRef,{
    reconstruct_exactly: AFKV2TargetPropertyComponent,
    quantitative_conclusions: [
      LocalTheoremOperatorRef(0),LocalTheoremOperatorRef(1),
      LocalTheoremOperatorRef(3)
    ],
    retained_obligations:
      every theorem-truth, model, map, efficiency, process-correspondence,
      and side-condition premise,
    forbidden_inference:
      no theorem truth, source property, family law, ROM law, or concrete-hash
      idealization follows from schema admission
  })

AFKV2TheoremSchemaBody = AnalysisTheoremSchemaBody {
  local_binding_catalog: AFKV2LocalBindingCatalog,
  source_property_schema: AFKV2SourcePropertyComponent,
  target_property_schema: AFKV2TargetPropertyComponent,
  source_experiment_schema: AFKV2SourceExperimentComponent,
  target_experiment_schema: AFKV2TargetExperimentComponent,
  required_source_view_schemas: AFKV2RequiredSourceViewComponents,
  map_schemas: AFKV2MapComponents,
  side_condition_and_parameter_schemas: AFKV2SideConditionComponents,
  local_quantitative_operator_catalog:
    AFKV2LocalQuantitativeOperatorCatalog,
  typed_resource_and_loss_transform_program:
    AFKV2TransformProgramComponent,
  exact_conclusion_reconstruction_law: AFKV2ConclusionLawComponent
}

AFKV2TheoremSchemaId =
  AnalysisTheoremSchemaId(B,AFKV2TheoremSchemaBody)

AFKV2SelectedStatementContentDigest =
  TheoremStatementDigest(AFKV2TheoremSchemaId)

AFKV2TheoremSourceValidationBody = AnalysisTheoremSourceValidationBody {
  theorem_schema_id: AFKV2TheoremSchemaId,
  source_authority: AFKV2SelectedSourceAuthority,
  truth_discharge_metadata: {
    authority_class: ImportedPaperOnly,
    admitted_proof_artifact: None,
    truth_discharge_mode: RetainedTheoremTruthAssumption,
    schema_admission_establishes_truth: false
  }
}

AFKV2TheoremSourceValidationId =
  AnalysisTheoremSourceValidationId(
    B,AFKV2TheoremSourceValidationBody)
```

The derived statement-content digest identifies the exact admitted profiled
semantic theorem body and cannot be supplied independently. The PDF digest and
locators identify only the selected source artifact. A source correction or
bibliographic revision therefore forms a different
`AFKV2TheoremSourceValidationId` without changing the theorem schema. An
all-query target, different quantifier order, changed expected-call unit, map,
or other semantic statement change forms a different theorem schema and, since
the validation body names that schema ID, a different source-validation ID.

For `k=2`, Lemma 4 gives the stronger transcript-extraction lower bound

```text
N/(N-1) * (epsilon-(Q+1)/N).
```

When `epsilon-(Q+1)/N` is nonnegative, that is at least the Definition-10
threshold with `q(n)=1`; when it is negative, probability nonnegativity already
implies the signed lower bound. The adaptive construction supplies the required
output-law preservation. This is why the selected schema uses the constant-one
polynomial; the choice is not inferred from a theorem name or finite example.

The success threshold, transcript-extraction threshold, and invocation bound
remain three different typed results. The schema does not clamp a signed lower
bound, treat raw random-oracle queries as adversary invocations, or turn a
concrete hash into a random oracle. Admission forms
`TheoremTruthPropositionId(AFKV2TheoremSchemaId)` but establishes none of it.

<!-- zkc-profile-source:analysis-transport-family-semantics:end -->

<!-- zkc-profile-source:analysis-property-quantitative-semantics:start -->

## 6. Typed quantitative language

### 6.1 Closed sorts

The active language has exactly these sorts:

```text
Nat
LogicalNat
StatementLength(statement_type)
ChallengeCardinality(challenge_set_id)
FamilyChallengeCardinality(family_id,logical_nat_parameter)
FamilyConstantChallengeCardinality(family_id)
QueryCount(resource_dimension)
ExpectedCount(resource_dimension)
Probability
SignedProbabilityLowerBound
ComputationalAdvantage(game_id)
```

`Probability` and `ComputationalAdvantage` do not alias. Neither aliases a raw
Relations export. `SignedProbabilityLowerBound` is not a probability: it is a
basis-neutral exact rational lower-bound sort that may be negative and appears only
on the right-hand side of a declared probability inequality. Every ordinary
numeric constant is a canonical natural or nonnegative rational; floats are
malformed.

### 6.2 Closed expression constructors

```text
BasisNeutralQuantitativeExpr<S> =
    Variable<S>(exact parameter)
  | NaturalConstant(n)                    // Nat only
  | CountConstant<S>(n)                    // exact Count sort S only
  | RationalConstant<S>(num, den)          // declared rational sort, den > 0
  | ApplyQuantitativeFormula(
      AnalysisQuantitativeFormulaId<S>, exact ordered argument expressions)
  | AddSameSort(
      BasisNeutralQuantitativeExpr<S>,
      BasisNeutralQuantitativeExpr<S>)
  | MultiplyNat(
      BasisNeutralQuantitativeExpr<Nat>,
      BasisNeutralQuantitativeExpr<Nat>)
  | ScaleByNat(
      BasisNeutralQuantitativeExpr<Nat>,
      BasisNeutralQuantitativeExpr<S>)
  | QueryBoundPlusOverheadAsExpectedCount(
      BasisNeutralQuantitativeExpr<QueryCount<query_resource>>,
      exact nonnegative overhead,
      exact expected-call resource dimension)
  | PredecessorCount(
      BasisNeutralQuantitativeExpr<S>, exact value >= 1 domain predicate)
  | ModelCardinality(AnalysisChallengeDomainId)
  | FamilyChallengeCardinalityAt(
      AnalysisAsymptoticProtocolFamilyDefinitionId,
      BasisNeutralQuantitativeExpr<LogicalNat>)
  | FamilyConstantChallengeCardinalityValue(
      AnalysisAsymptoticProtocolFamilyDefinitionId)
  | BoundedCountRatioAsProbability(
      numerator_count_expression,
      positive_denominator_count_expression,
      exact compatible-magnitude map,
      exact 0 <= numerator <= denominator domain predicate)
  | ProbabilityDifferenceAsSignedLowerBound(
      BasisNeutralQuantitativeExpr<Probability>,
      BasisNeutralQuantitativeExpr<Probability>)
  | DivideSignedLowerBoundByPositivePolynomial(
      BasisNeutralQuantitativeExpr<SignedProbabilityLowerBound>,
      AnalysisPositivePolynomialId,
      BasisNeutralQuantitativeExpr<the polynomial profile's exact input sort>)
  | ScaleSignedLowerBoundByPositiveCountRatio(
      positive_numerator_count_expression,
      positive_denominator_count_expression,
      exact compatible-magnitude map,
      BasisNeutralQuantitativeExpr<SignedProbabilityLowerBound>)
```

These are basis-neutral arithmetic denotations, not inference rules. They do
not say that a theorem applies, that a loss composes, or that a bound is true.
The count-ratio constructors require an explicit compatible-magnitude map and
their exact positive/range predicates; no ambient coercion relates arbitrary
resource dimensions. There is likewise no ambient rule that probabilities
add, advantages multiply, maxima distribute, retries are free, or out-of-range
results clamp. Wrong dimensions, an absent domain predicate, division by zero,
negative values in a sort that does not admit them, floats, or unsupported
constructors are malformed.

`ApplyQuantitativeFormula` may reference only an already formed formula whose
ordered parameter sorts match exactly. Formula-reference dependencies must be
acyclic; a self-reference, forward cycle, wrong arity, or wrong sort is
malformed.

`FamilyChallengeCardinalityAt(F,n)` is admitted only in a family context that
contains the total-denotation and finite-challenge-set hypotheses for `F`; it
is a symbolic dependent value, not evaluation of a Foundation function. The exact
compatible-magnitude map from a family query count to that cardinality is
selected by the family semantic basis. `ModelCardinality` is the distinct
finite-member constructor and requires an admitted `analysis.challenge-domain`
body. Neither constructor proves its associated hypothesis.

`FamilyConstantChallengeCardinalityValue(F)` is the distinct nominal value of
sort `FamilyConstantChallengeCardinality(F)`. It is formed from the exact family
ID but does not assert that member challenge sets have that size. The AFK
applicability context must retain the exact all-`n` equality
`N_F(n) = FamilyConstantChallengeCardinalityValue(F)` and positivity premise.
Only that checked binding may fill the theorem's fixed-`N` local role.

The one positive polynomial used by the family theorem is global and formed
over `LogicalNat`:

```text
AFKLogicalNatPositivePolynomialProfileBody = {
  input_sort: LogicalNat,
  coefficient_domain: Nat,
  value_shape: exactly coefficients_low_to_high = [1],
  canonical_degree_rule: degree = 0,
  evaluation: exact constant function returning 1,
  positivity_rule: value is 1 for every LogicalNat,
  admitted_coefficient_and_degree_bounds:
    coefficient = 1 and degree = 0
}

AFKLogicalNatPositivePolynomialProfileId =
  AnalysisPositivePolynomialProfileId(
    B,AFKLogicalNatPositivePolynomialProfileBody)

AFKLogicalNatConstantOnePolynomialId = AnalysisPositivePolynomialId(B,{
  profile_id: AFKLogicalNatPositivePolynomialProfileId,
  coefficients_low_to_high: [1]
})
```

The selected positive-polynomial profile admits exactly the singleton value
`[1]`. Consequently the existential `q_KS` in this restricted theorem schema
has one possible witness, `AFKLogicalNatConstantOnePolynomialId`; it cannot be
satisfied by choosing an unrelated polynomial while the transform continues
to divide by one. Expanding that profile rotates every dependent experiment,
formula binding, applicability question, and theorem instance.

The specialized family formula below is formed independently with the
authenticated constant-one ID. It is accepted as this theorem target binding
only after applicability resolves target experiment quantifier ordinal `0`,
checks that its binder uses this exact singleton profile, and binds the theorem-
local polynomial operand to that same `q_KS`. A formula that divides by another
polynomial, a changed quantifier profile, or a transform that does not consume
the binder refuses template equality; the existential is not a vacuous display
binder.

The family target uses separately formed formulas:

```text
AFKFamilyKnowledgeErrorFormulaBody(F) = {
  result_sort: Probability,
  parameter_schema: [
    n: LogicalNat,
    Q: QueryCount<AFKFamilyROQueryDimension(F)>],
  declared_parameter_independence: [n],
  expression:
    BoundedCountRatioAsProbability(
      AddSameSort(
        Q,CountConstant<QueryCount<AFKFamilyROQueryDimension(F)>>(1)),
      FamilyConstantChallengeCardinalityValue(F),
      exact family query-to-challenge magnitude map,
      exact domain
        0 <= Q < FamilyConstantChallengeCardinalityValue(F))
}

AFKFamilyKnowledgeErrorFormulaId(F) =
  AnalysisQuantitativeFormulaId<Probability>(
    B,AFKFamilyKnowledgeErrorFormulaBody(F))

AFKFamilyKnowledgeSuccessFormulaBody(F) = {
  result_sort: SignedProbabilityLowerBound,
  parameter_schema: [
    epsilon: Probability,
    n: LogicalNat,
    Q: QueryCount<AFKFamilyROQueryDimension(F)>],
  declared_parameter_independence: [],
  expression:
    DivideSignedLowerBoundByPositivePolynomial(
      ProbabilityDifferenceAsSignedLowerBound(
        epsilon,ApplyQuantitativeFormula(
          AFKFamilyKnowledgeErrorFormulaId(F),[n,Q])),
      AFKLogicalNatConstantOnePolynomialId,n)
}

AFKFamilyTranscriptExtractionFormulaBody(F) = {
  result_sort: SignedProbabilityLowerBound,
  parameter_schema: [
    epsilon: Probability,
    n: LogicalNat,
    Q: QueryCount<AFKFamilyROQueryDimension(F)>],
  declared_parameter_independence: [],
  expression:
    ScaleSignedLowerBoundByPositiveCountRatio(
      FamilyConstantChallengeCardinalityValue(F),
      PredecessorCount(
        FamilyConstantChallengeCardinalityValue(F),
        exact domain FamilyConstantChallengeCardinalityValue(F)>=2),
      exact family-cardinality magnitude map,
      ProbabilityDifferenceAsSignedLowerBound(
        epsilon,ApplyQuantitativeFormula(
          AFKFamilyKnowledgeErrorFormulaId(F),[n,Q])))
}

AFKFamilyExpectedCallsFormulaBody(F) = {
  result_sort: ExpectedCount<AFKFamilyAdversaryInvocationDimension(F)>,
  parameter_schema: [Q: QueryCount<AFKFamilyROQueryDimension(F)>],
  declared_parameter_independence: [],
  expression:
    QueryBoundPlusOverheadAsExpectedCount(
      Q,2,AFKFamilyAdversaryInvocationDimension(F))
}

AFKFamilyKnowledgeSuccessFormulaId(F) =
  AnalysisQuantitativeFormulaId<SignedProbabilityLowerBound>(
    B,AFKFamilyKnowledgeSuccessFormulaBody(F))
AFKFamilyTranscriptExtractionFormulaId(F) =
  AnalysisQuantitativeFormulaId<SignedProbabilityLowerBound>(
    B,AFKFamilyTranscriptExtractionFormulaBody(F))
AFKFamilyExpectedCallsFormulaId(F) =
  AnalysisQuantitativeFormulaId<
    ExpectedCount<AFKFamilyAdversaryInvocationDimension(F)>>(
      B,AFKFamilyExpectedCallsFormulaBody(F))
```

The family error retains the required `kappa(n,Q)` arity but declares exact
independence from `n`: the selected theorem uses one fixed challenge cardinality
for the protocol family. The family ID supplies only a nominal constant value;
the all-member equality is an applicability premise. No subject-dependent value
is baked into the global AFK theorem schema.

The target property uses these already formed basis-neutral formulas:

```text
AFKKnowledgeErrorFormulaBody(S: AnalysisSubjectTuple) = {
  result_sort: Probability,
  parameter_schema: [
    n: StatementLength(AnalysisStatementType(S)),
    Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [n],
  expression:
    BoundedCountRatioAsProbability(
      AddSameSort(
        Q, CountConstant<AFKAdversaryROQueryCount(S)>(1)),
      ModelCardinality(AnalysisChallengeDomainId(S)),
      exact natural-magnitude map, exact domain 0 <= Q < N)
}

AFKKnowledgeSuccessFormulaBody(S: AnalysisSubjectTuple) = {
  result_sort: SignedProbabilityLowerBound,
  parameter_schema: [
    epsilon: Probability,
    n: StatementLength(AnalysisStatementType(S)),
    Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [],
  expression:
    DivideSignedLowerBoundByPositivePolynomial(
      ProbabilityDifferenceAsSignedLowerBound(
        epsilon,
        BoundedCountRatioAsProbability(
          AddSameSort(
            Q, CountConstant<AFKAdversaryROQueryCount(S)>(1)),
          ModelCardinality(AnalysisChallengeDomainId(S)),
          exact natural-magnitude map, exact domain 0 <= Q < N)),
      AnalysisConstantOnePolynomialId(S), n)
}

AFKTranscriptExtractionFormulaBody(S: AnalysisSubjectTuple) = {
  result_sort: SignedProbabilityLowerBound,
  parameter_schema: [
    epsilon: Probability,
    n: StatementLength(AnalysisStatementType(S)),
    Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [n],
  expression:
    ScaleSignedLowerBoundByPositiveCountRatio(
      ModelCardinality(AnalysisChallengeDomainId(S)),
      PredecessorCount(
        ModelCardinality(AnalysisChallengeDomainId(S)), exact domain N >= 2),
      exact natural-magnitude map,
      ProbabilityDifferenceAsSignedLowerBound(
        epsilon,
        BoundedCountRatioAsProbability(
          AddSameSort(
            Q, CountConstant<AFKAdversaryROQueryCount(S)>(1)),
          ModelCardinality(AnalysisChallengeDomainId(S)),
          exact natural-magnitude map, exact domain 0 <= Q < N)))
}

AFKExpectedCallsFormulaBody(S: AnalysisSubjectTuple) = {
  result_sort: ExpectedCount<AFKAdversaryInvocationResourceDimension(S)>,
  parameter_schema: [Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [],
  expression:
    QueryBoundPlusOverheadAsExpectedCount(
      Q, 2, AFKAdversaryInvocationResourceDimension(S))
}

AFKKnowledgeErrorFormulaId(S: AnalysisSubjectTuple) =
  AnalysisQuantitativeFormulaId<Probability>(
    B, AFKKnowledgeErrorFormulaBody(S))

AFKKnowledgeSuccessFormulaId(S: AnalysisSubjectTuple) =
  AnalysisQuantitativeFormulaId<SignedProbabilityLowerBound>(
    B, AFKKnowledgeSuccessFormulaBody(S))

AFKTranscriptExtractionFormulaId(S: AnalysisSubjectTuple) =
  AnalysisQuantitativeFormulaId<SignedProbabilityLowerBound>(
    B, AFKTranscriptExtractionFormulaBody(S))

AFKExpectedCallsFormulaId(S: AnalysisSubjectTuple) =
  AnalysisQuantitativeFormulaId<
    ExpectedCount<AFKAdversaryInvocationResourceDimension(S)>>(
      B, AFKExpectedCallsFormulaBody(S))
```

The selected error function has the Definition-10 signature
`kappa_FS,S(n,Q)`; `N` is fixed by `AnalysisChallengeDomainId(S)`, and the body is
definitionally independent of `n`. The explicit
independence field is checked against its free variables. Thus the selected
substitution inhabits Definition 10's arity without pretending that the formula
uses the Statement length. `Q + 1` and `Q + 2` use constants in their exact
count dimensions, not ambient `Nat` additions. For `q_KS = 1`, the knowledge-
success formula denotes exactly `epsilon - (Q + 1) / N`; the separate
transcript formula denotes
`N / (N - 1) * (epsilon - (Q + 1) / N)`. Neither silently replaces a negative
lower bound by zero or reclassifies it as a probability.

The global theorem schema owns local typed operator templates but cannot name
family- or member-dependent formula IDs. One applicability semantic basis
binds those local operators to already formed formulas and verifies exact
template equality under its subject substitution:

```text
ApplicableTheoremQuantitativeBinding = {
  theorem_schema_id,
  local_operator: LocalTheoremOperatorRef,
  concrete_operand_and_result_formula_ids,
  exact_subject_and_parameter_substitution,
  checked_template_equality
}
```

This summary is explanatory only and has no `AnalysisBodyV0` arm. The exact
semantic statement is solely `AFKV2TheoremSchemaBody` below.

For family `F`, the AFK applicability basis binds ordinals `0..3` to
`AFKFamilyKnowledgeErrorFormulaId(F)`,
`AFKFamilyKnowledgeSuccessFormulaId(F)`,
`AFKFamilyTranscriptExtractionFormulaId(F)`, and
`AFKFamilyExpectedCallsFormulaId(F)`. The concrete-member specialization binds
the same templates to the four `S` formulas. A different body, dimension,
domain, parameter order, or polynomial refuses applicability. The theorem's
restricted statement occurs in the semantic basis and hypothesis context.
Source authority and proof status occur only in the distinct theorem-source
validation body and in the exact support or validation treatment that consumes
it; they never enter theorem, property, formula, question, or goal identity.

### 6.3 Loss imports

```text
AnalysisLossSemanticImport = {
  relations_bridge_id: ValueBridgeId,
  lossy_use_scope_and_occurrence_coordinate_schema:
    AnalysisProfileLawRef<RelationsLossyUseScopeAndCoordinateSchema>,
  direction: exactly Forward,
  source_semantics: {
    source_premise_proposition_id: AnalysisPropositionId,
    quantitative_export_id: TypedSemanticSubjectRef
  },
  declared_result_sort: AnalysisQuantitativeSort,
  admitted_interpretation_rule:
    AnalysisProfileLawRef<LossExportInterpretationRule>,
  exact_parameter_substitution:
    CanonicalMap<AnalysisParameterSchemaEntry,TypedSemanticSubjectRef>,
  per_occurrence_expression:
    BasisNeutralQuantitativeExpr<declared_result_sort>
}

AnalysisLossSemanticImportBody = AnalysisLossSemanticImport

AnalysisLossSemanticImportId =
  AnalysisId<"analysis.loss-semantic-import">(
    B, AnalysisLossSemanticImportBody)

RequiredAnalysisLanguageProfile(AnalysisLossSemanticImportBody(x)) =
  let P = NarrowestExactImportingProfileOfAuthenticatedPredecessors(
    x.relations_bridge_id,
    x.source_semantics.source_premise_proposition_id,
    x.source_semantics.quantitative_export_id,
    x.admitted_interpretation_rule,
    x.per_occurrence_expression);
  require P in {
    AnalysisCryptographicPropertyLanguageProfileId,
    AnalysisAFKTransportLanguageProfileId};
  return P; otherwise undefined

AnalysisLossSupport = {
  semantic_import_id,
  exact CheckBridgeUseSet result binding,
  exact occurrence-local source-premise result binding,
  exact quantitative-export result binding,
  exact CheckedLossyUseConsumerSource binding,
  owner policy dependency closure
}
```

For the active bounded Schnorr loss import this resolver returns the property
profile. An import whose premise proposition or quantitative export is
F-dependent returns the transport profile; it cannot form under the property
profile and create a reverse dependency. A validation-bearing result binding
is support, not semantic-import input, and therefore cannot force this semantic
constructor into the theorem-source-validation profile.

The complete ledger is derived from the exact Relations selection. Missing,
duplicated, extra, backward, ungrounded, wrong-sort, wrong-source, or stale
entries refuse. The use count is derived; callers never supply it.

An ordinary loss-bearing property formula names a typed quantitative parameter,
not an import occurrence or checked result. `AnalysisSemanticBasis` maps an
exact `AnalysisLossSemanticImportId` and the derived semantic occurrence/count
coordinates to that parameter; concrete checked-result bindings belong to
`SupportInstantiation`, while fresh Relations capabilities and the consumer-source
join are invocation inputs. This keeps property identity independent of its
proof/source basis. If any selected loss result or occurrence is owner-local,
the semantic basis remains portable because it names only the import schema and
occurrence-selection law. The support instantiation, derived judgment, and
later values that actually bind the local occurrence become owner-local and
receive no portable digest or exact cold replay.

An imported `sha256-216` export remains conditional on its exact
preimage/collision premise and occurrence. The generic language does not
invent `m * Adv_collision`; only a selected theorem or rule may specify that
expression.

For a future computational special-soundness profile, the preferred shape is a
tagged extended relation whose extractor returns either a normal relation
Witness or a primitive-break Witness such as a binding/collision break. The FS
theorem can target that extended relation, while a separate exact reduction and
assumption price the primitive-break branch. This preserves occurrence and
outcome meaning more faithfully than an ambient additive collision term.

<!-- zkc-profile-source:analysis-property-quantitative-semantics:end -->

<!-- zkc-profile-source:analysis-transport-application-semantics:start -->

## 7. Exact AFK applicability and family transport

### 7.1 Applicability proposition

The exact applicability question is family-specific while the theorem schema
remains global:

```text
AFKFamilyProjectionCoordinate(F,manifest_schema_id,slot_ordinal) = {
  family_definition_id: F,
  family_read_manifest_schema_id: manifest_schema_id,
  member_source_profile_id:
    ResolvedBody(manifest_schema_id).member_source_profile_id,
  slot_ordinal: the in-range slot in that source profile
}

AFKFamilyQuantifierCoordinate(profile_id,ordinal,expected_kind) = {
  experiment_profile_id: profile_id,
  quantifier_ordinal: ordinal,
  expected_quantifier_kind: expected_kind
}

AFKFamilySemanticRoleBindingTable(F) = CanonicalSeq [
  {AFKLocalStatementRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),0)},
  {AFKLocalWitnessRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),1)},
  {AFKLocalRelationRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),2)},
  {AFKLocalCommitmentRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),3)},
  {AFKLocalChallengeRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),4)},
  {AFKLocalResponseRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),5)},
  {AFKLocalFreshRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),6)},
  {AFKLocalVerifierRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),7)},
  {AFKLocalVerifierOutputRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),8)},
  {AFKLocalPublicSetupRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),9)},
  {AFKLocalFiatShamirRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),10)},
  {AFKLocalProofRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),11)},
  {AFKLocalAuxiliaryOutputRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),12)},
  {AFKLocalRandomOracleIndexRef,
    AFKFamilyProjectionCoordinate(F,AFKFamilyTargetReadManifestSchemaId(F),13)},
  {AFKLocalAcceptanceRef,
    exact symbolic acceptance projection derived from AFKLocalVerifierRef and
    AFKLocalVerifierOutputRef},
  {AFKLocalRandomOracleProcessRef,AFKFamilyRandomOracleProfileId(F)},
  {AFKLocalRandomOracleStatementIndexRef,
    exact Statement-index projection under
    AFKFamilyFiniteIndexAndOperationsGoal(F)},
  {AFKLocalRandomOracleCommitmentIndexRef,
    exact commitment-index projection under
    AFKFamilyFiniteIndexAndOperationsGoal(F)},
  {AFKLocalChallengeSamplerRef,
    exact sampler projection under AFKFamilySamplerAdequacyGoal(F)},
  {AFKLocalBoundedIndexContractRef,
    AnalysisGoalId(B,AFKFamilyFiniteIndexAndOperationsGoal(F))}
]

AFKFamilyLocalBindingSubstitution(F) = CanonicalConcat(
[
  {AFKLocalFamilyRef,F},
  {AFKLocalLogicalNatRef,{
    source: AFKFamilyQuantifierCoordinate(
      AFKFamilySpecialSoundnessExperimentProfileId(F),1,ForAllLogicalNat),
    target: AFKFamilyQuantifierCoordinate(
      AFKFamilyAdaptiveKnowledgeExperimentProfileId(F),2,ForAllLogicalNat)}},
  {AFKLocalPositivePolynomialRef,AFKFamilyQuantifierCoordinate(
    AFKFamilyAdaptiveKnowledgeExperimentProfileId(F),0,
    ExistsPositivePolynomial(AFKLogicalNatPositivePolynomialProfileId))},
  {AFKLocalSourceExtractorRef,AFKFamilyQuantifierCoordinate(
    AFKFamilySpecialSoundnessExperimentProfileId(F),0,
    ExistsUniformExtractorFamily(AFKFamilySourceExtractorProfileId(F)))},
  {AFKLocalAcceptingPairRef,AFKFamilyQuantifierCoordinate(
    AFKFamilySpecialSoundnessExperimentProfileId(F),2,
    ForAllFamilyValue(AcceptingDistinctTranscriptPair))},
  {AFKLocalTargetExtractorRef,AFKFamilyQuantifierCoordinate(
    AFKFamilyAdaptiveKnowledgeExperimentProfileId(F),1,
    ExistsUniformBlackBoxExtractor(AFKFamilyTargetExtractorProfileId(F)))}
],
AFKFamilySemanticRoleBindingTable(F),
[
  {AFKLocalChallengeCardinalityRef,
    FamilyConstantChallengeCardinalityValue(F)},
  {AFKLocalROQueryResourceRef,AFKFamilyROQueryDimension(F)},
  {AFKLocalAdversaryInvocationResourceRef,
    AFKFamilyAdversaryInvocationDimension(F)},
  {AFKLocalQueryBoundRef,AFKFamilyQuantifierCoordinate(
    AFKFamilyAdaptiveKnowledgeExperimentProfileId(F),3,
    ForAllQuantitativeValue(QueryCount<AFKFamilyROQueryDimension(F)>))},
  {AFKLocalAdaptiveProverRef,AFKFamilyQuantifierCoordinate(
    AFKFamilyAdaptiveKnowledgeExperimentProfileId(F),4,
    ForAllStrategy(AFKFamilyAdaptiveProverProfileId(F)))}
])

AFKFamilyApplicabilityPayload(F) = {
  theorem_schema_id: AFKV2TheoremSchemaId,
  applicability_subject_kind: AsymptoticFamilyInstance,
  required_structural_result_schemas_and_coordinates: {
    source_property: AFKV2SourcePropertyComponent,
    target_property: AFKV2TargetPropertyComponent,
    source_experiment: AFKV2SourceExperimentComponent,
    target_experiment: AFKV2TargetExperimentComponent,
    source_views: AFKV2RequiredSourceViewComponents,
    family_definition_id: F,
    source_family_read_manifest_schema_id:
      AFKFamilyFreshReadManifestSchemaId(F),
    target_family_read_manifest_schema_id:
      AFKFamilyTargetReadManifestSchemaId(F),
    source_experiment_profile_id:
      AFKFamilySpecialSoundnessExperimentProfileId(F),
    target_experiment_profile_id:
      AFKFamilyAdaptiveKnowledgeExperimentProfileId(F)
  },
  required_map_schemas_and_exact_map_proposals: {
    map_schemas: AFKV2MapComponents,
    exact_symbolic_role_projections: AFKFamilySemanticRoleBindingTable(F)
  },
  required_side_condition_schemas: AFKV2SideConditionComponents,
  exact_local_binding_substitution:
    AFKFamilyLocalBindingSubstitution(F),
  exact_typed_transform_instantiation: {
    transform_program: AFKV2TransformProgramComponent,
    conclusion_law: AFKV2ConclusionLawComponent,
    exact_parameter_specialization: {
      k: 2,
      positive_polynomial_profile: AFKLogicalNatPositivePolynomialProfileId,
      selected_positive_polynomial_value:
        AFKLogicalNatConstantOnePolynomialId,
      challenge_cardinality: FamilyConstantChallengeCardinalityValue(F),
      query_dimension: AFKFamilyROQueryDimension(F),
      adversary_invocation_dimension:
        AFKFamilyAdversaryInvocationDimension(F),
      exact_domain:
        0 <= AFKLocalQueryBoundRef and
        AFKLocalQueryBoundRef < FamilyConstantChallengeCardinalityValue(F)
    },
    local_operator_bindings: [
      {0,AFKFamilyKnowledgeErrorFormulaId(F)},
      {1,AFKFamilyKnowledgeSuccessFormulaId(F)},
      {2,AFKFamilyTranscriptExtractionFormulaId(F)},
      {3,AFKFamilyExpectedCallsFormulaId(F)}
    ]
  }
}

AFKFamilyApplicabilitySelection(F) = AsymptoticFamilySelection {
  theorem_schema_id: AFKV2TheoremSchemaId,
  family_definition_id: F,
  source_family_read_manifest_schema_id:
    AFKFamilyFreshReadManifestSchemaId(F),
  target_family_read_manifest_schema_id:
    AFKFamilyTargetReadManifestSchemaId(F),
  source_family_experiment_profile_id:
    AFKFamilySpecialSoundnessExperimentProfileId(F),
  target_family_experiment_profile_id:
    AFKFamilyAdaptiveKnowledgeExperimentProfileId(F)
}

AFKFamilyApplicabilityQuestion(F) = TheoremApplicabilityQuestion(
  AFKFamilyApplicabilitySelection(F),AFKFamilyApplicabilityPayload(F))

AFKFamilyApplicabilityGoal(F) = TheoremApplicabilityGoal(
  AFKFamilyApplicabilitySelection(F),AFKFamilyApplicabilityPayload(F))

AFKApplicabilityPremiseQuestion(F,family,payload) = AnalysisQuestionBody {
  family,
  exact_subjects: [AFKV2TheoremSchemaId,F],
  context: FamilySemanticExperimentContext {
    family_definition_id: F,
    family_read_manifest_schema_ids: [
      AFKFamilyFreshReadManifestSchemaId(F),
      AFKFamilyTargetReadManifestSchemaId(F)
    ],
    family_experiment_profile_ids: [
      AFKFamilySpecialSoundnessExperimentProfileId(F),
      AFKFamilyAdaptiveKnowledgeExperimentProfileId(F)
    ]
  },
  family_payload: payload,
  named_premise_requirements: NamedPremiseRequirementsOf(family, exact_subjects)
}

AFKApplicabilityPremiseGoal(F,family,payload) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(
    B,AFKApplicabilityPremiseQuestion(F,family,payload)),
  named_premise_bindings: {}
}

AFKFamilyFreshDistributionGoal(F) = AFKApplicabilityPremiseGoal(
  F,FreshUniformIndependentPublicCoin,{
    exact_proposition:
      `for every n, Fresh_F(n)'s challenge is uniform on ChallengeSet_F(n),
       independent of the prover's prior view, with exactly
       AFKFamilyConstantChallengeCardinality(F) outcomes`
  })

AFKFamilyFixedChallengeCardinalityGoal(F) = AFKApplicabilityPremiseGoal(
  F,FixedFamilyChallengeCardinality,{
    exact_proposition:
      `AFKFamilyConstantChallengeCardinality(F) is finite and at least 2, and
       for every LogicalNat n it equals MathematicalCardinality(
       ChallengeSet_F(n)); this is the one fixed N used by the theorem`
  })

AFKFamilyRandomOracleCorrespondenceGoal(F) = AFKApplicabilityPremiseGoal(
  F,ExactClassicalRandomOracleProcess,{
    exact_proposition:
      `for every n,Q,P^a, the complete adaptive query/answer process is one
       lazy random function on all indices, including repeats, off-image
       queries, and the extractor's authorized programming operations`
  })

AFKFamilyFiniteIndexAndOperationsGoal(F) = AFKApplicabilityPremiseGoal(
  F,FiniteBoundedRandomOracleIndexAndEfficientOperations,{
    exact_proposition:
      `for every n, RandomOracleIndex_F(n) is exactly the finite domain of
       bitstrings of length at most the authenticated bound u_F(n); the
       Statement/commitment framing is one canonical injective encoding into
       that domain; index enumeration, equality, encoding, challenge sampling,
       and table operations satisfy the selected uniform polynomial-time laws;
       and every table access, including repeats and off-image indices, is one
       AFKFamilyROQueryDimension(F) event`
  })

AFKFamilyFixedSetupGoal(F) = AFKApplicabilityPremiseGoal(
  F,FixedPublicSetupIndependence,{
    exact_proposition:
      `PublicSetup_F(n) is public and fixed before and independently of P^a
       and both random-oracle spaces for every n`
  })

AFKFamilySamplerAdequacyGoal(F) = AFKApplicabilityPremiseGoal(
  F,TotalUniformChallengeSamplerAdequacy,{
    exact_proposition:
      `the Fresh and Fiat--Shamir challenge interfaces are total, exactly
       uniform on ChallengeSet_F(n), and preserve theorem query accounting`
  })

AFKFamilyExperimentObservationCorrespondenceGoal(F) =
AFKApplicabilityPremiseGoal(
  F,AFKExperimentObservationCorrespondence,{
    exact_proposition:
      `under the structurally checked role maps, the family source and target
       experiment denotations preserve exactly acceptance, relation
       membership, fixed setup, the two probability spaces, the
       (Statement,proof,aux,verifier-output) marginal, and resource units`
  })

GammaAFKApplicabilityBody(F) = AnalysisHypothesisContextBody {
  nodes: [
    {0,AnalysisGoalId(B,AFKFamilyDenotationGoal(F)),[], premises(goal)},
    {1,AnalysisGoalId(B,AFKFamilyProjectionCoherenceGoal(F)),[0], premises(goal)},
    {2,AnalysisGoalId(B,AFKFamilyFixedChallengeCardinalityGoal(F)),[0,1], premises(goal)},
    {3,AnalysisGoalId(B,AFKFamilyFreshDistributionGoal(F)),[0,1,2], premises(goal)},
    {4,AnalysisGoalId(B,AFKFamilyRandomOracleCorrespondenceGoal(F)),[0,1], premises(goal)},
    {5,AnalysisGoalId(B,AFKFamilyFiniteIndexAndOperationsGoal(F)),[0,1,4], premises(goal)},
    {6,AnalysisGoalId(B,AFKFamilyFixedSetupGoal(F)),[0,1], premises(goal)},
    {7,AnalysisGoalId(B,AFKFamilySamplerAdequacyGoal(F)),[0,1,2,4,5], premises(goal)},
    {8,AnalysisGoalId(
         B,AFKFamilyExperimentObservationCorrespondenceGoal(F)),
       [0,1,2,3,4,5,6,7], premises(goal)}
  ],
  roots: [8],
  exact_named_premise_ids: ContextPremiseIds(nodes, roots)
}

GammaAFKApplicabilityId(F) =
  AnalysisHypothesisContextId(B,GammaAFKApplicabilityBody(F))

AFKFamilyApplicabilityPropositionBody(F) = AnalysisPropositionBody {
  goal_id: AnalysisGoalId(B,AFKFamilyApplicabilityGoal(F)),
  hypothesis_context_id: GammaAFKApplicabilityId(F)
}
```

The theorem-local quantitative ordinals are bound only in the semantic basis:

```text
AFKFamilyApplicabilitySemanticBasisBody(F) = AnalysisSemanticBasisBody {
  family: TheoremApplicability,
  exact_question_id:
    AnalysisQuestionId(B,AFKFamilyApplicabilityQuestion(F)),
  rule_source: AnalysisNativeRule(
    ExactTheoremApplicabilityCheckRuleRef,{
      theorem_schema_id: AFKV2TheoremSchemaId,
      family_definition_id: F,
      source_property_schema: AFKV2SourcePropertyComponent,
      target_property_schema: AFKV2TargetPropertyComponent,
      transform_program: AFKV2TransformProgramComponent,
      conclusion_law: AFKV2ConclusionLawComponent
    }),
  exact_premise_schemas:
    AllReachableHypothesisNodeRequirements(
      GammaAFKApplicabilityId(F),GammaAFKApplicabilityBody(F)),
  source_read_purposes: ExactCryptographicReadPurposes([],[
    AFKFamilyFreshReadManifestSchemaId(F),
    AFKFamilyTargetReadManifestSchemaId(F)
  ]),
  conclusion_schema: AFKFamilyApplicabilityGoal(F),
  typed_transform_program: [
    bind LocalTheoremOperatorRef(0) to
      AFKFamilyKnowledgeErrorFormulaId(F),
    bind LocalTheoremOperatorRef(1) to
      AFKFamilyKnowledgeSuccessFormulaId(F),
    bind LocalTheoremOperatorRef(2) to
      AFKFamilyTranscriptExtractionFormulaId(F),
    bind LocalTheoremOperatorRef(3) to
      AFKFamilyExpectedCallsFormulaId(F),
    substitute k=2, q=AFKLogicalNatConstantOnePolynomialId,
      challenge cardinality=FamilyConstantChallengeCardinalityValue(F), and
      query dimension=AFKFamilyROQueryDimension(F),
    require exact template equality for all four bindings
  ]
}

AFKFamilyApplicabilitySemanticBasisId(F) =
  AnalysisSemanticBasisId(B,AFKFamilyApplicabilitySemanticBasisBody(F))

AFKFamilyApplicabilitySupportSchemaBody(
    F,established_nodes,assumed_nodes,fresh_support,target_support) =
  AnalysisSupportInstantiationBody {
    semantic_basis_id: AFKFamilyApplicabilitySemanticBasisId(F),
    proposition_id: AnalysisPropositionId(
      B,AFKFamilyApplicabilityPropositionBody(F)),
    exact_named_premise_ids: PremiseIdsOfProposition(proposition_id),
    non_hypothesis_premise_bindings:
      ExactNonHypothesisPremiseBindingMap(
        AFKFamilyApplicabilitySemanticBasisId(F),
        AFKFamilyApplicabilitySemanticBasisBody(F),[]),
    established_hypothesis_node_bindings: established_nodes,
    assumed_hypothesis_node_bindings: assumed_nodes,
    source_support_bindings: [
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyFreshReadManifestSchemaId(F),
        dependent_support_schema: fresh_support,
        exact_retained_family_support_hypotheses:
          ReachableHypothesisGoalIds(
            GammaAFKApplicabilityId(F),GammaAFKApplicabilityBody(F))
      },
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyTargetReadManifestSchemaId(F),
        dependent_support_schema: target_support,
        exact_retained_family_support_hypotheses:
          ReachableHypothesisGoalIds(
            GammaAFKApplicabilityId(F),GammaAFKApplicabilityBody(F))
      }
    ]
  }

AFKFamilyApplicabilitySupportId(
    F,established_nodes,assumed_nodes,fresh_support,target_support) =
  AnalysisId<"analysis.support-instantiation">(B,
    AFKFamilyApplicabilitySupportSchemaBody(
      F,established_nodes,assumed_nodes,fresh_support,target_support))

AFKFamilyApplicabilityValidationBasisBody(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  ExactAnalysisValidationBasisBody(
    checker_contracts,translations,finite_controls,[],residual_trust_roots)

AFKFamilyApplicabilityValidationBasisId(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  AnalysisId<"analysis.validation-basis">(B,
    AFKFamilyApplicabilityValidationBasisBody(
      checker_contracts,translations,finite_controls,residual_trust_roots))

AFKFamilyApplicabilityOperationPolicyBody(F) =
  ExactAnalysisOperationPolicyBody(
    AnalysisPropositionId(B,AFKFamilyApplicabilityPropositionBody(F)),
    CanonicalMap {
      AFKFamilyPropertyTransportConsumerRef:
        CanonicalSingleton(AFKExactTheoremFamilyTransportPurposeRef)
    },
    AFKFamilyApplicabilityPolicyLawBundleRef)

AFKFamilyApplicabilityOperationPolicyId(F) =
  AnalysisId<"analysis.operation-policy">(
    B,AFKFamilyApplicabilityOperationPolicyBody(F))

AFKFamilyApplicabilityJudgmentBody(
    F,support_id,validation_basis_id) =
  ExactAffirmativeAnalysisJudgmentBody(
    AnalysisPropositionId(B,AFKFamilyApplicabilityPropositionBody(F)),
    NoQuantitativeResult,
    AFKFamilyApplicabilitySemanticBasisId(F),
    support_id,validation_basis_id,
    AFKFamilyApplicabilityQualificationRef,
    AFKFamilyApplicabilityOperationPolicyId(F))

AFKFamilyApplicabilityJudgmentId(F,support_id,validation_basis_id) =
  AnalysisId<"analysis.judgment-record">(B,
    AFKFamilyApplicabilityJudgmentBody(
      F,support_id,validation_basis_id))

AFKFamilyApplicabilityJudgmentSchema(F) = {
  exact_judgment_constructor: AFKFamilyApplicabilityJudgmentId,
  result: conditional affirmative theorem applicability inheriting exactly
    GammaAFKApplicabilityId(F),
  live_capability_permission:
    AFKFamilyPropertyTransportConsumerRef ->
      AFKExactTheoremFamilyTransportPurposeRef
}
```

`AFKFamilyApplicabilityPolicyLawBundleRef` is the one exact transport-profile
operation-policy law bundle for this result. It permits only the displayed
attenuated family-transport use and otherwise applies the common Analysis
freshness, disclosure, persistence, unknown-question, and replay laws.

The established and assumed maps are disjoint and partition all nine
reachable nodes; the unique outward root frontier is `[8]`. The native rule
checks structure against `AFKV2TheoremSchemaId`; the theorem schema is input
data, not the rule that proves its own applicability. Theorem truth is absent
because applicability is a structural/model-matching judgment. Applicability
does not establish the source property, and its port cannot occupy either the
source-property or theorem-truth slot.

### 7.2 Family property transport

Use the one closed `CanonicalGoalDagUnion` constructor from
[`analysis-model.md`](analysis-model.md#41-one-identity-algebra). The transported
proposition inherits, but does not duplicate, the source and applicability
premises:

```text
GammaAFKTheoremTruthBody = AnalysisHypothesisContextBody {
  nodes: [{0,AnalysisGoalId(
    B,TheoremTruthGoal(AFKV2TheoremSchemaId)),[], premises(goal)}],
  roots: [0],
  exact_named_premise_ids: ContextPremiseIds(nodes, roots)
}

GammaAFKFamilyTargetBody(F) = CanonicalGoalDagUnion([
  GammaAFKFamilySpecialBody(F),
  GammaAFKApplicabilityBody(F),
  GammaAFKTheoremTruthBody
])

GammaAFKFamilyTargetId(F) =
  AnalysisHypothesisContextId(B,GammaAFKFamilyTargetBody(F))

AFKFamilyAdaptiveKnowledgePropositionBody(F) = AnalysisPropositionBody {
  goal_id: AnalysisGoalId(B,AFKFamilyAdaptiveKnowledgeGoal(F)),
  hypothesis_context_id: GammaAFKFamilyTargetId(F)
}

AFKFamilyTransportSemanticBasisBody(F) = AnalysisSemanticBasisBody {
  family: AdaptiveKnowledgeSoundnessQltN,
  exact_question_id:
    AnalysisQuestionId(B,AFKFamilyAdaptiveKnowledgeQuestion(F)),
  rule_source: ImportedTheoremRuleSource(AFKV2TheoremSchemaId),
  exact_premise_schemas: CanonicalAppend(
    AllReachableHypothesisNodeRequirements(
      GammaAFKFamilyTargetId(F),GammaAFKFamilyTargetBody(F)),
    [
      AffirmativeJudgmentCapabilityRequirement {
        proposition_id:
          AnalysisPropositionId(B,AFKFamilySpecialSoundnessPropositionBody(F)),
        conclusion_family: AsymptoticKOutOfNSpecialSoundness,
        required_qualification: ExactInheritedConditionalQualificationRef,
        named_consumer: AFKFamilyPropertyTransportConsumerRef,
        typed_purpose: AFKTheoremSourcePropertyPurposeRef
      },
      AffirmativeJudgmentCapabilityRequirement {
        proposition_id:
          AnalysisPropositionId(B,AFKFamilyApplicabilityPropositionBody(F)),
        conclusion_family: TheoremApplicability,
        required_qualification: ExactInheritedConditionalQualificationRef,
        named_consumer: AFKFamilyPropertyTransportConsumerRef,
        typed_purpose: AFKExactTheoremFamilyTransportPurposeRef
      }
    ]),
  source_read_purposes: ExactCryptographicReadPurposes(
    [],[AFKFamilyTargetReadManifestSchemaId(F)]),
  conclusion_schema: AFKFamilyAdaptiveKnowledgeGoal(F),
  typed_transform_program:
    independently reconstruct the target goal and its three quantitative
    results from the checked applicability bindings, then inherit the exact
    canonical union of both premise DAGs
}

AFKFamilyTransportSemanticBasisId(F) =
  AnalysisSemanticBasisId(B,AFKFamilyTransportSemanticBasisBody(F))

AFKTheoremTruthNodeTreatment =
    EstablishedTheoremTruth {
      exact_affirmative_binding:
        ExactAffirmativeJudgmentCapabilityBinding<
          TheoremTruthPropositionId(AFKV2TheoremSchemaId)>,
      theorem_source_validation_id: AnalysisTheoremSourceValidationId,
      requirement:
        the binding's authenticated judgment validation basis contains
        exactly this validation ID, whose body names AFKV2TheoremSchemaId and
        selects EstablishedByCheckedProof; formation separately consumes the
        matching fresh capability and does not serialize it
    }
  | AssumedTheoremTruth {
      exact_goal_id:
        AnalysisGoalId(B,TheoremTruthGoal(AFKV2TheoremSchemaId)),
      theorem_source_validation_id: AFKV2TheoremSourceValidationId,
      requirement:
        the resolved validation body selects ImportedPaperOnly and
        RetainedTheoremTruthAssumption
    }

InheritedAFKFamilyTargetSupportPartition(
    F,source_property_binding,applicability_binding,
    theorem_truth_node_treatment:AFKTheoremTruthNodeTreatment) =
  authenticate the exact support records named by both portable bindings and
  separately require their matching fresh invocation capabilities; project
  their treatment of every node in GammaAFKFamilySpecialBody(F) and
  GammaAFKApplicabilityBody(F); add the exact theorem-truth node treatment; map
  equal goals through GammaAFKFamilyTargetBody(F); mark a merged node
  established when at least one exact affirmative node capability establishes
  it and otherwise Assumed when at least one authenticated input retains it;
  encode the theorem-truth assumed entry as `ExactlyAssumedGoal` with
  `ImportedTheoremSourceValidation(AFKV2TheoremSourceValidationId)` and every
  ordinary assumed entry with `NoExternalSourceValidation`;
  reject a missing node, unrelated capability, unsupported treatment, or any
  source-validation ID naming another theorem, and reject any output domain
  other than every node of GammaAFKFamilyTargetBody(F); return
  ExactHypothesisTreatmentPartition(
    GammaAFKFamilyTargetId(F),GammaAFKFamilyTargetBody(F),
    the derived complete treatment map)

RequiredAnalysisLanguageProfile(AFKFamilyTransportSemanticBasisBody) =
  AnalysisAFKTransportLanguageProfileId
RequiredAnalysisLanguageProfile(AFKFamilyAdaptiveKnowledgePropositionBody) =
  AnalysisAFKTransportLanguageProfileId
RequiredAnalysisLanguageProfile(AFKFamilyTransportSupportBody) =
  AnalysisAFKTheoremSourceValidationLanguageProfileId
RequiredAnalysisLanguageProfile(AFKFamilyTransportValidationBasisBody) =
  AnalysisAFKTheoremSourceValidationLanguageProfileId
RequiredAnalysisLanguageProfile(AFKFamilyTransportJudgmentBody) =
  AnalysisAFKTheoremSourceValidationLanguageProfileId

AFKFamilyTransportSupportBody(
    F,source_property_binding,applicability_binding,
    theorem_truth_node_treatment,
    target_family_support_schema) =
  AnalysisSupportInstantiationBody {
    semantic_basis_id: AFKFamilyTransportSemanticBasisId(F),
    proposition_id: AnalysisPropositionId(
      B,AFKFamilyAdaptiveKnowledgePropositionBody(F)),
    exact_named_premise_ids: PremiseIdsOfProposition(proposition_id),
    non_hypothesis_premise_bindings:
      ExactNonHypothesisPremiseBindingMap(
        AFKFamilyTransportSemanticBasisId(F),
        AFKFamilyTransportSemanticBasisBody(F),
        [source_property_binding,applicability_binding]),
    established_hypothesis_node_bindings:
      EstablishedPartitionOf(InheritedAFKFamilyTargetSupportPartition(
        F,source_property_binding,applicability_binding,
        theorem_truth_node_treatment)),
    assumed_hypothesis_node_bindings:
      AssumedPartitionOf(InheritedAFKFamilyTargetSupportPartition(
        F,source_property_binding,applicability_binding,
        theorem_truth_node_treatment)),
    source_support_bindings: [FamilyManifestSupportSchemaBinding {
      family_read_manifest_schema_id: AFKFamilyTargetReadManifestSchemaId(F),
      dependent_support_schema: target_family_support_schema,
      exact_retained_family_support_hypotheses:
        ReachableHypothesisGoalIds(
          GammaAFKFamilyTargetId(F),GammaAFKFamilyTargetBody(F))
    }]
  }

AFKFamilyTransportSupportId(
    F,source_property_binding,applicability_binding,
    theorem_truth_node_treatment,target_family_support_schema) =
  AnalysisId<"analysis.support-instantiation">(
    B,AFKFamilyTransportSupportBody(
      F,source_property_binding,applicability_binding,
      theorem_truth_node_treatment,target_family_support_schema))

AFKFamilyTransportValidationBasisBody(
    theorem_truth_node_treatment,
    admitted_transport_checker_contracts,
    exact_translation_contracts,
    finite_control_contracts,
    residual_trust_roots) =
  ExactAnalysisValidationBasisBody(
    admitted_transport_checker_contracts,
    exact_translation_contracts,
    finite_control_contracts,
    DirectlyConsumedTheoremSourceValidationIds(
      theorem_truth_node_treatment),
    residual_trust_roots)

DirectlyConsumedTheoremSourceValidationIds(treatment) =
  CanonicalSingleton(treatment.theorem_source_validation_id)
    when treatment is EstablishedTheoremTruth and the checking attempt
      consumes its exact CheckedProofArtifact validation;
  [] when treatment is AssumedTheoremTruth, because that exact imported-paper
      validation ID already occurs solely in the assumed support binding;
  undefined for any other or incoherent treatment

AFKFamilyTransportValidationBasisId(
    theorem_truth_node_treatment,
    admitted_transport_checker_contracts,
    exact_translation_contracts,
    finite_control_contracts,
    residual_trust_roots) =
  AnalysisId<"analysis.validation-basis">(
    B,AFKFamilyTransportValidationBasisBody(
      theorem_truth_node_treatment,
      admitted_transport_checker_contracts,
      exact_translation_contracts,
      finite_control_contracts,
      residual_trust_roots))

AFKFamilyTransportOperationPolicyBody(F) =
  ExactAnalysisOperationPolicyBody(
    AnalysisPropositionId(B,AFKFamilyAdaptiveKnowledgePropositionBody(F)),
    CanonicalMap {
      AFKMemberSpecializationConsumerRef:
        CanonicalSingleton(AFKFamilyTargetSpecializationPurposeRef)
    },
    AFKFamilyTransportPolicyLawBundleRef)

AFKFamilyTransportOperationPolicyId(F) =
  AnalysisId<"analysis.operation-policy">(
    B,AFKFamilyTransportOperationPolicyBody(F))

AFKFamilyTransportJudgmentBody(
    F,transport_support_id,transport_validation_basis_id) =
  ExactAffirmativeAnalysisJudgmentBody(
    AnalysisPropositionId(B,AFKFamilyAdaptiveKnowledgePropositionBody(F)),
    [
      AFKFamilyKnowledgeErrorFormulaId(F),
      AFKFamilyKnowledgeSuccessFormulaId(F),
      AFKFamilyExpectedCallsFormulaId(F)
    ],
    AFKFamilyTransportSemanticBasisId(F),
    transport_support_id,transport_validation_basis_id,
    AFKFamilyTransportQualificationRef,
    AFKFamilyTransportOperationPolicyId(F))

AFKFamilyTransportJudgmentId(
    F,transport_support_id,transport_validation_basis_id) =
  AnalysisId<"analysis.judgment-record">(
    B,AFKFamilyTransportJudgmentBody(
      F,transport_support_id,transport_validation_basis_id))

AFKFamilyTransportJudgmentSchema(F) = {
  judgment_id: the exact AFKFamilyTransportJudgmentId above,
  result: conditional affirmative AdaptiveKnowledgeSoundnessQltN judgment,
  live_capability:
    bound to this exact family proposition, hypotheses, model, and purpose
}
```

A source judgment for a different family, a structural FS result,
an applicability port for another family, or a target proposition supplied by
the caller refuses. Transport never discharges theorem truth, family laws, or
the ROM assumptions merely because they were retained by both inputs.
Formation derives `derived_source_policy_closure` from exactly the source-
property, applicability, and theorem-truth authority bindings; it is never a
caller assertion. The validation body admits at least one exact checker
contract, authenticates every translation, finite-control, and residual-trust
entry, and contains the selected theorem-source-validation ID exactly for an
established checked-proof treatment and no such ID for an assumed treatment;
the assumed support binding already authenticates it. The support, validation,
judgment, checked-result coordinate,
and authority envelope therefore select the source-validation child profile,
while the proposition and semantic basis remain under the transport parent.
Fresh capabilities are required to form and use the result but have no
`AnalysisBodyV0` encoding and never enter any ID above.

`AFKFamilyTransportPolicyLawBundleRef` is the exact source-validation-profile
operation-policy bundle for this result. It permits only the displayed
member-specialization consumer/purpose pair and applies the exact common
freshness, disclosure, unknown-question, persistence, and cold-replay laws.

### 7.3 Family premises

A question about a Fiat--Shamir Protocol consumes two named premises for its
family, owned by this profile: that the family's sampler is adequate, and that
the oracle process the experiment assumes is the one the construction
realizes. Both are stated for one exact oracle model, the distribution profile
the experiment uses.

```text
NamedHypothesisArgumentSchema<AnalysisAFKTransportLanguageProfileId, K> =
    [ coordinate: AnalysisFamilyPremiseCoordinate(_, SamplerAdequacy),
      oracle_model: AnalysisDistributionProfileId,
      form: SamplerAdequacyForm ]
        when K = FiatShamirSamplerAdequacy
  | [ coordinate: AnalysisFamilyPremiseCoordinate(_, OracleProcess),
      oracle_model: AnalysisDistributionProfileId ]
        when K = FiatShamirOracleProcess

SamplerAdequacyHypothesis =
  ExactNamedHypothesis<AnalysisAFKTransportLanguageProfileId,
                       FiatShamirSamplerAdequacy> whose canonical arguments
  are [ coordinate: AnalysisFamilyPremiseCoordinate(F, SamplerAdequacy),
  oracle_model: AnalysisDistributionProfileId, form: SamplerAdequacyForm ]:
  the family's challenge sampler over that oracle model is adequate in the
  named form, with the exhaustion term explicit when the form retries

OracleProcessHypothesis =
  ExactNamedHypothesis<AnalysisAFKTransportLanguageProfileId,
                       FiatShamirOracleProcess> whose canonical arguments are
  [ coordinate: AnalysisFamilyPremiseCoordinate(F, OracleProcess),
  oracle_model: AnalysisDistributionProfileId ]: the oracle process the
  experiment assumes over that model is the one the family's construction
  realizes, including adaptive queries and answers

SamplerAdequacyFormOf(F: AnalysisAsymptoticProtocolFamilyDefinitionId) =
  ExactTotal, the form named by the family's sampler-adequacy applicability
  premise TotalUniformChallengeSamplerAdequacy
  (AFKFamilySamplerAdequacyGoal(F)); this profile declares no retrying
  family sampler

FiatShamirFamilySamplerPremise(
    F: AnalysisAsymptoticProtocolFamilyDefinitionId,
    oracle_model: AnalysisDistributionProfileId,
    form: SamplerAdequacyForm,
    source: AnalysisNamedPremiseSource<AnalysisAFKTransportLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisAFKTransportLanguageProfileId,
                           FiatShamirSamplerAdequacy> {
    kind: exactly FiatShamirSamplerAdequacy,
    coordinate: AnalysisFamilyPremiseCoordinate(F, SamplerAdequacy),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's SamplerAdequacyHypothesis declaration,
      canonical_arguments: [AnalysisFamilyPremiseCoordinate(F, SamplerAdequacy),
                            oracle_model, form]
    }),
    source,
    evidence_depth,
    model_scope: OracleModelOnly(oracle_model)
  }

FiatShamirFamilyOracleProcessPremise(
    F: AnalysisAsymptoticProtocolFamilyDefinitionId,
    oracle_model: AnalysisDistributionProfileId,
    source: AnalysisNamedPremiseSource<AnalysisAFKTransportLanguageProfileId>,
    evidence_depth: AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<AnalysisAFKTransportLanguageProfileId,
                           FiatShamirOracleProcess> {
    kind: exactly FiatShamirOracleProcess,
    coordinate: AnalysisFamilyPremiseCoordinate(F, OracleProcess),
    bound_model_or_hypothesis: BoundHypothesis(AnalysisLawTerm {
      law_ref: the profile's OracleProcessHypothesis declaration,
      canonical_arguments: [AnalysisFamilyPremiseCoordinate(F, OracleProcess),
                            oracle_model]
    }),
    source,
    evidence_depth,
    model_scope: OracleModelOnly(oracle_model)
  }

AFKTransportPropertyFamilyRef(family) =
  AnalysisProfileDeclarationRef<AnalysisAFKTransportLanguageProfileId,
                                "analysis.property-family">
  naming the transport profile's own declaration of family, a member of
  AnalysisAFKTransportFamilyCoordinates (Section 2.1)

FiatShamirNamedPremiseRequirements(F, oracle_model) =
  CanonicalSortedUniqueSeq [
    { slot: "sampler", kind: FiatShamirSamplerAdequacy,
      coordinate: AnalysisFamilyPremiseCoordinate(F, SamplerAdequacy) },
    { slot: "oracle-process", kind: FiatShamirOracleProcess,
      coordinate: AnalysisFamilyPremiseCoordinate(F, OracleProcess) }
  ]

FiatShamirFamilyPremiseBindings(F) =
  the binding map IntakeAnalysisNamedPremises(
    AFKFamilyAdaptiveKnowledgeQuestion(F), supplied) forms, where supplied
  binds
    "sampler"        -> PremiseIdOf(FiatShamirFamilySamplerPremise(F,
                          AFKFamilyRandomOracleProfileId(F),
                          SamplerAdequacyFormOf(F),
                          FamilyHypothesisSource(
                            AFKTransportPropertyFamilyRef(
                              TotalUniformChallengeSamplerAdequacy)),
                          SourceGroundedMapping)),
    "oracle-process" -> PremiseIdOf(FiatShamirFamilyOracleProcessPremise(F,
                          AFKFamilyRandomOracleProfileId(F),
                          FamilyHypothesisSource(
                            AFKTransportPropertyFamilyRef(
                              ExactClassicalRandomOracleProcess)),
                          SourceGroundedMapping))
```

The source of a family hypothesis is the property family that declares the
hypothesis, an `AnalysisFamilyCoordinate` of the transport profile; the
asymptotic family `F` is already the subject of the premise coordinate and is
a semantic subject identity, not a declaration reference, so it is never
passed where the source constructor requires one.

For the classical adaptive experiment of Section 4 the oracle model is
`AFKClassicalRandomOracleProfileId(S)`, and a question about a Fiat--Shamir
Protocol of family `F` carries `FiatShamirNamedPremiseRequirements(F,
AFKClassicalRandomOracleProfileId(S))` as its requirement sequence. A
quantum-random-oracle or concrete-process model needs distinct premise bodies
with their own scope; no family or spelling match transports a premise from
one model to another, and a premise whose scope is another model is refused
by the intake. The three hypothesis law families and the provider declaration
and carrier families are `analysis.semantic-law` declarations of their
profiles; none is published yet, and until one is, no premise of its kind can
be formed.

## 8. Concrete member correspondence and specialization

### 8.1 One representable member

Concrete native objects are related to the abstract family only at one exact
representable index:

```text
AnalysisLogicalNatLiteralBody(n0) = MetaRecord {0: MetaNatural(n0)}
AnalysisLogicalNatLiteralId(n0) =
  AnalysisId<"analysis.logical-nat-literal">(
    B,AnalysisLogicalNatLiteralBody(n0))

RequiredAnalysisLanguageProfile(AnalysisLogicalNatLiteralBody) =
  AnalysisAFKTransportLanguageProfileId

AFKFamilyRoleCatalog = CanonicalSeq [
  {0,Statement},
  {1,Witness},
  {2,Relation},
  {3,PublicSetup},
  {4,Commitment},
  {5,ChallengeSet},
  {6,Response},
  {7,FreshExperiment},
  {8,FiatShamirExperiment},
  {9,Proof},
  {10,AuxiliaryOutput},
  {11,Verifier},
  {12,VerifierOutput},
  {13,RandomOracleIndex},
  {14,StatementLength},
  {15,RandomOracleQueryResource},
  {16,AdversaryInvocationResource},
  {17,ConstantOnePolynomialProfile},
  {18,ConstantOnePolynomialValueAtIndex},
  {19,FixedChallengeCardinality}
]

AFKFamilyRoleCatalogDeclarationBody = {
  roles: AFKFamilyRoleCatalog,
  ordinal_law: exactly zero-based, contiguous, unique, and in displayed order,
  role_semantics:
    exactly the abstract/native symbolic-resolution and map-clause tables below
}

AFKFamilyRoleCatalogRef =
  the one exact AnalysisProfileDeclarationRef<
    "analysis.afk-family-role-catalog"> whose
  resolved declaration body is AFKFamilyRoleCatalogDeclarationBody

AFKFamilyRoleCoordinate(i) = {
  catalog_ref: AFKFamilyRoleCatalogRef,
  local_role_ordinal: i : Natural with 0 <= i < 20,
  exact_role_tag: AFKFamilyRoleCatalog[i].role_tag
}

AFKAbstractFamilyMemberRoleRef(F,n0_literal,role) = {
  family_definition_id: F,
  logical_index_id: n0_literal,
  role: role : AFKFamilyRoleCoordinate(role.local_role_ordinal)
}

AFKNativeSubjectRefs(S) = CanonicalAppend(
  AFKTargetSubjectProjection(S),
  [AnalysisChallengeDomainId(S),AFKFixedPublicSetupId(S)])

AFKNativeMemberRoleRef(S,ell0,role) = {
  native_subject_refs: AFKNativeSubjectRefs(S),
  native_statement_length: ell0,
  role: role : AFKFamilyRoleCoordinate(role.local_role_ordinal)
}

AnalysisExperimentProcessRef(profile_id,process_ordinal,process_schema) = {
  experiment_profile_id: profile_id,
  local_process_ordinal: process_ordinal,
  exact_process_schema: process_schema
}

AnalysisVerifierProcessRef(S) = {
  protocol_id: S.fiat_shamir_protocol_id,
  check_ref: S.core_check_ref,
  accept_terminal_ref: S.core_accept_terminal_ref,
  exact_process_schema:
    the verifier transition from its proof/Statement inputs through that check
    to that accepting terminal
}

ResolveAFKAbstractRole(F,n0_literal,role) =
  outside every identity preimage, select by role.local_role_ordinal from [
    Statement_F(Value(n0_literal)),Witness_F(Value(n0_literal)),
    Relation_F(Value(n0_literal)),PublicSetup_F(Value(n0_literal)),
    Commitment_F(Value(n0_literal)),ChallengeSet_F(Value(n0_literal)),
    Response_F(Value(n0_literal)),Fresh_F(Value(n0_literal)),
    FiatShamir_F(Value(n0_literal)),Proof_F(Value(n0_literal)),
    Aux_F(Value(n0_literal)),Verifier_F(Value(n0_literal)),
    VerifierOutput_F(Value(n0_literal)),
    RandomOracleIndex_F(Value(n0_literal)),
    statement_length_F(Value(n0_literal)),
    AFKFamilyROQueryDimension(F),
    AFKFamilyAdversaryInvocationDimension(F),
    AFKLogicalNatPositivePolynomialProfileId,
    Evaluate(AFKLogicalNatConstantOnePolynomialId,Value(n0_literal)),
    FamilyConstantChallengeCardinalityValue(F)
  ]

ResolveAFKNativeRole(S,ell0,role) =
  outside every identity preimage, select by role.local_role_ordinal from [
    AnalysisStatementType(S),AnalysisWitnessType(S),S.relation_instance_id,
    AFKFixedPublicSetupId(S),AnalysisCommitmentType(S),
    AnalysisChallengeDomainId(S),AnalysisResponseType(S),
    AnalysisExperimentProcessRef(
      SchnorrSpecialSoundnessExperimentProfileId(S),0,
      exact accepted-pair validation and deterministic extraction process),
    AnalysisExperimentProcessRef(
      AFKMemberKnowledgeExperimentProfileId(S,ell0),0,
      exact Fiat--Shamir adaptive-prover process),
    AFKProofType(S),BitString,
    AnalysisVerifierProcessRef(S),
    TerminalVerdict,AFKRandomOracleIndex(S),ell0,
    AFKAdversaryROQueryResourceDimension(S),
    AFKAdversaryInvocationResourceDimension(S),
    AnalysisConstantOnePolynomialProfileId(S),
    Evaluate(AnalysisConstantOnePolynomialId(S),ell0),
    ModelCardinality(AnalysisChallengeDomainId(S))
  ]

AFKFamilyRoleMapClauseKind =
    TypedCarrierEquivalence
  | PredicateEquivalence
  | ExactValueCorrespondence
  | ExperimentProcessCorrespondence
  | VerifierProcessCorrespondence
  | ResourceMeasureCorrespondence
  | PositivePolynomialProfileSpecialization
  | PositivePolynomialValueCorrespondence

AFKFamilyRoleMapClauseKinds = CanonicalSeq [
  {0,TypedCarrierEquivalence},{1,TypedCarrierEquivalence},
  {2,PredicateEquivalence},{3,ExactValueCorrespondence},
  {4,TypedCarrierEquivalence},{5,TypedCarrierEquivalence},
  {6,TypedCarrierEquivalence},{7,ExperimentProcessCorrespondence},
  {8,ExperimentProcessCorrespondence},{9,TypedCarrierEquivalence},
  {10,TypedCarrierEquivalence},{11,VerifierProcessCorrespondence},
  {12,TypedCarrierEquivalence},{13,TypedCarrierEquivalence},
  {14,ExactValueCorrespondence},{15,ResourceMeasureCorrespondence},
  {16,ResourceMeasureCorrespondence},
  {17,PositivePolynomialProfileSpecialization},
  {18,PositivePolynomialValueCorrespondence},
  {19,ExactValueCorrespondence}
]

AFKAbstractRoleSchemaRef(i) =
  the exact AnalysisAFKTransportLanguageProfileId-local
  AnalysisProfileLawRef<AFKAbstractResolvedRoleSchema> at ordinal i whose
  closed schema admits exactly ResolveAFKAbstractRole(F,n0_literal,role_i)

AFKNativeRoleSchemaRef(i) =
  the exact AnalysisAFKTransportLanguageProfileId-local
  AnalysisProfileLawRef<AFKNativeResolvedRoleSchema> at ordinal i whose closed
  schema admits exactly ResolveAFKNativeRole(S,ell0,role_i)

AFKRoleCorrespondenceLawRef(i) =
  the exact AnalysisAFKTransportLanguageProfileId-local
  AnalysisProfileLawRef<AFKRoleCorrespondenceLaw> at ordinal i, typed from
  AFKAbstractRoleSchemaRef(i) to AFKNativeRoleSchemaRef(i) and implementing
  exactly AFKFamilyRoleMapClauseKinds[i].clause_kind

AFKTransportAttemptFailurePartitionRef =
  CommonAnalysisAttemptFailurePartitionRef<
    AnalysisAFKTransportLanguageProfileId>

ExactNaturalRange(start_inclusive,end_exclusive) =
  require `0 <= start_inclusive <= end_exclusive` and the difference to fit
  the selected Foundation sequence bound; return `[]` when the endpoints are equal and
  otherwise return `[start_inclusive]` concatenated with
  `ExactNaturalRange(start_inclusive + 1,end_exclusive)`

AFKFamilyRoleMapClauseDeclarationBody(i) = {
  local_clause_ordinal: i,
  clause_kind: AFKFamilyRoleMapClauseKinds[i].clause_kind,
  exact_abstract_source_schema: AFKAbstractRoleSchemaRef(i),
  exact_native_target_schema: AFKNativeRoleSchemaRef(i),
  refinement_or_correspondence_law: AFKRoleCorrespondenceLawRef(i),
  information_loss: ExactEquivalence,
  failure_classification: AFKTransportAttemptFailurePartitionRef
}

AFKFamilyRoleMapClauseCatalog =
  CanonicalSeq [AFKFamilyRoleMapClauseDeclarationBody(i)
    for i in ExactNaturalRange(start_inclusive:0,end_exclusive:20)]

AFKFamilyRoleMapClauseCatalogRef =
  the one exact AnalysisProfileDeclarationRef<
    "analysis.afk-family-role-map-clause"> whose
  resolved declaration body is exactly AFKFamilyRoleMapClauseCatalog

AFKFamilyRoleMapClauseCoordinate(role) = {
  catalog_ref: AFKFamilyRoleMapClauseCatalogRef,
  local_clause_ordinal: role.local_role_ordinal,
  exact_clause_kind:
    AFKFamilyRoleMapClauseDeclarationBody(
      role.local_role_ordinal).clause_kind
}

The role catalog, symbolic reference forms, resolution tables, and clause table
above are one admitted closed declaration set. All tables have exactly twenty
entries and admission
checks ordinal continuity, role/type compatibility, and table totality. The
resource entries are exact subroles of the family member's
`resource_measures_F`; the polynomial and cardinality entries are symbolic
specialization coordinates, not additional abstract-member payload fields.
No caller-authored label or partial map is a role coordinate.

Formation of a role-map proposal binds both sides to these resolved content
coordinates. It does not establish that their mathematical denotations agree.
That stronger claim is exactly the separate
`FamilyInstanceRoleMapAdequacyGoal`; it must remain in the pointwise
hypothesis context unless an owner-qualified checker or proof discharges it.
The quantitative normalization contract is narrower: it checks typed
canonical AST equality after the declared substitutions, while any bridge from
that syntax to an external mathematical denotation remains an explicit
correspondence premise.

FamilyInstanceRoleMapProposalBody(F,n0_literal,S,ell0,role) = {
  family_id: F,
  logical_index_id: n0_literal,
  native_subject_refs: AFKNativeSubjectRefs(S),
  native_length_value: ell0,
  role: role : AFKFamilyRoleCoordinate(role.local_role_ordinal),
  abstract_role_ref:
    AFKAbstractFamilyMemberRoleRef(F,n0_literal,role),
  native_role_ref: AFKNativeMemberRoleRef(S,ell0,role),
  map_clause_coordinate: AFKFamilyRoleMapClauseCoordinate(role),
  information_loss: ExactEquivalence
}

FamilyInstanceRoleMapProposalId(F,n0_literal,S,ell0,role) =
  AnalysisId<"analysis.family-instance-role-map">(
    B,FamilyInstanceRoleMapProposalBody(F,n0_literal,S,ell0,role))

RequiredAnalysisLanguageProfile(FamilyInstanceRoleMapProposalBody) =
  AnalysisAFKTransportLanguageProfileId

RequiredAFKFamilyInstanceRoleMaps(F,n0_literal,S,ell0) =
  CanonicalSeq, in AFKFamilyRoleCatalog ordinal order, of exactly one
  FamilyInstanceRoleMapProposalId for every role in AFKFamilyRoleCatalog

AFKPointwiseQuantitativeNormalizationContractBody(
    F,n0_literal,S,ell0) = {
  logical_index_substitution:
    AFKLocalLogicalNatRef -> Value(n0_literal) -> ell0 under the exact length map,
  challenge_cardinality_substitution:
    FamilyConstantChallengeCardinalityValue(F) ->
      ModelCardinality(AnalysisChallengeDomainId(S)),
  positive_polynomial_profile_substitution:
    AFKLogicalNatPositivePolynomialProfileId ->
      AnalysisConstantOnePolynomialProfileId(S),
  positive_polynomial_value_substitution:
    Evaluate(AFKLogicalNatConstantOnePolynomialId,Value(n0_literal)) ->
      Evaluate(AnalysisConstantOnePolynomialId(S),ell0) -> 1,
  resource_substitution: [
    AFKFamilyROQueryDimension(F) -> AFKAdversaryROQueryResourceDimension(S),
    AFKFamilyAdversaryInvocationDimension(F) ->
      AFKAdversaryInvocationResourceDimension(S)
  ],
  canonical_formula_normalization:
    recursively apply the substitutions above, inline acyclic referenced
    quantitative formulas, preserve exact typed count/probability coercions and
    declared domains, then canonicalize under the closed quantitative AST rules,
  required_equal_normal_forms: [
    {family_formula_id: AFKFamilyKnowledgeErrorFormulaId(F),
     member_formula_id: AFKKnowledgeErrorFormulaId(S)},
    {family_formula_id: AFKFamilyKnowledgeSuccessFormulaId(F),
     member_formula_id: AFKKnowledgeSuccessFormulaId(S)},
    {family_formula_id: AFKFamilyTranscriptExtractionFormulaId(F),
     member_formula_id: AFKTranscriptExtractionFormulaId(S)},
    {family_formula_id: AFKFamilyExpectedCallsFormulaId(F),
     member_formula_id: AFKExpectedCallsFormulaId(S)}
  ]
}

AFKPointwiseQuantitativeNormalizationContractId(F,n0_literal,S,ell0) =
  AnalysisId<"analysis.pointwise-quantitative-normalization">(
    B,AFKPointwiseQuantitativeNormalizationContractBody(
      F,n0_literal,S,ell0))

RequiredAnalysisLanguageProfile(
    AFKPointwiseQuantitativeNormalizationContractBody) =
  AnalysisAFKTransportLanguageProfileId

FamilyInstanceCorrespondenceQuestion(
    F,n0_literal:AnalysisLogicalNatLiteralId,
    S:AnalysisSubjectTuple,
    ell0:StatementLength(AnalysisStatementType(S))) = AnalysisQuestionBody {
  family: FamilyInstanceCorrespondence,
  exact_subjects: CanonicalAppend(
    CanonicalAppend([F,n0_literal],AFKTargetSubjectProjection(S)),
    [AnalysisChallengeDomainId(S),AFKFixedPublicSetupId(S)]),
  context: FamilyInstanceContext {
    family_definition_id: F,
    family_read_manifest_schema_ids: [
      AFKFamilyFreshReadManifestSchemaId(F),
      AFKFamilyTargetReadManifestSchemaId(F)
    ],
    concrete_semantic_read_manifest_ids: [
      SchnorrRelationSemanticReadManifestId(S),
      AFKTargetSemanticReadManifestId(S)
    ],
    family_experiment_profile_ids: [
      AFKFamilySpecialSoundnessExperimentProfileId(F),
      AFKFamilyAdaptiveKnowledgeExperimentProfileId(F)
    ],
    concrete_experiment_profile_ids: [
      SchnorrSpecialSoundnessExperimentProfileId(S),
      AFKMemberKnowledgeExperimentProfileId(S,ell0)
    ]
  },
  family_payload: {
    logical_index_id: n0_literal,
    native_statement_length: ell0,
    exact_length_embedding:
      EmbedStatementLength(S,ell0) = Value(n0_literal),
    role_map_proposal_ids:
      RequiredAFKFamilyInstanceRoleMaps(F,n0_literal,S,ell0),
    pointwise_quantitative_normalization_contract_id:
      AFKPointwiseQuantitativeNormalizationContractId(
        F,n0_literal,S,ell0)
  },
  named_premise_requirements: []
}

FamilyInstanceCorrespondenceGoal(F,n0_literal,S,ell0) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(
    B,FamilyInstanceCorrespondenceQuestion(F,n0_literal,S,ell0)),
  named_premise_bindings: {}
}

FamilyInstancePremiseQuestion(
    F,n0_literal,S,ell0,family,payload) =
  FamilyInstanceCorrespondenceQuestion(F,n0_literal,S,ell0) with {
    family: family,
    family_payload: payload
  }

FamilyInstancePremiseGoal(
    F,n0_literal,S,ell0,family,payload) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B,FamilyInstancePremiseQuestion(
    F,n0_literal,S,ell0,family,payload)),
  named_premise_bindings: {}
}

FamilyInstanceDenotationAtIndexGoal(F,n0_literal,S,ell0) =
  FamilyInstancePremiseGoal(
    F,n0_literal,S,ell0,FamilyDenotationAtIndex,{
      exact_proposition:
        `F denotes one abstract member at Value(n0_literal), and ell0 embeds to
         exactly that logical index`
    })

FamilyInstanceProjectionAtIndexGoal(F,n0_literal,S,ell0) =
  FamilyInstancePremiseGoal(
    F,n0_literal,S,ell0,FamilyProjectionAtIndex,{
      exact_proposition:
        `every family source/target role used by this question is the derived
         projection of that one member at Value(n0_literal); no all-index
         coherence proposition is claimed`
    })

FamilyInstanceRoleMapAdequacyGoal(F,n0_literal,S,ell0) =
  FamilyInstancePremiseGoal(
    F,n0_literal,S,ell0,FamilyInstanceRoleMapAdequacy,{
      exact_proposition:
        `every identity-bearing role-map proposal denotes the claimed total
         bijection or predicate equivalence, with no hidden loss`
  })

FamilyInstanceQuantitativeNormalizationGoal(F,n0_literal,S,ell0) =
  FamilyInstancePremiseGoal(
    F,n0_literal,S,ell0,FamilyInstanceQuantitativeNormalizationAdequacy,{
      exact_proposition:
        `the exact pointwise normalization contract is well typed, total on the
         four selected formula pairs, and yields byte-identical canonical normal
         forms after length, fixed-cardinality, resource, polynomial-profile,
         polynomial-value, and acyclic-formula-inlining substitutions`
    })

FamilyInstanceProcessCorrespondenceGoal(F,n0_literal,S,ell0) =
  FamilyInstancePremiseGoal(
    F,n0_literal,S,ell0,FamilyInstanceProcessCorrespondence,{
      exact_proposition:
        `the Fresh, FS, verifier, full adaptive random-oracle, setup, and
         resource processes agree under the admitted role maps`
    })

GammaFamilyInstanceBody(F,n0_literal,S,ell0) =
  AnalysisHypothesisContextBody {
    nodes: [
      {0,AnalysisGoalId(
          B,FamilyInstanceDenotationAtIndexGoal(F,n0_literal,S,ell0)),[],
          premises(goal)},
      {1,AnalysisGoalId(
          B,FamilyInstanceProjectionAtIndexGoal(
            F,n0_literal,S,ell0)),[0], premises(goal)},
      {2,AnalysisGoalId(B,SchnorrChallengeModelGoal(S)),[], premises(goal)},
      {3,AnalysisGoalId(B,SchnorrAcceptanceRelationGoal(S)),[], premises(goal)},
      {4,AnalysisGoalId(B,AFKFamilyFixedChallengeCardinalityGoal(F)),[0,1], premises(goal)},
      {5,AnalysisGoalId(B,AFKFamilyFiniteIndexAndOperationsGoal(F)),[0,1], premises(goal)},
      {6,AnalysisGoalId(
          B,FamilyInstanceRoleMapAdequacyGoal(F,n0_literal,S,ell0)),
          [0,1,2,3,4,5], premises(goal)},
      {7,AnalysisGoalId(
          B,FamilyInstanceQuantitativeNormalizationGoal(
            F,n0_literal,S,ell0)),[0,1,2,4,6], premises(goal)},
      {8,AnalysisGoalId(
          B,FamilyInstanceProcessCorrespondenceGoal(F,n0_literal,S,ell0)),
          [0,1,5,6], premises(goal)}
    ],
    roots: [7,8]
  ,
    exact_named_premise_ids: ContextPremiseIds(nodes, roots)
}

GammaFamilyInstanceId(F,n0_literal,S,ell0) =
  AnalysisHypothesisContextId(
    B,GammaFamilyInstanceBody(F,n0_literal,S,ell0))

FamilyInstanceCorrespondencePropositionBody(F,n0_literal,S,ell0) =
  AnalysisPropositionBody {
    goal_id: AnalysisGoalId(
      B,FamilyInstanceCorrespondenceGoal(F,n0_literal,S,ell0)),
    hypothesis_context_id:
      GammaFamilyInstanceId(F,n0_literal,S,ell0)
  }

FamilyInstanceCorrespondenceSemanticBasisBody(F,n0_literal,S,ell0) =
  AnalysisSemanticBasisBody {
    family: FamilyInstanceCorrespondence,
    exact_question_id: AnalysisQuestionId(
      B,FamilyInstanceCorrespondenceQuestion(F,n0_literal,S,ell0)),
    rule_source: AnalysisNativeRule(
      ConditionalFamilyInstanceCorrespondenceIntroductionRuleRef,{
        family_definition_id: F,
        logical_index_id: n0_literal,
        concrete_subjects: AFKNativeSubjectRefs(S),
        native_statement_length: ell0,
        exact_role_catalog_ref: AFKFamilyRoleCatalogRef
      }),
    exact_premise_schemas:
      AllReachableHypothesisNodeRequirements(
        GammaFamilyInstanceId(F,n0_literal,S,ell0),
        GammaFamilyInstanceBody(F,n0_literal,S,ell0)),
    source_read_purposes: ExactCryptographicReadPurposes(
      [SchnorrRelationSemanticReadManifestId(S),
       AFKTargetSemanticReadManifestId(S)],
      [AFKFamilyFreshReadManifestSchemaId(F),
       AFKFamilyTargetReadManifestSchemaId(F)]),
    conclusion_schema:
      FamilyInstanceCorrespondenceGoal(F,n0_literal,S,ell0),
    typed_transform_program:
      independently check the exact required role-map domain, coordinate
      typing, concrete owner bindings, length embedding, and four quantitative
      AST substitutions; retain role-map adequacy and process correspondence
      as propositions rather than accepting caller Booleans
  }

FamilyInstanceCorrespondenceSemanticBasisId(F,n0_literal,S,ell0) =
  AnalysisSemanticBasisId(B,
    FamilyInstanceCorrespondenceSemanticBasisBody(F,n0_literal,S,ell0))

FamilyInstanceCorrespondenceSupportBody(
    F,n0_literal,S,ell0,established_nodes,assumed_nodes,
    family_fresh_support,family_target_support,
    concrete_fresh_support,concrete_target_support) =
  AnalysisSupportInstantiationBody {
    semantic_basis_id:
      FamilyInstanceCorrespondenceSemanticBasisId(F,n0_literal,S,ell0),
    proposition_id: AnalysisPropositionId(B,
      FamilyInstanceCorrespondencePropositionBody(F,n0_literal,S,ell0)),
    exact_named_premise_ids: PremiseIdsOfProposition(proposition_id),
    non_hypothesis_premise_bindings:
      ExactNonHypothesisPremiseBindingMap(
        FamilyInstanceCorrespondenceSemanticBasisId(
          F,n0_literal,S,ell0),
        FamilyInstanceCorrespondenceSemanticBasisBody(
          F,n0_literal,S,ell0),[]),
    established_hypothesis_node_bindings: established_nodes,
    assumed_hypothesis_node_bindings: assumed_nodes,
    source_support_bindings: [
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyFreshReadManifestSchemaId(F),
        dependent_support_schema: family_fresh_support,
        exact_retained_family_support_hypotheses:
          ReachableHypothesisGoalIds(
            GammaFamilyInstanceId(F,n0_literal,S,ell0),
            GammaFamilyInstanceBody(F,n0_literal,S,ell0))
      },
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyTargetReadManifestSchemaId(F),
        dependent_support_schema: family_target_support,
        exact_retained_family_support_hypotheses:
          ReachableHypothesisGoalIds(
            GammaFamilyInstanceId(F,n0_literal,S,ell0),
            GammaFamilyInstanceBody(F,n0_literal,S,ell0))
      },
      ExactManifestSupportBinding {
        semantic_read_manifest_id:
          SchnorrRelationSemanticReadManifestId(S),
        source_support_coordinate: concrete_fresh_support
      },
      ExactManifestSupportBinding {
        semantic_read_manifest_id: AFKTargetSemanticReadManifestId(S),
        source_support_coordinate: concrete_target_support
      }
    ]
  }

FamilyInstanceCorrespondenceSupportId(
    F,n0_literal,S,ell0,established_nodes,assumed_nodes,
    family_fresh_support,family_target_support,
    concrete_fresh_support,concrete_target_support) =
  AnalysisId<"analysis.support-instantiation">(B,
    FamilyInstanceCorrespondenceSupportBody(
      F,n0_literal,S,ell0,established_nodes,assumed_nodes,
      family_fresh_support,family_target_support,
      concrete_fresh_support,concrete_target_support))

FamilyInstanceCorrespondenceValidationBasisBody(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  ExactAnalysisValidationBasisBody(
    checker_contracts,translations,finite_controls,[],residual_trust_roots)

FamilyInstanceCorrespondenceValidationBasisId(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  AnalysisId<"analysis.validation-basis">(B,
    FamilyInstanceCorrespondenceValidationBasisBody(
      checker_contracts,translations,finite_controls,residual_trust_roots))

FamilyInstanceCorrespondenceOperationPolicyBody(
    F,n0_literal,S,ell0) =
  ExactAnalysisOperationPolicyBody(
    AnalysisPropositionId(B,
      FamilyInstanceCorrespondencePropositionBody(
        F,n0_literal,S,ell0)),
    CanonicalMap {
      AFKMemberSpecializationConsumerRef:
        CanonicalSingleton(AFKExactFamilyMemberSpecializationPurposeRef)
    },
    AFKFamilyInstanceCorrespondencePolicyLawBundleRef)

FamilyInstanceCorrespondenceOperationPolicyId(F,n0_literal,S,ell0) =
  AnalysisId<"analysis.operation-policy">(B,
    FamilyInstanceCorrespondenceOperationPolicyBody(
      F,n0_literal,S,ell0))

FamilyInstanceCorrespondenceJudgmentBody(
    F,n0_literal,S,ell0,support_id,validation_basis_id) =
  ExactAffirmativeAnalysisJudgmentBody(
    AnalysisPropositionId(B,
      FamilyInstanceCorrespondencePropositionBody(
        F,n0_literal,S,ell0)),
    NoQuantitativeResult,
    FamilyInstanceCorrespondenceSemanticBasisId(
      F,n0_literal,S,ell0),
    support_id,validation_basis_id,
    AFKFamilyInstanceCorrespondenceQualificationRef,
    FamilyInstanceCorrespondenceOperationPolicyId(
      F,n0_literal,S,ell0))

FamilyInstanceCorrespondenceJudgmentId(
    F,n0_literal,S,ell0,support_id,validation_basis_id) =
  AnalysisId<"analysis.judgment-record">(B,
    FamilyInstanceCorrespondenceJudgmentBody(
      F,n0_literal,S,ell0,support_id,validation_basis_id))

FamilyInstanceCorrespondenceJudgmentSchema(F,n0_literal,S,ell0) = {
  exact_judgment_constructor: FamilyInstanceCorrespondenceJudgmentId,
  result: conditional affirmative FamilyInstanceCorrespondence inheriting
    exactly GammaFamilyInstanceId(F,n0_literal,S,ell0),
  live_capability_permission:
    AFKMemberSpecializationConsumerRef ->
      AFKExactFamilyMemberSpecializationPurposeRef
}
```

`AFKFamilyInstanceCorrespondencePolicyLawBundleRef` is the one exact
transport-profile operation-policy law bundle for the pointwise result. The
matching live FS-construction-view and Relations correspondence capabilities are
checking-invocation inputs attached to their owner support bindings, not
semantic premise facts; PIR does not forward the consumed checked-construction
capability.

The established and assumed maps are disjoint and partition all nine reachable
nodes; the unique outward root frontier is `[7,8]`. The checker establishes only
canonical completeness, typing,
owner-source agreement, length embedding, and formula substitution. It cannot
mark a role-map or probability-process law true merely because the proposal has
the right shape. A conditional result retains every undischarged adequacy law,
says nothing about another index, and cannot be generalized.

### 8.2 Pointwise specialization

```text
GammaAFKMemberSpecializationBody(F,n0_literal,S,ell0) =
CanonicalGoalDagUnion([
  GammaAFKFamilyTargetBody(F),
  GammaFamilyInstanceBody(F,n0_literal,S,ell0)
])

GammaAFKMemberSpecializationId(F,n0_literal,S,ell0) =
  AnalysisHypothesisContextId(
    B,GammaAFKMemberSpecializationBody(F,n0_literal,S,ell0))

AFKMemberSpecializationPropositionBody(F,n0_literal,S,ell0) =
  AnalysisPropositionBody {
    goal_id: AnalysisGoalId(B,AFKMemberKnowledgeGoal(S,ell0)),
    hypothesis_context_id:
      GammaAFKMemberSpecializationId(F,n0_literal,S,ell0)
  }

AFKMemberSpecializationSemanticBasisBody(F,n0_literal,S,ell0) =
  AnalysisSemanticBasisBody {
    family: AdaptiveKnowledgeExtractionAtFixedLengthQltN,
    exact_question_id:
      AnalysisQuestionId(B,AFKMemberKnowledgeQuestion(S,ell0)),
    rule_source: AnalysisNativeRule(
      DependentFamilyMemberSpecializationRuleRef,{
        family_definition_id: F,
        logical_index_id: n0_literal,
        concrete_subjects: AFKNativeSubjectRefs(S),
        native_statement_length: ell0,
        exact_role_catalog_ref: AFKFamilyRoleCatalogRef
      }),
    exact_premise_schemas: CanonicalAppend(
      AllReachableHypothesisNodeRequirements(
        GammaAFKMemberSpecializationId(F,n0_literal,S,ell0),
        GammaAFKMemberSpecializationBody(F,n0_literal,S,ell0)),
      [
        AffirmativeJudgmentCapabilityRequirement {
          proposition_id: AnalysisPropositionId(
            B,AFKFamilyAdaptiveKnowledgePropositionBody(F)),
          conclusion_family: AdaptiveKnowledgeSoundnessQltN,
          required_qualification: ExactInheritedConditionalQualificationRef,
          named_consumer: AFKMemberSpecializationConsumerRef,
          typed_purpose: AFKFamilyTargetSpecializationPurposeRef
        },
        AffirmativeJudgmentCapabilityRequirement {
          proposition_id: AnalysisPropositionId(B,
            FamilyInstanceCorrespondencePropositionBody(
              F,n0_literal,S,ell0)),
          conclusion_family: FamilyInstanceCorrespondence,
          required_qualification: ExactInheritedConditionalQualificationRef,
          named_consumer: AFKMemberSpecializationConsumerRef,
          typed_purpose: AFKExactFamilyMemberSpecializationPurposeRef
        }
      ]),
    source_read_purposes: ExactCryptographicReadPurposes(
      [AFKTargetSemanticReadManifestId(S)],[]),
    conclusion_schema: AFKMemberKnowledgeGoal(S,ell0),
    typed_transform_program:
      substitute n=Value(n0_literal) and native length=ell0 through the checked
      instance maps and independently
      reconstruct AFKKnowledgeErrorFormulaId(S),
      AFKKnowledgeSuccessFormulaId(S), and
      AFKExpectedCallsFormulaId(S)
  }

AFKMemberSpecializationSemanticBasisId(F,n0_literal,S,ell0) =
  AnalysisSemanticBasisId(
    B,AFKMemberSpecializationSemanticBasisBody(
      F,n0_literal,S,ell0))

InheritedAFKMemberSupportPartition(
    F,n0_literal,S,ell0,
    family_property_capability,instance_capability) =
  authenticate both exact premise capabilities and their support records;
  project every node treatment from GammaAFKFamilyTargetBody(F) and
  GammaFamilyInstanceBody(F,n0_literal,S,ell0); merge equal goals through
  GammaAFKMemberSpecializationBody(F,n0_literal,S,ell0); prefer an exact
  established node capability over an Assumed occurrence and otherwise retain
  Assumed; reject a missing node, unrelated capability, or output domain other
  than the complete specialization-context node set; return
  ExactHypothesisTreatmentPartition(
    GammaAFKMemberSpecializationId(F,n0_literal,S,ell0),
    GammaAFKMemberSpecializationBody(F,n0_literal,S,ell0),
    the derived complete treatment map)

AFKMemberSpecializationSupportBody(
    F,n0_literal,S,ell0,
    family_property_capability,instance_capability,
    member_target_support) =
AnalysisSupportInstantiationBody {
  semantic_basis_id:
    AFKMemberSpecializationSemanticBasisId(F,n0_literal,S,ell0),
  proposition_id: AnalysisPropositionId(
    B,AFKMemberSpecializationPropositionBody(
      F,n0_literal,S,ell0)),
  exact_named_premise_ids: PremiseIdsOfProposition(proposition_id),
  non_hypothesis_premise_bindings:
    ExactNonHypothesisPremiseBindingMap(
      AFKMemberSpecializationSemanticBasisId(F,n0_literal,S,ell0),
      AFKMemberSpecializationSemanticBasisBody(F,n0_literal,S,ell0),
      [family_property_capability,instance_capability]),
  established_hypothesis_node_bindings:
    EstablishedPartitionOf(InheritedAFKMemberSupportPartition(
      F,n0_literal,S,ell0,
      family_property_capability,instance_capability)),
  assumed_hypothesis_node_bindings:
    AssumedPartitionOf(InheritedAFKMemberSupportPartition(
      F,n0_literal,S,ell0,
      family_property_capability,instance_capability)),
  source_support_bindings: [ExactManifestSupportBinding {
    semantic_read_manifest_id: AFKTargetSemanticReadManifestId(S),
    source_support_coordinate: member_target_support
  }]
}

AFKMemberSpecializationSupportId(
    F,n0_literal,S,ell0,
    family_property_capability,instance_capability,member_target_support) =
  AnalysisId<"analysis.support-instantiation">(B,
    AFKMemberSpecializationSupportBody(
      F,n0_literal,S,ell0,
      family_property_capability,instance_capability,member_target_support))

AFKMemberSpecializationValidationBasisBody(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  ExactAnalysisValidationBasisBody(
    checker_contracts,translations,finite_controls,[],residual_trust_roots)

AFKMemberSpecializationValidationBasisId(
    checker_contracts,translations,finite_controls,residual_trust_roots) =
  AnalysisId<"analysis.validation-basis">(B,
    AFKMemberSpecializationValidationBasisBody(
      checker_contracts,translations,finite_controls,residual_trust_roots))

AFKMemberSpecializationOperationPolicyBody(F,n0_literal,S,ell0) =
  ExactAnalysisOperationPolicyBody(
    AnalysisPropositionId(B,
      AFKMemberSpecializationPropositionBody(F,n0_literal,S,ell0)),
    CanonicalMap {},
    AFKMemberSpecializationPolicyLawBundleRef)

AFKMemberSpecializationOperationPolicyId(F,n0_literal,S,ell0) =
  AnalysisId<"analysis.operation-policy">(B,
    AFKMemberSpecializationOperationPolicyBody(F,n0_literal,S,ell0))

AFKMemberSpecializationJudgmentBody(
    F,n0_literal,S,ell0,support_id,validation_basis_id) =
  ExactAffirmativeAnalysisJudgmentBody(
    AnalysisPropositionId(B,
      AFKMemberSpecializationPropositionBody(F,n0_literal,S,ell0)),
    [AFKKnowledgeErrorFormulaId(S),AFKKnowledgeSuccessFormulaId(S),
     AFKExpectedCallsFormulaId(S)],
    AFKMemberSpecializationSemanticBasisId(F,n0_literal,S,ell0),
    support_id,validation_basis_id,
    AFKMemberSpecializationQualificationRef,
    AFKMemberSpecializationOperationPolicyId(F,n0_literal,S,ell0))

AFKMemberSpecializationJudgmentId(
    F,n0_literal,S,ell0,support_id,validation_basis_id) =
  AnalysisId<"analysis.judgment-record">(B,
    AFKMemberSpecializationJudgmentBody(
      F,n0_literal,S,ell0,support_id,validation_basis_id))

AFKMemberSpecializationJudgmentSchema(F,n0_literal,S,ell0) = {
  exact_judgment_constructor: AFKMemberSpecializationJudgmentId,
  result: conditional affirmative fixed-length member judgment inheriting
    exactly GammaAFKMemberSpecializationId(F,n0_literal,S,ell0),
  live_capability_permissions: none in the selected Analysis profile
}
```

`AFKMemberSpecializationPolicyLawBundleRef` is the one exact source-validation-
profile operation-policy law bundle for this terminal result. Its empty
consumer map forbids issuing a downstream premise capability; it does not erase
the judgment, support, validation, persistence, disclosure, or replay policy.

The finite reference instrument may form these bodies, exercise exact
arithmetic at one `(n0_literal,ell0)`, and reject a changed role, query domain, formula,
hypothesis partition, or capability. It cannot establish the family property,
the correspondence's universal process premise, theorem truth, ROM security,
or any asymptotic statement.

## 9. Explicit unsupported profiles

Analysis returns `Unsupported` for QROM, malicious-verifier zero knowledge,
multi-prover independence, generic state restoration, IOP/IOR-to-concrete-Core
transforms, concrete hash security, and generic property composition. It does
not infer ordinary soundness, zero knowledge, EUF-CMA, round-by-round
soundness, or whole-protocol security from the two selected profiles.

The exact classical FRI research instrument does not widen this active
catalog. It separately forms candidate round-by-round and restricted-
restoration questions, authenticates a three-fold scalar-terminal structural
shape, and classifies one exact theorem-parameter substitution as non-vacuous.
Its theorem-truth and applicability coordinates remain unresolved and its
property status remains unevaluated. Durable activation requires exact family,
experiment, adversary, source-manifest, question, proposition, support, and
authority bodies under an explicit Analysis profile revision.

<!-- zkc-profile-source:analysis-transport-application-semantics:end -->
