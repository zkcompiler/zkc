# Cryptographic property profiles

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-C target
> **Target status:** One relation-bound Fresh premise and one classical-ROM
> Fresh-to-Fiat--Shamir transport profile
> **Provisional owner:** `analysis`
> **Authority:** This page defines a redesign target only. The current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> Admitting these schemas or passing a finite gate establishes no theorem truth,
> cryptographic security, concrete-hash security, or implementation support.

## 1. Selection and research basis

K3-C selects one exact theorem edge, not a generic rule that Fiat--Shamir
preserves every property:

```text
2-out-of-N special soundness of one exact three-move public-coin Fresh profile
  -> adaptive knowledge soundness of its exact Fiat--Shamir profile
     in the classical random-oracle model
```

The concrete theorem schema is pinned to the February 16, 2022 ePrint version 2
of Attema, Fehr, and Klooß and uses Definition 4, Definition 10, Definition 11,
Lemma 4, the adaptive construction in Section 6.3 immediately preceding
Theorem 4, Remark 2 for deterministic next-message access and rewinding,
Remark 6 for consistent oracle answers across reruns, and Theorem 4,
[*Fiat--Shamir Transformation of Multi-Round Interactive Proofs (Extended
Version)*](https://eprint.iacr.org/2021/1377.pdf). The corresponding published
article is [Journal of Cryptology 36, article 36
(2023)](https://link.springer.com/article/10.1007/s00145-023-09478-y). A theorem
schema for the journal revision must be formed separately with its own exact
locators and statement digest; citations across the two revisions cannot be
mixed inside one schema. The common
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

## 3. Relation-bound Fresh special soundness

All active nominal constructors below are parameterized by one exact subject
tuple; a bare display label is never an ID:

```text
K3CSubjectTuple S = {
  fresh_protocol_id,
  fiat_shamir_protocol_id,
  shared_core_id,
  transcript_construction_id,
  fs_construction_result_schema,
  relation_definition_id,
  relation_semantic_model_id,
  relation_interface_id,
  relation_instance_id,
  protocol_relation_binding_id,
  plan_witness_binding_id,
  statement_correspondence_question_id_and_StatementEdgeRef,
  claim_correspondence_question_id_and_ClaimMeaningRef,
  witness_correspondence_question_id_and_PlanWitnessEdgeRef,
  k2_check_ref,
  k2_accept_terminal_ref,
  grounding_equation_id,
  equation_grounding_question_id,
  challenge_ref,
  challenge_value_type,
  challenge_domain_ref,
  challenge_fresh_law_ref,
  analysis_challenge_values:
    CanonicalNonEmptySortedUniqueSeq<CanonicalValue<challenge_value_type>>,
  fixed_setup_sources: {
    exact relation/group-parameter source coordinate,
    exact K2 PublicParameter and selected fixed SessionContext BindingRefs plus
      typed invocation assignments, excluding the prover-output Statement,
    exact transcript-construction application_domain nominal ref
  }
}

K3CStatementType(S) =
  the one ValueType whose equality is checked across the selected K2 Statement
  BindingRef, exact StatementEdgeRef target, and selected relation public slot

K3CWitnessType(S) =
  the one ValueType whose equality is checked across the selected Plan Witness
  surface, exact PlanWitnessEdgeRef target, and selected relation Witness slot

K3CCommitmentType(S) =
  the one ValueType of the unique prover Message occurrence preceding the
  selected Fresh challenge and occupying the corresponding first field of the
  selected Fiat--Shamir proof projection

K3CResponseType(S) =
  the one ValueType of the unique prover Message occurrence following the
  selected Fresh challenge and occupying the corresponding response field of
  the selected Fiat--Shamir proof projection

AFKProofType(S) = CanonicalRecord<
  the exact ordered prover-controlled FS proof-occurrence projections consumed
  by the selected FS verifier, excluding the Statement and auxiliary output,
  with each field carrying its owner K2 ValueType and occurrence coordinate>

K3CChallengeDomainBody(S) = {
  source_challenge_ref: S.challenge_ref,
  value_type: S.challenge_value_type,
  source_nominal_domain_ref: S.challenge_domain_ref,
  model_values: S.analysis_challenge_values,
  adequacy_law: every member has one canonical value representation and the
    ModelCardinality derivation is the length of this exact canonical nonempty
    sorted-unique sequence, is total under the K1 finite-term bound, and is
    cardinality >= 2 for this K3-C family,
  semantic_status:
    Analysis-owned finite model requiring an ordinary correspondence premise
    to the owner-qualified nominal domain ref and K2 value type
}

K3CChallengeDomainId(S) =
  AnalysisId<"analysis.challenge-domain">(B, K3CChallengeDomainBody(S))

AFKFixedPublicSetupBody(S) = {
  exact_sources: [S.shared_core_id, S.transcript_construction_id,
                  S.challenge_ref, S.fixed_setup_sources],
  derived_projection:
    deterministically derive the exact CoreHeader, ConstructionHeader,
    ApplicationDomainHeader, scope/opening frames, public-parameter frames,
    challenge-condition framing schema, prefix-construction function, and
    ChallengeNamespace schema from those owner sources under the K2
    construction law; the concrete DerivedPrefix additionally takes the later
    prover outputs Y and A and is not fixed setup,
  required_selection_schedule:
    fixed before and independent of P^a and both random-oracle spaces,
  visibility_map:
    coordinate-by-coordinate public visibility through the exact
    PublicBindingView and transcript-construction views
}

AFKFixedPublicSetupId(S) =
  AnalysisId<"analysis.fixed-public-setup">(B, AFKFixedPublicSetupBody(S))
```

Every top-level field other than `analysis_challenge_values` and the grouping
record `fixed_setup_sources` is a typed owner semantic coordinate or an exact
owner-declared field projection. The
finite challenge-value sequence is an Analysis-owned model coordinate bound by
`K3CChallengeDomainId(S)`; formation proves only its canonical finite shape.
An ordinary hypothesis must relate the K2 nominal domain ref and value type to
that model. The separate AFK applicability hypotheses relate the nominal
fresh-law ref and correlation fields to the required uniform process. The fixed-setup
body and ID are an Analysis-owned exact projection of their listed owner source
coordinates and values, not copied derived headers, a new owner fact, or an
owner-issued view. Ordinary
applicability hypotheses establish its visibility, fixedness, and independence.
Formation requires the two Protocols to name
`shared_core_id`, every relation/binding/ref coordinate to agree, and the exact
transcript-construction/result schema to name those Fresh/FS subjects. The
selected terminal must have verdict `Accept`, must list `k2_check_ref` in
`required_true_checks`, and both refs must have their unique K2 occurrence
backlinks. The selected correspondence question must be exactly the
`EquationGrounding` variant over `grounding_equation_id`.
`K3CChallengeDomainBody(S)` formation additionally rejects cardinality below
`2`; an empty pair domain cannot inhabit `KOutOfNSpecialSoundness(k = 2)`.
The
concrete `CheckedFSConstruction` result binding and fresh capability belong to
support and invocation; no `CheckedFSConstructionId` exists. Replacing,
omitting, or reordering a field changes or malforms every dependent manifest,
question, or derived setup/domain ID. In the remaining displays, a bare
`...Id` whose body depends on subjects means `...Id(S)` under an explicitly
bound `S`; use outside that scope is malformed.

Owner-qualified view coordinates are derived, never supplied:

```text
K3COwnerViewCoordinate(S, PublicBindingView) =
  OwnerViewCoordinate(PIR,S.shared_core_id,PublicBindingView)
K3COwnerViewCoordinate(S, StrategyDecisionView | PublicCoinView | EffectView |
                           ClaimReductionView | ExecutionView) =
  OwnerViewCoordinate(PIR,S.shared_core_id,the selected view kind)
K3COwnerViewCoordinate(S, TranscriptDeclarationView | RequiredInfluenceView |
                           ChallengeTransitionView) =
  OwnerViewCoordinate(
    PIR,S.transcript_construction_id,the selected construction-view kind)
K3COwnerViewCoordinate(S, FSConstructionView) =
  OwnerResultViewCoordinate(
    PIR,S.fs_construction_result_schema,
    [S.fresh_protocol_id,S.fiat_shamir_protocol_id,S.shared_core_id,
     S.transcript_construction_id])

SchnorrRelationSubjectProjection(S) = CanonicalSeq [
  S.fresh_protocol_id,
  S.shared_core_id,
  S.relation_definition_id,
  S.relation_semantic_model_id,
  S.relation_interface_id,
  S.relation_instance_id,
  S.protocol_relation_binding_id,
  S.plan_witness_binding_id,
  QuestionIdOf(S.statement_correspondence_question_id_and_StatementEdgeRef),
  QuestionIdOf(S.claim_correspondence_question_id_and_ClaimMeaningRef),
  QuestionIdOf(S.witness_correspondence_question_id_and_PlanWitnessEdgeRef),
  S.grounding_equation_id,
  S.equation_grounding_question_id
]

AFKTargetSubjectProjection(S) = CanonicalSeq [
  every entry of SchnorrRelationSubjectProjection(S) in the same order,
  S.fiat_shamir_protocol_id,
  S.transcript_construction_id
]
```

The two projections above are exact typed-semantic-subject constructors, not
prose set comprehensions. Their displayed field order is their identity order;
`QuestionIdOf` accepts only the declared pair carrier and returns its exact
owner question ID. Check/terminal/challenge refs and result-schema coordinates
remain selected fields of the identified Core or construction sources and are
not smuggled into `exact_subjects` as non-ID values. A missing field, a
different order, or an additional subject is malformed.

The active slot catalogs use these exact ordered field projections:

```text
K3CFamilyRoleKindRef(name,signature_class) =
  the one exact ModuleDeclarationRef<"analysis.family-role-kind"> whose
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

K3CPIRSourceSlot(view_kind,coordinate_schema,field_paths,purpose,adequacy) =
  ConcreteOwnerReadSlotSchema(
    PIR,view_kind,
    DependentForAll([subject : K3CSubjectTuple],coordinate_schema),purpose,
    ExactOwnerFieldProjection(
      ResolvedOwnerSourceBodySchema(PIR,view_kind),field_paths),
    adequacy,ResolvedOwnerSourceBindingSchema(PIR,view_kind),None,
    common K3-C source-ingress failure partition)

K3CPIRFreshSourceSlotFragment = CanonicalSeq [
  K3CPIRSourceSlot(PublicBindingView,
    K3COwnerViewCoordinate(subject,PublicBindingView),
    [scope_openings,binding_ref.class,binding_ref.value_type,
     binding_ref.value_origin,public_parameter_assignments,
     fixed_session_context_assignments],SemanticMeaning,
    exact Statement binding and public-role typing),
  K3CPIRSourceSlot(StrategyDecisionView,
    K3COwnerViewCoordinate(subject,StrategyDecisionView),
    [decision_points,prover_view_formation,legal_move_types],SemanticMeaning,
    exact prover-controlled move surface),
  K3CPIRSourceSlot(PublicCoinView,
    K3COwnerViewCoordinate(subject,PublicCoinView),
    [challenge_ref.value_type,challenge_ref.domain,
     challenge_ref.reduction_use,challenge_ref.public_conditions,
     structural_public_coin_eligibility],SemanticMeaning,
    exact selected Fresh challenge and public-coin structure),
  K3CPIRSourceSlot(EffectView,
    K3COwnerViewCoordinate(subject,EffectView),
    [check_ref.algorithm,check_ref.evaluation_contract,check_ref.inputs,
     check_ref.unique_invoke_occurrence,terminal_ref.verdict,
     terminal_ref.required_true_checks,terminal_ref.claim_dispositions,
     terminal_ref.unique_occurrence],SemanticMeaning,
    exact selected verifier check and accepting terminal),
  K3CPIRSourceSlot(ClaimReductionView,
    K3COwnerViewCoordinate(subject,ClaimReductionView),
    [claim.contract,claim.usage,claim.source,terminal.claim_disposition],
    SemanticMeaning,exact selected knowledge-claim meaning),
  K3CPIRSourceSlot(ExecutionView,
    K3COwnerViewCoordinate(subject,ExecutionView),
    [generated_execution_law,run_record_schema,replay_qualification_law],
    OccurrenceEvidence,exact execution/replay evidence boundary)
]

SchnorrSourceSlotCatalog = CanonicalConcat(
  K3CPIRFreshSourceSlotFragment,
  K3BRelationSourceSlotFragment)

AFKAdditionalSourceSlotCatalog = CanonicalSeq [
  K3CPIRSourceSlot(TranscriptDeclarationView,
    K3COwnerViewCoordinate(subject,TranscriptDeclarationView),
    [construction_frames,event_declarations,challenge_namespace,
     application_domain_nominal_ref],
    SemanticMeaning,exact selected construction declaration),
  K3CPIRSourceSlot(RequiredInfluenceView,
    K3COwnerViewCoordinate(subject,RequiredInfluenceView),
    [challenge_indexed_required_influence_sets],PremiseSupport,
    exact selected challenge influence law),
  K3CPIRSourceSlot(ChallengeTransitionView,
    K3COwnerViewCoordinate(subject,ChallengeTransitionView),
    [prefix_transition,sampler,challenge_decoding_coordinates],
    SemanticMeaning,exact selected FS challenge transition),
  K3CPIRSourceSlot(PublicCoinView,
    K3COwnerViewCoordinate(subject,PublicCoinView),
    [challenge_ref.fresh_law,challenge_ref.correlation],PremiseSupport,
    exact selected Fresh distribution declaration),
  K3CPIRSourceSlot(FSConstructionView,
    K3COwnerViewCoordinate(subject,FSConstructionView),
    [result_schema,fresh_protocol_id,fiat_shamir_protocol_id,shared_core_id,
     transcript_construction_id,exact_maps,structural_conclusion],
    PremiseSupport,exact selected Fresh/FS construction result schema)
]
```

The closed source/profile bodies are:

```text
SchnorrRelationSourceProfileBody = {
  family_tag: SchnorrRelationSpecialSoundnessSource,
  slot_schemas: SchnorrSourceSlotCatalog,
  closed_field_read_set: exact derived union of those owner schema fields,
  adequacy_predicate: one shared Fresh Protocol/Core, one exact relation seam,
    and complete Statement/claim/Witness/check/terminal agreement
}

SchnorrRelationSemanticReadManifestBody(S) = {
  source_profile_id: SchnorrRelationSourceProfileId,
  exact_subjects: SchnorrRelationSubjectProjection(S),
  slots: exact canonical instantiation of every declared slot schema from S
}

AFKFreshFsSourceProfileBody = {
  family_tag: AFKAdaptiveFreshFsSource,
  slot_schemas:
    CanonicalAppend(SchnorrSourceSlotCatalog,AFKAdditionalSourceSlotCatalog),
  closed_field_read_set: exact derived union of those owner schema fields,
  adequacy_predicate: Schnorr source adequacy plus exact same-Core Fresh/FS
    construction and complete fixed-setup/query-index agreement
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
manifest imports only `K3BRelationSourceSlotFragment` from
[the relation-source boundary](semantic-relations.md#3-exact-relation-source-projection).
Its source manifest binds:

```text
one admitted Fresh Protocol and K2 source views
one admitted relation definition, Interface, and instance
checked Statement, claim, and Witness-role edges
commitment, challenge, response, verifier check, and accepting event
the exact challenge set C with cardinality N >= k = 2
```

The experiment and `Gamma_special(S)`, rather than the source manifest, bind the
quantified extractor profile, group laws, efficiency premises, and other
algebraic side conditions. A source manifest contains only owner-issued
semantic reads; it cannot acquire Analysis-owned quantifiers or hypotheses.

`PublicCoinView` establishes structural eligibility and the location of public
coin sinks; it does not establish a probability law. The deterministic source
property does not read one. The separate AFK applicability manifest retains the
truth and exact K2-to-experiment correspondence of the Fresh uniform independent
challenge distribution as explicit premises unless exact accepted authority
discharges them.

The quantified source carrier is a finite K1 value type owned on this page:

```text
SchnorrSpecialSoundnessTranscriptType(S) = RootRecord<[
  (0,K3CStatementType(S)),
  (1,K3CCommitmentType(S)),
  (2,S.challenge_value_type),
  (3,K3CResponseType(S))
]>

SchnorrSpecialSoundnessPair(S) = RootRecord<[
  (0,SchnorrSpecialSoundnessTranscriptType(S)),
  (1,SchnorrSpecialSoundnessTranscriptType(S))
]>

admitted_pair_predicate(S,pair) iff
  pair is one CanonicalValue<SchnorrSpecialSoundnessPair(S)>,
  both transcript Statements are equal and both commitments are equal,
  both challenges inhabit ModelValues(K3CChallengeDomainId(S)),
  the two canonical challenge values are unequal, and
  both transcript tuples satisfy the exact accepting predicate reconstructed
    from S.k2_check_ref, S.k2_accept_terminal_ref, S.grounding_equation_id, and
    the selected relation/verifier correspondence schemas
```

`RootRecord` is the exact K1 root record type constructor, so neither the type
nor a value carries a `RunRecord`, live replay capability, owner handle, or
future Analysis ID. The complete subject tuple fixes the Protocol, relation,
check, terminal, and challenge model outside the value. A `CheckedReplayMatch`
may validate how one concrete tuple was obtained, but it is occurrence support
only and is neither pair membership nor universal property authority. Changing
any type, field ordinal, subject, or reconstructed acceptance predicate changes
the pair schema or its question; no undefined dependent-record constructor is
used.

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
SchnorrDeterministicExtractorProfileBody(S: K3CSubjectTuple) = {
  input_types: [SchnorrSpecialSoundnessPair(S)],
  output_types: [K3CWitnessType(S)],
  private_state_and_randomness_types: [Unit, Unit],
  allowed_source_oracle_capabilities: [],
  rerun_fork_rewind_programming_rights: none,
  state_preservation_relation: deterministic stateless evaluation,
  output_distribution_preservation_relation: deterministic singleton law,
  witness_success_relation:
    output x satisfies the exact relation selected by the pair subjects,
  termination_and_asymptotic_resource_law:
    polynomial-time field/group algorithm under separately supplied exact
    primitive and resource premise schemas,
  counterfactual_capability_contract: none,
  property_family_scope: FixedExtractorUniversalCorrectness and
    KOutOfNSpecialSoundness(k = 2)
}

SchnorrDeterministicExtractorProfileId(S: K3CSubjectTuple) =
  AnalysisExtractorProfileId(
    B, SchnorrDeterministicExtractorProfileBody(S))

SchnorrSpecialSoundnessExperimentProfile(S: K3CSubjectTuple) = {
  family: KOutOfNSpecialSoundness,
  source_profile_id: SchnorrRelationSourceProfileId,
  quantifier_prefix: [
    ExistsExtractor(
      SchnorrDeterministicExtractorProfileId(S), Ext),
    ForAllValue(
      SchnorrSpecialSoundnessPair(S), admitted_pair_predicate(S), pair)
  ],
  role_interfaces: [Ext: deterministic_extractor_abi],
  setup_and_input_sampling: none,
  randomness_ownership_and_independence: none,
  public_coin_or_oracle_model:
    exact Fresh public-coin structural profile and challenge set,
  scheduler: deterministic pair validation then extraction,
  generated_execution_relation:
    exact accepted typed pair membership reconstructed from the selected static
    K2 and Relations semantics,
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

SchnorrSpecialSoundnessQuestion(S: K3CSubjectTuple) = AnalysisQuestionBody {
  family: KOutOfNSpecialSoundness,
  exact_subjects: CanonicalUnion(
    SchnorrRelationSubjectProjection(S), [K3CChallengeDomainId(S)]),
  context: SemanticExperimentContext {
    semantic_read_manifest_ids: [SchnorrRelationSemanticReadManifestId(S)],
    experiment_profile_ids: [SchnorrSpecialSoundnessExperimentProfileId(S)]
  },
  family_payload: {
    k = 2, K3CChallengeDomainId(S) and its exact cardinality N,
    exact accepted typed pair-domain schema,
    exact deterministic extractor ABI,
    exact relation-witness conclusion schema
  }
}

SchnorrSpecialSoundnessGoal(S: K3CSubjectTuple) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B, SchnorrSpecialSoundnessQuestion(S)),
  conclusion_family: KOutOfNSpecialSoundness,
  hypothesis_free_conclusion:
    there exists one admitted polynomial-time Ext such that, for every
    admitted pair, Ext returns an exact Witness satisfying the relation
}

SchnorrFixedExtractorUniversalExperimentProfile(S: K3CSubjectTuple) = {
  family: FixedExtractorUniversalCorrectness,
  source_profile_id: SchnorrRelationSourceProfileId,
  quantifier_prefix: [
    ForAllValue(
      SchnorrSpecialSoundnessPair(S), admitted_pair_predicate(S), pair)
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
    exact accepted typed pair membership reconstructed from the selected static
    K2 and Relations semantics,
  observation_and_win_event:
    the candidate extractor output satisfies the bound relation for every
    member,
  failure_abort_and_noncompletion_law:
    malformed, refused, and nonmember inputs are outside the implication;
    candidate failure on a member is an exact counterexample,
  termination_law: candidate extractor polynomial-time premise,
  resource_basis: exact candidate extractor steps,
  output_type: deterministic fixed-extractor universal judgment
}

SchnorrFixedExtractorWorksQuestion(
  S: K3CSubjectTuple, Ext: PortableAlgorithmRef) =
AnalysisQuestionBody {
  family: FixedExtractorUniversalCorrectness,
  exact_subjects:
    CanonicalAppend(
      CanonicalUnion(SchnorrRelationSubjectProjection(S),
                     [K3CChallengeDomainId(S)]), [Ext]),
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
  }
}

SchnorrFixedExtractorWorksGoal(
  S: K3CSubjectTuple, Ext: PortableAlgorithmRef) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(
    B, SchnorrFixedExtractorWorksQuestion(S, Ext)),
  conclusion_family: FixedExtractorUniversalCorrectness,
  hypothesis_free_conclusion:
    for every admitted pair, this exact Ext returns an exact Witness
    satisfying the relation
}
```

The fixed-extractor subquestion names `Ext` as an exact subject and reuses the
same pair domain and experiment body with the existential removed. A member on
which `Ext` fails is a counterexample to that subquestion. An affirmative
fixed-extractor universal judgment, together with admission of the exact
polynomial-time extractor profile, introduces the witness for the existential
`SchnorrSpecialSoundnessGoal(S)`. Failure of a proposed extractor therefore
produces support for rejecting that proposal, not `Negative` for special
soundness. The existential family may emit `Negative` only if a separately
admitted procedure completely refutes every extractor in its exact quantified
domain; K3-C selects no such procedure.

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
    exact_subjects: CanonicalUnion(
      SchnorrRelationSubjectProjection(S),
      [K3CChallengeDomainId(S)] + extra_subjects),
    context: SemanticExperimentContext {
      semantic_read_manifest_ids:
        [SchnorrRelationSemanticReadManifestId(S)],
      experiment_profile_ids:
        [SchnorrSpecialSoundnessExperimentProfileId(S)]
    },
    family_payload: payload
  }

SchnorrSourcePremiseGoal(S, family, payload, extra_subjects) =
  AnalysisGoalBody {
    question_id: AnalysisQuestionId(
      B, SchnorrSourcePremiseQuestion(S,family,payload,extra_subjects)),
    conclusion_family: family,
    hypothesis_free_conclusion: payload.exact_proposition
  }

SchnorrChallengeModelGoal(S) = SchnorrSourcePremiseGoal(
  S, ChallengeDomainCorrespondence, {
    owner_coordinate: S.challenge_ref and its exact ChallengeDecl projection,
    analysis_model: K3CChallengeDomainId(S),
    exact_proposition:
      the nominal domain ref denotes exactly the model value sequence at the
      declared value type; its cardinality is the model cardinality
  }, [])

SchnorrAcceptanceRelationGoal(S) = SchnorrSourcePremiseGoal(
  S, AcceptanceRelationCorrespondence, {
    K2_source: S.k2_check_ref, its unique InvokeCheck occurrence, exact
      CheckDecl fields, S.k2_accept_terminal_ref, and exact TerminalDecl fields,
    Relations_source: S.relation_instance_id, S.grounding_equation_id, and
      S.equation_grounding_question_id whose variant is exactly
      EquationGrounding(S.grounding_equation_id,...),
    exact_proposition:
      for every structurally complete admitted transcript projection, reaching
      the selected Accept terminal iff the selected K2 check returns true iff
      the exact grounding/relation verifier predicate holds
  }, [])

SchnorrAlgebraEncodingGoal(S) = SchnorrSourcePremiseGoal(
  S, AlgebraAndCanonicalEncodingLaws, {
    exact relation/group/encoding coordinates wholly contained in
      S.relation_definition_id, S.relation_semantic_model_id, and
      K3CChallengeDomainId(S),
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
    exact K2 CheckDecl algorithm/evaluation contract and terminal path,
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
    {0, AnalysisGoalId(B,SchnorrChallengeModelGoal(S)), []},
    {1, AnalysisGoalId(B,SchnorrAcceptanceRelationGoal(S)), []},
    {2, AnalysisGoalId(B,SchnorrAlgebraEncodingGoal(S)), []},
    {3, AnalysisGoalId(B,SchnorrRelationMembershipEfficiencyGoal(S)), []},
    {4, AnalysisGoalId(B,SchnorrVerifierEfficiencyGoal(S)), []},
    {5, AnalysisGoalId(B,SchnorrExtractorEfficiencyGoal(S,Ext)), []},
    {6, AnalysisGoalId(B,SchnorrFixedExtractorWorksGoal(S,Ext)), []}
  ],
  roots: [0,1,2,3,4,5,6]
}

GammaSpecialId(S,Ext) =
  AnalysisHypothesisContextId(B, GammaSpecialBody(S,Ext))

SchnorrSpecialSoundnessProposition(S,Ext) = AnalysisPropositionBody {
  goal_id: AnalysisGoalId(B, SchnorrSpecialSoundnessGoal(S)),
  hypothesis_context_id: GammaSpecialId(S,Ext)
}
```

The algebra/encoding premise reads no `fixed_setup_sources` field. Its group
and encoding meaning is owned by the relation definition/model already present
in `SchnorrSourceSlotCatalog`; the Analysis challenge model supplies only its
finite challenge-value correspondence. AFK fixed-setup sources enter only the
target manifest and applicability path.

The deterministic conclusion does not use a challenge probability law. Fresh
uniformity, independence, and their K2-to-experiment correspondence are
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

AnalysisNativeRuleSemanticsCatalog(B) contains exactly these active K3-C
entries:
  ExistentialExtractorIntroductionRuleRef ->
    AnalysisNativeRuleSemanticsContract {
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
      failure_classification: common K3-C outcome partition
    },
  ExactTheoremApplicabilityCheckRuleRef ->
    AnalysisNativeRuleSemanticsContract {
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
      failure_classification: common K3-C outcome partition
    },
  ConditionalFamilyInstanceCorrespondenceIntroductionRuleRef ->
    AnalysisNativeRuleSemanticsContract {
      exact_payload_meta_schema: ExactAFKFamilyMemberRulePayload,
      allowed_conclusion_families: [FamilyInstanceCorrespondence],
      exact_premise_requirement_schema:
        AllReachableHypothesisNodeRequirements of the exact pointwise context,
      exact_typed_transform_program_schema:
        complete role-table and quantitative-substitution checking,
      conclusion_reconstruction_law:
        reconstruct only the exact pointwise correspondence goal,
      failure_classification: common K3-C outcome partition
    },
  DependentFamilyMemberSpecializationRuleRef ->
    AnalysisNativeRuleSemanticsContract {
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
      failure_classification: common K3-C outcome partition
    }.

ExactAFKFamilyMemberRulePayload = {
  family_definition_id: AnalysisAsymptoticProtocolFamilyDefinitionId,
  logical_index_id: AnalysisLogicalNatLiteralId,
  concrete_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  native_statement_length: StatementLength(exact statement-type coordinate),
  exact_role_catalog_ref:
    ModuleDeclarationRef<"analysis.afk-family-role-catalog">
}

K3CUseDeclarationBody(kind,tag) = MetaRecord {
  0: MetaSymbol(kind), 1: MetaSymbol(tag), 2: MetaNatural(0)
}

The nine use coordinates above resolve exactly these pairwise-distinct bodies:

```text
ExactInheritedConditionalQualificationRef ->
  K3CUseDeclarationBody("qualification","exact-inherited-conditional")
FiniteSpecialSoundnessConsumerRef ->
  K3CUseDeclarationBody("consumer","finite-special-soundness")
AFKFamilyPropertyTransportConsumerRef ->
  K3CUseDeclarationBody("consumer","afk-family-property-transport")
AFKMemberSpecializationConsumerRef ->
  K3CUseDeclarationBody("consumer","afk-member-specialization")
FiniteSpecialSoundnessPurposeRef ->
  K3CUseDeclarationBody("purpose","finite-special-soundness")
AFKTheoremSourcePropertyPurposeRef ->
  K3CUseDeclarationBody("purpose","afk-theorem-source-property")
AFKExactTheoremFamilyTransportPurposeRef ->
  K3CUseDeclarationBody("purpose","afk-exact-theorem-family-transport")
AFKFamilyTargetSpecializationPurposeRef ->
  K3CUseDeclarationBody("purpose","afk-family-target-specialization")
AFKExactFamilyMemberSpecializationPurposeRef ->
  K3CUseDeclarationBody("purpose","afk-exact-family-member-specialization")
```

```text
K3CUseContract(accepted_kinds,exact_qualification,attenuation,policy) =
  AnalysisUseSemanticsContract {
    accepted_subject_and_result_kinds: accepted_kinds,
    qualification_predicate_or_exact_match: exact_qualification,
    capability_attenuation_law: attenuation,
    operation_policy_compatibility_law: policy,
    failure_classification: common K3-C outcome partition
  }

CryptographicAnalysisUseSemanticsEntries = CanonicalKeySortedSeq [
  {ExactInheritedConditionalQualificationRef,
   K3CUseContract(
     every active K3-C conditional affirmative judgment,
     byte-identical proposition, conclusion, complete inherited hypothesis
       context, semantic basis, support partition, and operation policy,
     no strengthening or hypothesis erasure,
     exact same policy or an explicitly admitted monotone restriction)},
  {FiniteSpecialSoundnessConsumerRef,
   K3CUseContract(
     [KOutOfNSpecialSoundness with FiniteSpecialSoundnessPurposeRef],
     ExactInheritedConditionalQualificationRef,
     one exact finite-property use only,exact finite-analysis policy)},
  {AFKFamilyPropertyTransportConsumerRef,
   K3CUseContract([
     AsymptoticKOutOfNSpecialSoundness with AFKTheoremSourcePropertyPurposeRef,
     TheoremApplicability with AFKExactTheoremFamilyTransportPurposeRef],
     ExactInheritedConditionalQualificationRef,
     single use by one exact `(AFKV2TheoremSchemaId,F)` transport,
     exact family-transport policy)},
  {AFKMemberSpecializationConsumerRef,
   K3CUseContract([
     AdaptiveKnowledgeSoundnessQltN with
       AFKFamilyTargetSpecializationPurposeRef,
     FamilyInstanceCorrespondence with
       AFKExactFamilyMemberSpecializationPurposeRef],
     ExactInheritedConditionalQualificationRef,
     single use by one exact `(F,n0_literal,S,ell0)` specialization,
     exact member-specialization policy)},
  {FiniteSpecialSoundnessPurposeRef,
   K3CUseContract(
     [KOutOfNSpecialSoundness by FiniteSpecialSoundnessConsumerRef],
     ExactInheritedConditionalQualificationRef,
     no family or theorem transport,exact finite-analysis policy)},
  {AFKTheoremSourcePropertyPurposeRef,
   K3CUseContract([
     AsymptoticKOutOfNSpecialSoundness by
       AFKFamilyPropertyTransportConsumerRef],
     ExactInheritedConditionalQualificationRef,
     source-property input only,exact family-transport policy)},
  {AFKExactTheoremFamilyTransportPurposeRef,
   K3CUseContract([
     TheoremApplicability by AFKFamilyPropertyTransportConsumerRef],
     ExactInheritedConditionalQualificationRef,
     structural-applicability input only,exact family-transport policy)},
  {AFKFamilyTargetSpecializationPurposeRef,
   K3CUseContract([
     AdaptiveKnowledgeSoundnessQltN by AFKMemberSpecializationConsumerRef],
     ExactInheritedConditionalQualificationRef,
     family-target input at one index only,exact member-specialization policy)},
  {AFKExactFamilyMemberSpecializationPurposeRef,
   K3CUseContract([
     FamilyInstanceCorrespondence by AFKMemberSpecializationConsumerRef],
     ExactInheritedConditionalQualificationRef,
     pointwise-correspondence input only,exact member-specialization policy)}
]

AnalysisUseSemanticsCatalog(B) contains exactly
`CryptographicAnalysisUseSemanticsEntries` in the active K3-C regime. Each
entry is keyed by the complete resolved coordinate and declaration body, not
its display tag. A missing, extra, cross-consumer, cross-purpose, cross-family,
weakened-qualification, or body-mismatched entry refuses use.

K3CNativeRule(rule_coordinate,payload) =
  NativeRuleSource(NativeRuleSchema {
    rule_coordinate: rule_coordinate,
    canonical_rule_payload:
      CanonicalValue<resolved and lifted payload type of rule_coordinate>(
        payload)
  })

SchnorrSpecialSoundnessSemanticBasisBody(S,Ext) =
  AnalysisSemanticBasisBody {
    family: KOutOfNSpecialSoundness,
    rule_source: K3CNativeRule(
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
    source_read_purposes:
      exact purposes in SchnorrRelationSemanticReadManifestId(S),
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
    non_hypothesis_premise_bindings: [exact_witness_binding],
    established_hypothesis_node_bindings: established_node_bindings,
    assumed_hypothesis_node_bindings: assumed_node_bindings,
    source_support_bindings: [ExactManifestSupportBinding {
      semantic_read_manifest_id:
        SchnorrRelationSemanticReadManifestId(S),
      source_support_coordinate: source_support
    }]
  }

SchnorrSpecialSoundnessJudgmentSchema(S,Ext) = {
  exact proposition: SchnorrSpecialSoundnessProposition(S,Ext),
  exact quantified witness: Ext,
  semantic basis: SchnorrSpecialSoundnessSemanticBasisId(S,Ext),
  support: exact admitted support body above,
  result: Affirmative conditional KOutOfNSpecialSoundness judgment inheriting
    GammaSpecialId(S,Ext),
  live capability purpose:
    FiniteSpecialSoundnessPurposeRef for
    FiniteSpecialSoundnessConsumerRef only; no family-transport use
}
```

The established and assumed hypothesis-node maps must be disjoint and their
domains must partition every and only the seven reachable DAG nodes. Each established entry supplies an
exact affirmative premise capability; each assumed entry names the same goal
ID without pretending to establish it. The native rule may therefore produce a
conditional source judgment even when fixed-extractor correctness remains an
explicit assumption; it never mints an affirmative universal-correctness
judgment from finite evaluation. Failure of one candidate still refutes only
that candidate, never the existential family.

## 4. Classical adaptive Fiat--Shamir experiment

### 4.1 Adversary and quantifier order

The theorem target is classical and adaptive in the Statement. Its native AFK
quantifiers range over one asymptotic protocol family, not over the finitely
many lengths admitted by one K1 `ValueType`. The exact family profile is formed
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

`P^a` may be randomized in the outer Definition-10 experiment. For the
theorem-granted black-box extraction, its initially sampled coin tape is fixed
before extractor interaction, yielding the deterministic next-message strategy
of Remark 2. Every rerun rewinds that same strategy state and retains the same
coin fixing. Resampling prover coins between reruns is outside this profile;
that branch would invalidate the `P <= Q + 1` step used by the transported
bound.

The full distribution equality across the two probability spaces,
failure/abort treatment, input-length coordinate, and native success inequality
are part of the target `AnalysisExperimentProfile` and proposition identity,
not an uninterpreted citation field. An adversary gets only the typed random-
oracle query capability, never the hidden table. The theorem-granted extractor
may receive exactly the programming, lazy-sampling, and rerun capabilities
stated by that schema; those capabilities are not K2 replay and are unavailable
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
    ModuleDeclarationRef<"analysis.resource-operation">

AFKClassicalRandomOracleProfileBody(S: K3CSubjectTuple) = {
  output_type: ModelValue(K3CChallengeDomainId(S)),
  exact_support_predicate:
    membership in K3CChallengeDomainId(S),
  exact_probability_mass_or_measure_law:
    repeated indices return the same value and every first query at a new index
    returns a jointly independent uniform model value, including adaptively
    chosen and off-image indices,
  parameter_and_security_parameter_coordinates:
    [S,StatementLength(K3CStatementType(S))],
  independence_and_correlation_declarations:
    hidden table belongs to the experiment; ordinary P^a and V receive only
    query capability; E receives exactly the selected simulation/programming
    capability,
  sampling_or_oracle_denotation:
    one total lazy function from every admitted AFKRandomOracleIndex(S) to the
    exact finite model values with query ABI
    `Query(AFKRandomOracleIndex(S)) -> ModelValue(K3CChallengeDomainId(S))`,
  failure_and_nontermination_law: total and failure-free
}

AFKClassicalRandomOracleProfileId(S: K3CSubjectTuple) =
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

AFKAdaptiveQQueryProverProfileBody(S: K3CSubjectTuple) = {
  role: adaptive Fiat--Shamir prover,
  dependent_parameter_schema: [
    n: StatementLength(K3CStatementType(S)),
    Q: AFKAdversaryROQueryCount(S) with 0 <= Q <
      ModelCardinality(K3CChallengeDomainId(S))
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

AFKExtractorProfileBody(S: K3CSubjectTuple) = {
  input_types: [StatementLength(K3CStatementType(S))],
  output_types: [K3CStatementType(S), AFKProofType(S), BitString,
                 TerminalVerdict, K3CWitnessType(S)],
  private_state_and_randomness_types:
    [extractor state, extractor coins, lazy random-function state],
  allowed_source_oracle_capabilities:
    [black-box prover invocation, typed RO simulation and programming],
  rerun_fork_rewind_programming_rights:
    exact lazy-sampling, rerun, and programming contract selected here,
  state_preservation_relation:
    same-index consistency except exact programmed points under the contract,
  output_distribution_preservation_relation:
    IdenticalMarginalLaw on (x,pi,aux,v),
  witness_success_relation:
    v = Accept and RelationHolds(S.relation_instance_id,x,w),
  termination_and_asymptotic_resource_law:
    for a concrete member, only the exact expected-call/resource proposition;
    this profile makes no asymptotic-uniformity claim,
  counterfactual_capability_contract:
    Analysis-owned AFK oracle/fork interface, never K2 ReplayRun,
  property_family_scope: AdaptiveKnowledgeExtractionAtFixedLengthQltN
}

AdaptiveQQueryProver(S, n, Q, RO_ABI) = {
  ordinary_inputs: [],
  ambient_instance: AFKFixedPublicSetupId(S),
  capabilities: [AFKRandomOracleQueryABI(S)],
  output: (x: K3CStatementType(S), pi: AFKProofType(S), aux: BitString),
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
  output: (x: K3CStatementType(S),
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
  output: (x: K3CStatementType(S),
           pi: AFKProofType(S), aux: BitString,
           v: TerminalVerdict, w: K3CWitnessType(S)),
  total_mass: 1
}

AFKAdversaryRunningAlgorithmSchema(S) = {
  parameter_schema: [
    n: StatementLength(K3CStatementType(S)),
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
K3CConstantOnePolynomialProfileBody(S: K3CSubjectTuple) = {
  input_sort: StatementLength(K3CStatementType(S)),
  coefficient_domain: Nat,
  value_shape: exactly coefficients_low_to_high = [1],
  canonical_degree_rule: degree = 0,
  evaluation: exact checked-natural constant function returning 1,
  positivity_rule: value is 1 for every admitted Statement length,
  admitted_coefficient_and_degree_bounds: coefficient = 1 and degree = 0
}

K3CConstantOnePolynomialProfileId(S: K3CSubjectTuple) =
  AnalysisPositivePolynomialProfileId(
    B, K3CConstantOnePolynomialProfileBody(S))

K3CConstantOnePolynomialId(S: K3CSubjectTuple) =
  AnalysisPositivePolynomialId(B, {
    profile_id: K3CConstantOnePolynomialProfileId(S),
    coefficients_low_to_high: [1]
  })

AFKMemberKnowledgeExperimentProfile(
    S: K3CSubjectTuple,
    ell0: StatementLength(K3CStatementType(S))) = {
  family: AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  source_profile_id: AFKFreshFsSourceProfileId,
  quantifier_prefix: [
    ExistsUniformBlackBoxExtractor(AFKExtractorProfileId(S), E),
    ForAllQuantitativeValue(
      AFKAdversaryROQueryCount(S),
      0 <= Q < ModelCardinality(K3CChallengeDomainId(S)), Q),
    ForAllStrategy(
      AFKAdaptiveQQueryProverProfileId(S),
      AdaptiveQQueryProver(S, ell0, Q, exact RO ABI), P^a)
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
    S: K3CSubjectTuple,
    ell0: StatementLength(K3CStatementType(S))) = AnalysisQuestionBody {
  family: AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  exact_subjects: CanonicalUnion(
    AFKTargetSubjectProjection(S),
    [K3CChallengeDomainId(S), AFKFixedPublicSetupId(S)]),
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
  }
}

AFKMemberKnowledgeGoal(
    S: K3CSubjectTuple,
    ell0: StatementLength(K3CStatementType(S))) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B, AFKMemberKnowledgeQuestion(S,ell0)),
  conclusion_family: AdaptiveKnowledgeExtractionAtFixedLengthQltN,
  hypothesis_free_conclusion:
    the exact IdenticalMarginalLaw holds and
    extractor_witness_success(S,ell0,Q,P^a,E) is at least the application of
      AFKKnowledgeSuccessFormulaId(S) to
      (epsilon(S,ell0,Q,P^a), ell0, Q), and the expected invocation count is at
      most AFKExpectedCallsFormulaId(S)(Q)
}
```

`AFKTranscriptExtractionFormulaId(S)` is an applicability/proof-intermediate
formula corresponding to AFK Lemma 4. It is checked when the theorem template
is instantiated, but it is not a fourth result of the Definition-10 target
property and therefore does not enter this question or goal.

The active nominal spellings are aliases for the common K1 constructors, not
additional identity formulas:

```text
SchnorrRelationSourceProfileId =
  AnalysisSourceProfileId(B, SchnorrRelationSourceProfileBody)
SchnorrRelationSemanticReadManifestId(S: K3CSubjectTuple) =
  AnalysisSemanticReadManifestId(
    B, SchnorrRelationSemanticReadManifestBody(S))
SchnorrSpecialSoundnessExperimentProfileId(S: K3CSubjectTuple) =
  AnalysisExperimentProfileId(
    B, SchnorrSpecialSoundnessExperimentProfile(S))
SchnorrFixedExtractorUniversalExperimentProfileId(S: K3CSubjectTuple) =
  AnalysisExperimentProfileId(
    B, SchnorrFixedExtractorUniversalExperimentProfile(S))

AFKFreshFsSourceProfileId =
  AnalysisSourceProfileId(B, AFKFreshFsSourceProfileBody)
AFKTargetSemanticReadManifestId(S: K3CSubjectTuple) =
  AnalysisSemanticReadManifestId(B, AFKTargetSemanticReadManifestBody(S))
AFKAdaptiveQQueryProverProfileId(S: K3CSubjectTuple) =
  AnalysisStrategyClassProfileId(B, AFKAdaptiveQQueryProverProfileBody(S))
AFKExtractorProfileId(S: K3CSubjectTuple) =
  AnalysisExtractorProfileId(B, AFKExtractorProfileBody(S))
AFKMemberKnowledgeExperimentProfileId(
    S: K3CSubjectTuple,
    ell0: StatementLength(K3CStatementType(S))) =
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

Applicability consumes the current K2 views:

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
commitment in their K2-defined order and framing. The Statement and commitment
maps come from the checked K3-B/K2 sources. An omitted, late, reordered, or
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
  CanonicalByteString under the exact K1 family bound

AFKLogicalQuery_FixedSetup(Y, A) =
  CanonicalEncode(
    exact K2 DerivedPrefix at the challenge for this setup, Y, and A,
    exact K2 ChallengeNamespace at draw zero)

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
image, that process must additionally agree with the K2 construction's encoded
query. In particular, it preserves same-index repeat consistency, the joint
independent-uniform law at distinct indices even when later indices are chosen
adaptively, exact logical-query counting, and every theorem-authorized
rerun/programming operation used by the extractor, including off-image points.
One K2 squeeze/decoder invocation corresponds to one first query at its
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

K2 supports bounded rejection and an explicit `SamplingExhausted` outcome.
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

### 4.4 Asymptotic family profile and concrete-member split

The Definition-10 subject is a mathematical family. It is not an infinite
sequence of native K1/K2 objects. The family ID therefore authenticates only
one finite language reference and one finite payload:

```text
AFKSchnorrFamilyDefinitionBody(language_ref,payload) =
  AnalysisAsymptoticProtocolFamilyDefinitionBody(language_ref,payload)

AFKSchnorrFamilyDefinitionId(language_ref,payload) =
  AnalysisAsymptoticProtocolFamilyDefinitionId(
    B,language_ref,payload)

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
    common K3-C source-ingress failure partition)

AFKFamilyFreshAbstractSlotCatalog = CanonicalSeq [
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("statement",ValueCarrier),
    0,Statement_F(n),
    exact Statement projection of one member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("witness",ValueCarrier),
    1,Witness_F(n),
    exact Witness projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("relation",Predicate),2,
    Relation_F(n): Statement_F(n) * Witness_F(n) -> Bool,
    exact relation projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("commitment",ValueCarrier),
    3,Commitment_F(n),
    exact first-message projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("challenge-set",ValueCarrier),
    4,ChallengeSet_F(n),
    exact finite nonempty challenge-set projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("response",ValueCarrier),
    5,Response_F(n),
    exact response projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "fresh-experiment",ExperimentProcess),6,Fresh_F(n),
    exact Fresh experiment projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("verifier",VerifierProcess),
    7,Verifier_F(n),
    exact verifier projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "verifier-output",ValueCarrier),8,VerifierOutput_F(n),
    exact verifier-output projection of that member)
]

AFKFamilyTargetAdditionalAbstractSlotCatalog = CanonicalSeq [
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("public-setup",ValueCarrier),
    9,PublicSetup_F(n),
    exact public-setup projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "fiat-shamir-experiment",ExperimentProcess),10,FiatShamir_F(n),
    exact Fiat--Shamir experiment projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef("proof",ValueCarrier),
    11,Proof_F(n),
    exact proof projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "auxiliary-output",ValueCarrier),12,Aux_F(n),
    exact auxiliary-output projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "random-oracle-index",ValueCarrier),13,RandomOracleIndex_F(n),
    exact random-oracle-index projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "statement-length",QuantitativeValue),14,statement_length_F(n),
    exact statement-length projection of that member),
  AFKAbstractSourceRole(K3CFamilyRoleKindRef(
      "resource-measures",ResourceMeasure),15,resource_measures_F(n),
    exact resource-measure projection of that member)
]

AFKFamilyFreshSourceProfileBody = {
  family_tag: AFKAbstractFreshFamilySource,
  slot_schemas: AFKFamilyFreshAbstractSlotCatalog,
  closed_field_read_set:
    exact projections of those roles from one abstract family member,
  adequacy_predicate:
    every projection comes from the same member and has the declared dependent
    carrier or relation signature
}

AFKFamilyTargetSourceProfileBody = {
  family_tag: AFKAbstractFreshFsFamilySource,
  slot_schemas:
    CanonicalConcat(AFKFamilyFreshAbstractSlotCatalog,
                    AFKFamilyTargetAdditionalAbstractSlotCatalog),
  closed_field_read_set:
    exact projections of those roles from one abstract family member,
  adequacy_predicate:
    Fresh/FS roles share the same interaction, relation, setup, and role
    carriers and every target projection comes from that one member
}

AFKFamilyFreshSourceProfileId =
  AnalysisSourceProfileId(B,AFKFamilyFreshSourceProfileBody)
AFKFamilyTargetSourceProfileId =
  AnalysisSourceProfileId(B,AFKFamilyTargetSourceProfileBody)

SchnorrRelationSpecialSoundnessSourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody {
    allowed_slot_variant: ConcreteOwnerSource,
    exact_slot_and_field_schema: SchnorrSourceSlotCatalog,
    exact_adequacy_schema:
      one shared Fresh Protocol/Core, one exact relation seam, and complete
      Statement/claim/Witness/check/terminal agreement,
    failure_classification: common K3-C source-ingress failure partition
  }

AFKAdaptiveFreshFsSourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody {
    allowed_slot_variant: ConcreteOwnerSource,
    exact_slot_and_field_schema:
      CanonicalConcat(SchnorrSourceSlotCatalog,AFKAdditionalSourceSlotCatalog),
    exact_adequacy_schema:
      Schnorr source adequacy plus exact same-Core Fresh/FS construction and
      complete fixed-setup/query-index agreement,
    failure_classification: common K3-C source-ingress failure partition
  }

AFKAbstractFreshFamilySourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody {
    allowed_slot_variant: AbstractFamilyRole,
    exact_slot_and_field_schema: AFKFamilyFreshAbstractSlotCatalog,
    exact_adequacy_schema:
      all projections resolve from one member with their exact dependent
      signatures,
    failure_classification: common K3-C source-ingress failure partition
  }

AFKAbstractFreshFsFamilySourceDeclarationBody =
  AnalysisSourceFamilyDeclarationBody {
    allowed_slot_variant: AbstractFamilyRole,
    exact_slot_and_field_schema:
      CanonicalConcat(AFKFamilyFreshAbstractSlotCatalog,
                      AFKFamilyTargetAdditionalAbstractSlotCatalog),
    exact_adequacy_schema:
      all projections resolve from one member and Fresh/FS share the same
      interaction, relation, setup, and role carriers,
    failure_classification: common K3-C source-ingress failure partition
  }

SchnorrRelationSpecialSoundnessSource =
  the one exact AnalysisSourceFamilyCoordinate whose resolved body is
  SchnorrRelationSpecialSoundnessSourceDeclarationBody
AFKAdaptiveFreshFsSource =
  the one exact AnalysisSourceFamilyCoordinate whose resolved body is
  AFKAdaptiveFreshFsSourceDeclarationBody
AFKAbstractFreshFamilySource =
  the one exact AnalysisSourceFamilyCoordinate whose resolved body is
  AFKAbstractFreshFamilySourceDeclarationBody
AFKAbstractFreshFsFamilySource =
  the one exact AnalysisSourceFamilyCoordinate whose resolved body is
  AFKAbstractFreshFsFamilySourceDeclarationBody

K3CSourceFamilyContract(body) = AnalysisSourceFamilySemanticsContract {
  allowed_slot_variant: body.allowed_slot_variant,
  exact_slot_and_field_schema: body.exact_slot_and_field_schema,
  exact_adequacy_schema: body.exact_adequacy_schema,
  failure_classification: body.failure_classification
}

CryptographicAnalysisSourceFamilySemanticsEntries = CanonicalKeySortedSeq [
  {SchnorrRelationSpecialSoundnessSource,
   SchnorrRelationSpecialSoundnessSourceDeclarationBody,
   K3CSourceFamilyContract(
     SchnorrRelationSpecialSoundnessSourceDeclarationBody)},
  {AFKAdaptiveFreshFsSource,AFKAdaptiveFreshFsSourceDeclarationBody,
   K3CSourceFamilyContract(AFKAdaptiveFreshFsSourceDeclarationBody)},
  {AFKAbstractFreshFamilySource,
   AFKAbstractFreshFamilySourceDeclarationBody,
   K3CSourceFamilyContract(AFKAbstractFreshFamilySourceDeclarationBody)},
  {AFKAbstractFreshFsFamilySource,
   AFKAbstractFreshFsFamilySourceDeclarationBody,
   K3CSourceFamilyContract(AFKAbstractFreshFsFamilySourceDeclarationBody)}
]

AnalysisSourceFamilySemanticsCatalog(B) =
  the authenticated mapping with exactly
  CryptographicAnalysisSourceFamilySemanticsEntries for the active K3-C regime;
  a missing, extra, duplicate, or body-mismatched entry rejects regime support
```

The selected language declaration must resolve under the exact three-field
grammar in [`analysis-model.md`](analysis-model.md#23-asymptotic-family-ingress),
its lifted payload type must contain `payload`, and its contract must denote
the abstract fields above. None of those fields is a `K3CSubjectTuple`,
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
finite K2 sampler:

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
```

The uniform algorithm profiles are logical algorithm schemas. They are not K1
portable algorithms and do not inherit K1's finite iteration limit:

```text
AFKFamilySourceExtractorProfileBody(F) = {
  input_types: [n : LogicalNat, AFKSpecialSoundnessPair_F(n)],
  output_types: [Witness_F(n)],
  private_state_and_randomness_types: [Unit,Unit],
  allowed_source_oracle_capabilities: [],
  rerun_fork_rewind_programming_rights: none,
  state_preservation_relation: deterministic stateless evaluation,
  output_distribution_preservation_relation: deterministic singleton law,
  witness_success_relation:
    every admitted pair maps to a Witness satisfying Relation_F(n),
  termination_and_asymptotic_resource_law:
    total and polynomial in the exact family length measure,
  counterfactual_capability_contract: none,
  property_family_scope: AsymptoticKOutOfNSpecialSoundness(k=2)
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
      statement_length_F(Statement)=n,
  private_state_type: family-declared prover state,
  initial_advice_type: family-declared private advice quantified with P^a,
  allowed_views: own private state, advice, randomness, and prior query answers,
  allowed_oracles_and_capabilities:
    only AFKFamilyRandomOracleQueryABI(F,n),
  legal_move_relation:
    every query inhabits RandomOracleIndex_F(n), at most Q counted calls occur
    including repeats and off-image calls, and the final output has length n,
  extractor_rerun_coin_law:
    sample a prover coin tape once at the outer experiment boundary, fix it
    into the deterministic next-message strategy of Remark 2, and retain it
    across every extractor rerun,
  stop_and_noncompletion_law:
    exactly one total output; no polynomial-time requirement,
  resource_dimensions:
    [AFKFamilyROQueryDimension(F)] with parameters n and Q
}

AFKFamilyTargetExtractorProfileBody(F) = {
  input_types: [n : LogicalNat],
  output_types:
    [(Statement_F(n),Proof_F(n),Aux_F(n),VerifierOutput_F(n),Witness_F(n))],
  private_state_and_randomness_types:
    [family extractor state,fresh extractor coins],
  allowed_source_oracle_capabilities:
    black-box P^a invocation and the exact independent family-RO
    simulation/programming contract,
  rerun_fork_rewind_programming_rights:
    create independent lazy random-function tables, invoke and rerun the
    same deterministic black-box next-message strategy with its initially
    fixed prover coins retained, inspect only query/answer traffic exposed by
    the query ABI, and
    program one not-yet-defined table index to a selected challenge; no K2
    replay capability and no access to hidden oracle-table entries,
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
  counterfactual_capability_contract:
    exact classical lazy-RO simulation/programming contract for restricted
    adaptive knowledge soundness; the input ABI excludes Q, epsilon, prover
    code, and the oracle table,
  property_family_scope:
    AdaptiveKnowledgeSoundnessQltN; QROM and generic restoration are unsupported
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
    ExistsUniformExtractorFamily(AFKFamilySourceExtractorProfileId(F),Ext_F),
    ForAllLogicalNat(true,n),
    ForAllFamilyValue(
      F,AFKSpecialSoundnessPair_F(n),admitted_pair_F(n),pair)
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
      AFKLogicalNatPositivePolynomialProfileId,q_KS),
    ExistsUniformBlackBoxExtractor(AFKFamilyTargetExtractorProfileId(F),E),
    ForAllLogicalNat(true,n),
    ForAllQuantitativeValue(
      QueryCount<AFKFamilyROQueryDimension(F)>,
      0 <= Q < AFKFamilyConstantChallengeCardinality(F),Q),
    ForAllStrategy(
      AFKFamilyAdaptiveProverProfileId(F),
      exact total-output adaptive Q-query member strategy,P^a)
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
    exact `exists uniform Ext_F; forall n; forall pair` relation conclusion
}

AFKFamilySpecialSoundnessGoal(F) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B,AFKFamilySpecialSoundnessQuestion(F)),
  conclusion_family: AsymptoticKOutOfNSpecialSoundness,
  hypothesis_free_conclusion:
    one uniform polynomial-time Ext_F extracts a valid Witness_F(n) from every
    admitted two-transcript pair for every n : LogicalNat
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
  }
}

AFKFamilyAdaptiveKnowledgeGoal(F) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B,AFKFamilyAdaptiveKnowledgeQuestion(F)),
  conclusion_family: AdaptiveKnowledgeSoundnessQltN,
  hypothesis_free_conclusion:
    Definition 10's marginal equality, witness-success inequality, and
    expected-polynomial extractor law hold under
    0 <= Q < AFKFamilyConstantChallengeCardinality(F) for every
    n and every admitted P^a
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
  }

AFKFamilyPremiseGoal(F,family,payload,extra_subjects) =
  AnalysisGoalBody {
    question_id: AnalysisQuestionId(
      B,AFKFamilyPremiseQuestion(F,family,payload,extra_subjects)),
    conclusion_family: family,
    hypothesis_free_conclusion: payload.exact_proposition
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
    {0,AnalysisGoalId(B,AFKFamilyDenotationGoal(F)),[]},
    {1,AnalysisGoalId(B,AFKFamilyProjectionCoherenceGoal(F)),[0]},
    {2,AnalysisGoalId(B,AFKFamilyChallengeAndAlgebraGoal(F)),[0,1]},
    {3,AnalysisGoalId(B,AFKFamilyRelationEfficiencyGoal(F)),[0,1]},
    {4,AnalysisGoalId(B,AFKFamilyVerifierEfficiencyGoal(F)),[0,1]}
  ],
  roots: [2,3,4]
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

K3-C deliberately defines no native semantic basis that mints an affirmative
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
AFKV2SelectedAuthority = {
  publication_kind: IACR ePrint archive PDF,
  stable_source_id: "iacr-eprint:2021/1377",
  bibliographic_revision: version 2, 2022-02-16,
  artifact_media_type: application/pdf,
  artifact_sha256:
    93837e2dd7c0e99ef3d06bbb4f235d9ed0dcafb8b96e56d867e7548751e9122c,
  exact_locators: [Definition 4, Definition 10, Definition 11, Lemma 4,
    Section 6.3 adaptive construction immediately before Theorem 4,
    Remark 2, Remark 6, Theorem 4]
}

AFKV2SelectedStatementTemplateBody = {
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
  theorem_status:
    exact k=2 restricted-query consequence justified by the listed lemma,
    adaptive construction, and theorem; not the paper's full all-Q profile
}

AFKV2SelectedStatementContentDigest =
  SHA256(M(AFKV2SelectedStatementTemplateBody))

AFKV2LocalBindingCatalog = CanonicalSeq [
  {0,AsymptoticFamilyParameter,[],
    `one theorem-application family F`},
  {1,LogicalNatParameter(LocalTheoremBindingRef(0)),[0],
    `the same LogicalNat n at source quantifier ordinal 1 and target ordinal 2`},
  {2,PositivePolynomialParameter(LogicalNat),[],
    `target ordinal 0; the exact singleton positive-polynomial profile [1]`},
  {3,QuantifiedStrategyParameter(UniformSourceExtractor),[0],
    `source ordinal 0; one uniform polynomial-time two-transcript extractor`},
  {4,SemanticRole(AcceptingDistinctTranscriptPair),[0,1],
    `source ordinal 2; one accepted same-prefix distinct-challenge pair`},
  {5,QuantifiedStrategyParameter(UniformBlackBoxTargetExtractor),[0],
    `target ordinal 1; one uniform black-box extractor family`},
  {6,SemanticRole(Statement),[0,1],`the family Statement role`},
  {7,SemanticRole(RelationWitness),[0,1],`the family Witness role`},
  {8,SemanticRole(Commitment),[0,1],`the first prover-message role`},
  {9,SemanticRole(Challenge),[0,1],`the public challenge role`},
  {10,SemanticRole(Response),[0,1],`the final prover-message role`},
  {11,SemanticRole(Acceptance),[0,1],`the verifier acceptance predicate`},
  {12,SemanticRole(FixedPublicSetup),[0,1],`the fixed public setup role`},
  {13,SemanticRole(FreshInteraction),[0,1],`the Fresh experiment role`},
  {14,SemanticRole(FiatShamirInteraction),[0,1],`the FS experiment role`},
  {15,SemanticRole(FullRandomOracleProcess),[0,1],
    `the complete classical lazy-random-function process`},
  {16,SemanticRole(Proof),[0,1],`the Fiat--Shamir proof role`},
  {17,SemanticRole(AuxiliaryOutput),[0,1],`the auxiliary-output role`},
  {18,SemanticRole(VerifierOutput),[0,1],`the verifier-output role`},
  {19,SemanticRole(Relation),[0,1],`the relation predicate role`},
  {20,SemanticRole(RandomOracleIndex),[0,1],`the complete oracle-index role`},
  {21,SemanticRole(RandomOracleStatementIndex),[0,1],
    `the injectively encoded Statement component of an oracle index`},
  {22,SemanticRole(RandomOracleCommitmentIndex),[0,1],
    `the injectively encoded commitment component of an oracle index`},
  {23,SemanticRole(Verifier),[0,1],`the source and target verifier role`},
  {24,SemanticRole(ChallengeSampler),[0,1],
    `the exact uniform challenge-sampling role`},
  {25,SemanticRole(BoundedBitStringIndexContract),[0,1,20],
    `RandomOracleIndex is exactly a finite bounded-bitstring domain with one
     canonical injective Statement/commitment encoding and efficient index and
     challenge operations; every table access has the declared query count`},
  {26,ChallengeCardinalityRole(LocalTheoremBindingRef(0)),[0],
    `one fixed finite cardinality N shared by every logical n, with N >= 2`},
  {27,ResourceRole(QueryCount),[0,15,20,25],
    `every adversary random-oracle table lookup, including repeats and
     off-image indices`},
  {28,ResourceRole(ExpectedCount),[0],
    `one complete black-box adversary invocation`},
  {29,QuantitativeParameter(QueryCount(LocalTheoremBindingRef(27))),
    [0,1,26,27],`target ordinal 3; 0 <= Q < N`},
  {30,QuantifiedStrategyParameter(InputFreeAdaptiveOracleProver),
    [0,1,20,27,29],`target ordinal 4; one total-output Q-query prover`}
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
  authority:
    AFKV2AuthorityContractRef :
      ModuleDeclarationRef<"analysis.theorem-authority">,
  proof_status:
    AFKV2ProofStatusContractRef :
      ModuleDeclarationRef<"analysis.theorem-proof-status">,
  property:
    AFKV2PropertySchemaContractRef :
      ModuleDeclarationRef<"analysis.theorem-property-schema">,
  experiment:
    AFKV2ExperimentSchemaContractRef :
      ModuleDeclarationRef<"analysis.theorem-experiment-schema">,
  source_view:
    AFKV2SourceViewSchemaContractRef :
      ModuleDeclarationRef<"analysis.theorem-source-view-schema">,
  map:
    AFKV2MapSchemaContractRef :
      ModuleDeclarationRef<"analysis.theorem-map-schema">,
  side_condition:
    AFKV2SideConditionSchemaContractRef :
      ModuleDeclarationRef<"analysis.theorem-side-condition-schema">,
  transform:
    AFKV2TransformProgramContractRef :
      ModuleDeclarationRef<"analysis.theorem-transform-program">,
  conclusion:
    AFKV2ConclusionLawContractRef :
      ModuleDeclarationRef<"analysis.theorem-conclusion-law">
}

AnalysisTheoremComponentSemanticsCatalog(B) contains exactly these active K3-C
entries, keyed by the complete declaration references above:

  AFKV2AuthorityContractRef ->
    AnalysisTheoremComponentSemanticsContract<"analysis.theorem-authority"> {
      exact_component_payload_meta_schema: CanonicalRecord {
        selected_authority: exact AFK authority record,
        selected_statement_content_digest: Bytes32
      },
      admitted_local_binding_kinds_and_occurrence_paths: [],
      exact_component_interpretation_law:
        select exactly the pinned artifact, locator set, and restricted statement
        digest; establish no theorem truth,
      cross_component_coherence_law:
        the digest is exactly AFKV2SelectedStatementContentDigest,
      failure_classification: common K3-C outcome partition
    },

  AFKV2ProofStatusContractRef ->
    AnalysisTheoremComponentSemanticsContract<"analysis.theorem-proof-status"> {
      exact_component_payload_meta_schema: CanonicalRecord {
        authority_class: exactly ImportedPaperOnly,
        admitted_proof_artifact: exactly None,
        truth_discharge_mode:
          exactly ExternalPostFormationTheoremTruthProposition,
        schema_admission_establishes_truth: exactly false
      },
      admitted_local_binding_kinds_and_occurrence_paths: [],
      exact_component_interpretation_law:
        theorem truth can enter only through TheoremTruthGoal after formation,
      cross_component_coherence_law:
        the authority component has the same restricted statement digest,
      failure_classification: common K3-C outcome partition
    },

  AFKV2PropertySchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<"analysis.theorem-property-schema"> {
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
      failure_classification: common K3-C outcome partition
    },

  AFKV2ExperimentSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<"analysis.theorem-experiment-schema"> {
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
      failure_classification: common K3-C outcome partition
    },

  AFKV2SourceViewSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
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
      failure_classification: common K3-C outcome partition
    },

  AFKV2MapSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<"analysis.theorem-map-schema"> {
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
      failure_classification: common K3-C outcome partition
    },

  AFKV2SideConditionSchemaContractRef ->
    AnalysisTheoremComponentSemanticsContract<
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
      failure_classification: common K3-C outcome partition
    },

  AFKV2TransformProgramContractRef ->
    AnalysisTheoremComponentSemanticsContract<
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
      failure_classification: common K3-C outcome partition
    },

  AFKV2ConclusionLawContractRef ->
    AnalysisTheoremComponentSemanticsContract<"analysis.theorem-conclusion-law"> {
      exact_component_payload_meta_schema:
        exactly the closed conclusion-reconstruction record displayed below,
      admitted_local_binding_kinds_and_occurrence_paths:
        exactly the local operator refs selected by that record,
      exact_component_interpretation_law:
        reconstruct only AFKV2TargetPropertyComponent and retain every listed
        obligation,
      cross_component_coherence_law:
        the reconstructed target and operators equal the enclosing components,
      failure_classification: common K3-C outcome partition
    }.

The phrase “displayed below” in this catalog is a same-page grammar reference:
admission expands the referenced canonical record fields and tags before hashing
or comparison. It is not a label accepted in place of the body. A missing,
extra, reordered, differently typed, or payload-less variant is malformed; a
different complete declaration coordinate is unsupported.

AFKV2Component<C>(contract_ref:ModuleDeclarationRef<C>,payload) =
  TheoremSchemaComponent<C> {
    contract_ref: contract_ref,
    canonical_payload:
      CanonicalValue<resolved and lifted payload type of contract_ref>(payload)
  }

AFKV2AuthorityComponent = AFKV2Component(
  AFKV2AuthorityContractRef,{
    selected_authority: AFKV2SelectedAuthority,
    selected_statement_content_digest:
      AFKV2SelectedStatementContentDigest
  })

AFKV2ProofStatusComponent = AFKV2Component(
  AFKV2ProofStatusContractRef,{
    authority_class: ImportedPaperOnly,
    admitted_proof_artifact: None,
    truth_discharge_mode: ExternalPostFormationTheoremTruthProposition,
    schema_admission_establishes_truth: false
  })

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
  authority_coordinate: AFKV2AuthorityComponent,
  authority_and_proof_status_contract: AFKV2ProofStatusComponent,
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
```

The PDF digest identifies the selected source artifact; the separately derived
statement-content digest identifies the exact restricted theorem statement
that this schema claims. A journal revision, all-query target, different
quantifier order, changed expected-call unit, or changed map forms a different
schema.

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
is a symbolic dependent value, not evaluation of a K1 function. The exact
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
AFKKnowledgeErrorFormulaBody(S: K3CSubjectTuple) = {
  result_sort: Probability,
  parameter_schema: [
    n: StatementLength(K3CStatementType(S)),
    Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [n],
  expression:
    BoundedCountRatioAsProbability(
      AddSameSort(
        Q, CountConstant<AFKAdversaryROQueryCount(S)>(1)),
      ModelCardinality(K3CChallengeDomainId(S)),
      exact natural-magnitude map, exact domain 0 <= Q < N)
}

AFKKnowledgeSuccessFormulaBody(S: K3CSubjectTuple) = {
  result_sort: SignedProbabilityLowerBound,
  parameter_schema: [
    epsilon: Probability,
    n: StatementLength(K3CStatementType(S)),
    Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [],
  expression:
    DivideSignedLowerBoundByPositivePolynomial(
      ProbabilityDifferenceAsSignedLowerBound(
        epsilon,
        BoundedCountRatioAsProbability(
          AddSameSort(
            Q, CountConstant<AFKAdversaryROQueryCount(S)>(1)),
          ModelCardinality(K3CChallengeDomainId(S)),
          exact natural-magnitude map, exact domain 0 <= Q < N)),
      K3CConstantOnePolynomialId(S), n)
}

AFKTranscriptExtractionFormulaBody(S: K3CSubjectTuple) = {
  result_sort: SignedProbabilityLowerBound,
  parameter_schema: [
    epsilon: Probability,
    n: StatementLength(K3CStatementType(S)),
    Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [n],
  expression:
    ScaleSignedLowerBoundByPositiveCountRatio(
      ModelCardinality(K3CChallengeDomainId(S)),
      PredecessorCount(
        ModelCardinality(K3CChallengeDomainId(S)), exact domain N >= 2),
      exact natural-magnitude map,
      ProbabilityDifferenceAsSignedLowerBound(
        epsilon,
        BoundedCountRatioAsProbability(
          AddSameSort(
            Q, CountConstant<AFKAdversaryROQueryCount(S)>(1)),
          ModelCardinality(K3CChallengeDomainId(S)),
          exact natural-magnitude map, exact domain 0 <= Q < N)))
}

AFKExpectedCallsFormulaBody(S: K3CSubjectTuple) = {
  result_sort: ExpectedCount<AFKAdversaryInvocationResourceDimension(S)>,
  parameter_schema: [Q: AFKAdversaryROQueryCount(S)],
  declared_parameter_independence: [],
  expression:
    QueryBoundPlusOverheadAsExpectedCount(
      Q, 2, AFKAdversaryInvocationResourceDimension(S))
}

AFKKnowledgeErrorFormulaId(S: K3CSubjectTuple) =
  AnalysisQuantitativeFormulaId<Probability>(
    B, AFKKnowledgeErrorFormulaBody(S))

AFKKnowledgeSuccessFormulaId(S: K3CSubjectTuple) =
  AnalysisQuantitativeFormulaId<SignedProbabilityLowerBound>(
    B, AFKKnowledgeSuccessFormulaBody(S))

AFKTranscriptExtractionFormulaId(S: K3CSubjectTuple) =
  AnalysisQuantitativeFormulaId<SignedProbabilityLowerBound>(
    B, AFKTranscriptExtractionFormulaBody(S))

AFKExpectedCallsFormulaId(S: K3CSubjectTuple) =
  AnalysisQuantitativeFormulaId<
    ExpectedCount<AFKAdversaryInvocationResourceDimension(S)>>(
      B, AFKExpectedCallsFormulaBody(S))
```

The selected error function has the Definition-10 signature
`kappa_FS,S(n,Q)`; `N` is fixed by `K3CChallengeDomainId(S)`, and the body is
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

For family `F`, the AFK applicability basis binds ordinals `0..3` to
`AFKFamilyKnowledgeErrorFormulaId(F)`,
`AFKFamilyKnowledgeSuccessFormulaId(F)`,
`AFKFamilyTranscriptExtractionFormulaId(F)`, and
`AFKFamilyExpectedCallsFormulaId(F)`. The concrete-member specialization binds
the same templates to the four `S` formulas. A different body, dimension,
domain, parameter order, or polynomial refuses applicability. Theorem
authority and proof status therefore occur in the semantic basis and
hypothesis context, never in ordinary property or formula identity.

### 6.3 Loss imports

```text
AnalysisLossSemanticImport = {
  exact Relations bridge ID,
  exact lossy-use scope and occurrence-coordinate schema,
  exact direction,
  exact source-premise proposition and quantitative-export ID,
  declared Analysis result sort,
  admitted interpretation rule,
  exact parameter substitution,
  per-occurrence expression
}

AnalysisLossSemanticImportId =
  AnalysisId<"analysis.loss-semantic-import">(
    B, AnalysisLossSemanticImportBody)

AnalysisLossSupport = {
  semantic_import_id,
  exact CheckBridgeUseSet result binding,
  exact occurrence-local source-premise result binding,
  exact quantitative-export result binding,
  exact CheckedLossyUseConsumerSource binding,
  owner policy dependency closure
}
```

The complete ledger is derived from the exact K3-B selection. Missing,
duplicated, extra, backward, ungrounded, wrong-sort, wrong-source, or stale
entries refuse. The use count is derived; callers never supply it.

An ordinary loss-bearing property formula names a typed quantitative parameter,
not an import occurrence or checked result. `AnalysisSemanticBasis` maps an
exact `AnalysisLossSemanticImportId` and the derived semantic occurrence/count
coordinates to that parameter; concrete checked-result bindings belong to
`SupportInstantiation`, while fresh K3-B capabilities and the consumer-source
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
  family_payload: payload
}

AFKApplicabilityPremiseGoal(F,family,payload) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(
    B,AFKApplicabilityPremiseQuestion(F,family,payload)),
  conclusion_family: family,
  hypothesis_free_conclusion: payload.exact_proposition
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
    {0,AnalysisGoalId(B,AFKFamilyDenotationGoal(F)),[]},
    {1,AnalysisGoalId(B,AFKFamilyProjectionCoherenceGoal(F)),[0]},
    {2,AnalysisGoalId(B,AFKFamilyFixedChallengeCardinalityGoal(F)),[0,1]},
    {3,AnalysisGoalId(B,AFKFamilyFreshDistributionGoal(F)),[0,1,2]},
    {4,AnalysisGoalId(B,AFKFamilyRandomOracleCorrespondenceGoal(F)),[0,1]},
    {5,AnalysisGoalId(B,AFKFamilyFiniteIndexAndOperationsGoal(F)),[0,1,4]},
    {6,AnalysisGoalId(B,AFKFamilyFixedSetupGoal(F)),[0,1]},
    {7,AnalysisGoalId(B,AFKFamilySamplerAdequacyGoal(F)),[0,1,2,4,5]},
    {8,AnalysisGoalId(
         B,AFKFamilyExperimentObservationCorrespondenceGoal(F)),
       [0,1,2,3,4,5,6,7]}
  ],
  roots: [8]
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
  rule_source: K3CNativeRule(
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
  source_read_purposes: [
    AFKFamilyFreshReadManifestSchemaId(F),
    AFKFamilyTargetReadManifestSchemaId(F)
  ],
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
    non_hypothesis_premise_bindings: [],
    established_hypothesis_node_bindings: established_nodes,
    assumed_hypothesis_node_bindings: assumed_nodes,
    source_support_bindings: [
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyFreshReadManifestSchemaId(F),
        dependent_support_schema: fresh_support,
        exact retained family-support hypotheses:
          GammaAFKApplicabilityId(F)
      },
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyTargetReadManifestSchemaId(F),
        dependent_support_schema: target_support,
        exact retained family-support hypotheses:
          GammaAFKApplicabilityId(F)
      }
    ]
  }

AFKFamilyApplicabilityJudgmentSchema(F) = {
  proposition: AFKFamilyApplicabilityPropositionBody(F),
  semantic_basis: AFKFamilyApplicabilitySemanticBasisId(F),
  support: the exact support schema above,
  result:
    conditional affirmative theorem-applicability judgment inheriting
    GammaAFKApplicabilityId(F),
  live_port:
    attenuated to AFK family property transport for this exact `(T,F)` only
}
```

The established and assumed maps are disjoint and partition all nine
reachable nodes; the unique outward root frontier is `[8]`. The native rule
checks structure against `AFKV2TheoremSchemaId`; the theorem schema is input
data, not the rule that proves its own applicability. Theorem truth is absent
because applicability is a structural/model-matching judgment. Applicability
does not establish the source property, and its port cannot occupy either the
source-property or theorem-truth slot.

### 7.2 Family property transport

Use the one closed `CanonicalGoalDagUnion` constructor from
[`analysis-model.md`](analysis-model.md#45-exact-common-bodies). The transported
proposition inherits, but does not duplicate, the source and applicability
premises:

```text
GammaAFKTheoremTruthBody = AnalysisHypothesisContextBody {
  nodes: [{0,AnalysisGoalId(
    B,TheoremTruthGoal(AFKV2TheoremSchemaId)),[]}],
  roots: [0]
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
  source_read_purposes: [AFKFamilyTargetReadManifestSchemaId(F)],
  conclusion_schema: AFKFamilyAdaptiveKnowledgeGoal(F),
  typed_transform_program:
    independently reconstruct the target goal and its three quantitative
    results from the checked applicability bindings, then inherit the exact
    canonical union of both premise DAGs
}

AFKFamilyTransportSemanticBasisId(F) =
  AnalysisSemanticBasisId(B,AFKFamilyTransportSemanticBasisBody(F))

InheritedAFKFamilyTargetSupportPartition(
    F,source_property_capability,applicability_port,
    theorem_truth_node_treatment) =
  authenticate the exact support records bound to both live inputs; project
  their treatment of every node in GammaAFKFamilySpecialBody(F) and
  GammaAFKApplicabilityBody(F); add the exact theorem-truth node treatment; map
  equal goals through GammaAFKFamilyTargetBody(F); mark a merged node
  established when at least one exact affirmative node capability establishes
  it and otherwise Assumed when at least one authenticated input retains it;
  reject a missing node, unrelated capability, unsupported treatment, or any
  output domain other than every node of GammaAFKFamilyTargetBody(F)

AFKFamilyTransportSupportBody(
    F,source_property_capability,applicability_port,
    theorem_truth_node_treatment,
    target_family_support_schema) =
  AnalysisSupportInstantiationBody {
    semantic_basis_id: AFKFamilyTransportSemanticBasisId(F),
    proposition_id: AnalysisPropositionId(
      B,AFKFamilyAdaptiveKnowledgePropositionBody(F)),
    non_hypothesis_premise_bindings: [
      source_property_capability,applicability_port
    ],
    established_hypothesis_node_bindings:
      EstablishedPartitionOf(InheritedAFKFamilyTargetSupportPartition(
        F,source_property_capability,applicability_port,
        theorem_truth_node_treatment)),
    assumed_hypothesis_node_bindings:
      AssumedPartitionOf(InheritedAFKFamilyTargetSupportPartition(
        F,source_property_capability,applicability_port,
        theorem_truth_node_treatment)),
    source_support_bindings: [FamilyManifestSupportSchemaBinding {
      family_read_manifest_schema_id: AFKFamilyTargetReadManifestSchemaId(F),
      dependent_support_schema: target_family_support_schema,
      exact retained family-support hypotheses:
        GammaAFKFamilyTargetId(F)
    }]
  }

AFKFamilyTransportJudgmentSchema(F) = {
  proposition: AFKFamilyAdaptiveKnowledgePropositionBody(F),
  semantic_basis: AFKFamilyTransportSemanticBasisId(F),
  support: exact support above,
  quantitative_result: [
    AFKFamilyKnowledgeErrorFormulaId(F),
    AFKFamilyKnowledgeSuccessFormulaId(F),
    AFKFamilyExpectedCallsFormulaId(F)
  ],
  result:
    conditional affirmative AdaptiveKnowledgeSoundnessQltN judgment,
  live_capability:
    bound to this exact family proposition, hypotheses, model, and purpose
}
```

A source judgment for a different family, a structural FS result,
an applicability port for another family, or a target proposition supplied by
the caller refuses. Transport never discharges theorem truth, family laws, or
the ROM assumptions merely because they were retained by both inputs.

## 8. Concrete member correspondence and specialization

### 8.1 One representable member

Concrete native objects are related to the abstract family only at one exact
representable index:

```text
AnalysisLogicalNatLiteralBody(n0) = MetaRecord {0: MetaNatural(n0)}
AnalysisLogicalNatLiteralId(n0) =
  AnalysisId<"analysis.logical-nat-literal">(
    B,AnalysisLogicalNatLiteralBody(n0))

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
  the one exact ModuleDeclarationRef<"analysis.afk-family-role-catalog"> whose
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
  [K3CChallengeDomainId(S),AFKFixedPublicSetupId(S)])

AFKNativeMemberRoleRef(S,ell0,role) = {
  native_subject_refs: AFKNativeSubjectRefs(S),
  native_statement_length: ell0,
  role: role : AFKFamilyRoleCoordinate(role.local_role_ordinal)
}

K3CExperimentProcessRef(profile_id,process_ordinal,process_schema) = {
  experiment_profile_id: profile_id,
  local_process_ordinal: process_ordinal,
  exact_process_schema: process_schema
}

K3CVerifierProcessRef(S) = {
  protocol_id: S.fiat_shamir_protocol_id,
  check_ref: S.k2_check_ref,
  accept_terminal_ref: S.k2_accept_terminal_ref,
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
    K3CStatementType(S),K3CWitnessType(S),S.relation_instance_id,
    AFKFixedPublicSetupId(S),K3CCommitmentType(S),
    K3CChallengeDomainId(S),K3CResponseType(S),
    K3CExperimentProcessRef(
      SchnorrSpecialSoundnessExperimentProfileId(S),0,
      exact accepted-pair validation and deterministic extraction process),
    K3CExperimentProcessRef(
      AFKMemberKnowledgeExperimentProfileId(S,ell0),0,
      exact Fiat--Shamir adaptive-prover process),
    AFKProofType(S),BitString,
    K3CVerifierProcessRef(S),
    TerminalVerdict,AFKRandomOracleIndex(S),ell0,
    AFKAdversaryROQueryResourceDimension(S),
    AFKAdversaryInvocationResourceDimension(S),
    K3CConstantOnePolynomialProfileId(S),
    Evaluate(K3CConstantOnePolynomialId(S),ell0),
    ModelCardinality(K3CChallengeDomainId(S))
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

AFKFamilyRoleMapClauseCatalog = CanonicalSeq [
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

AFKFamilyRoleMapClauseCatalogRef =
  the one exact ModuleDeclarationRef<"analysis.afk-family-role-map-clause"> whose
  resolved declaration body is exactly AFKFamilyRoleMapClauseCatalog with the
  common typed source/target/refinement and failure fields

AFKFamilyRoleMapClauseCoordinate(role) = {
  catalog_ref: AFKFamilyRoleMapClauseCatalogRef,
  local_clause_ordinal: role.local_role_ordinal,
  exact_clause_kind:
    AFKFamilyRoleMapClauseCatalog[role.local_role_ordinal].clause_kind
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

RequiredAFKFamilyInstanceRoleMaps(F,n0_literal,S,ell0) =
  CanonicalSeq, in AFKFamilyRoleCatalog ordinal order, of exactly one
  FamilyInstanceRoleMapProposalId for every role in AFKFamilyRoleCatalog

AFKPointwiseQuantitativeNormalizationContractBody(
    F,n0_literal,S,ell0) = {
  logical_index_substitution:
    AFKLocalLogicalNatRef -> Value(n0_literal) -> ell0 under the exact length map,
  challenge_cardinality_substitution:
    FamilyConstantChallengeCardinalityValue(F) ->
      ModelCardinality(K3CChallengeDomainId(S)),
  positive_polynomial_profile_substitution:
    AFKLogicalNatPositivePolynomialProfileId ->
      K3CConstantOnePolynomialProfileId(S),
  positive_polynomial_value_substitution:
    Evaluate(AFKLogicalNatConstantOnePolynomialId,Value(n0_literal)) ->
      Evaluate(K3CConstantOnePolynomialId(S),ell0) -> 1,
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
    family/member error, family/member success,
    family/member transcript extraction, family/member expected calls
  ]
}

AFKPointwiseQuantitativeNormalizationContractId(F,n0_literal,S,ell0) =
  AnalysisId<"analysis.pointwise-quantitative-normalization">(
    B,AFKPointwiseQuantitativeNormalizationContractBody(
      F,n0_literal,S,ell0))

FamilyInstanceCorrespondenceQuestion(
    F,n0_literal:AnalysisLogicalNatLiteralId,
    S:K3CSubjectTuple,
    ell0:StatementLength(K3CStatementType(S))) = AnalysisQuestionBody {
  family: FamilyInstanceCorrespondence,
  exact_subjects: CanonicalAppend(
    CanonicalAppend([F,n0_literal],AFKTargetSubjectProjection(S)),
    [K3CChallengeDomainId(S),AFKFixedPublicSetupId(S)]),
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
  }
}

FamilyInstanceCorrespondenceGoal(F,n0_literal,S,ell0) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(
    B,FamilyInstanceCorrespondenceQuestion(F,n0_literal,S,ell0)),
  conclusion_family: FamilyInstanceCorrespondence,
  hypothesis_free_conclusion:
    FamilyMember(F,Value(n0_literal)) and S at ell0 correspond under every
    exact role proposal, experiment/model law, resource map, and formula map
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
  conclusion_family: family,
  hypothesis_free_conclusion: payload.exact_proposition
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
          B,FamilyInstanceDenotationAtIndexGoal(F,n0_literal,S,ell0)),[]},
      {1,AnalysisGoalId(
          B,FamilyInstanceProjectionAtIndexGoal(
            F,n0_literal,S,ell0)),[0]},
      {2,AnalysisGoalId(B,SchnorrChallengeModelGoal(S)),[]},
      {3,AnalysisGoalId(B,SchnorrAcceptanceRelationGoal(S)),[]},
      {4,AnalysisGoalId(B,AFKFamilyFixedChallengeCardinalityGoal(F)),[0,1]},
      {5,AnalysisGoalId(B,AFKFamilyFiniteIndexAndOperationsGoal(F)),[0,1]},
      {6,AnalysisGoalId(
          B,FamilyInstanceRoleMapAdequacyGoal(F,n0_literal,S,ell0)),
          [0,1,2,3,4,5]},
      {7,AnalysisGoalId(
          B,FamilyInstanceQuantitativeNormalizationGoal(
            F,n0_literal,S,ell0)),[0,1,2,4,6]},
      {8,AnalysisGoalId(
          B,FamilyInstanceProcessCorrespondenceGoal(F,n0_literal,S,ell0)),
          [0,1,5,6]}
    ],
    roots: [7,8]
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
    rule_source: K3CNativeRule(
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
    source_read_purposes: [
      AFKFamilyFreshReadManifestSchemaId(F),
      AFKFamilyTargetReadManifestSchemaId(F),
      SchnorrRelationSemanticReadManifestId(S),
      AFKTargetSemanticReadManifestId(S)
    ],
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
    non_hypothesis_premise_bindings: [],
    established_hypothesis_node_bindings: established_nodes,
    assumed_hypothesis_node_bindings: assumed_nodes,
    source_support_bindings: [
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyFreshReadManifestSchemaId(F),
        dependent_support_schema: family_fresh_support,
        exact retained family-support hypotheses:
          GammaFamilyInstanceId(F,n0_literal,S,ell0)
      },
      FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AFKFamilyTargetReadManifestSchemaId(F),
        dependent_support_schema: family_target_support,
        exact retained family-support hypotheses:
          GammaFamilyInstanceId(F,n0_literal,S,ell0)
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

FamilyInstanceCorrespondenceJudgmentSchema(F,n0_literal,S,ell0) = {
  proposition:
    FamilyInstanceCorrespondencePropositionBody(F,n0_literal,S,ell0),
  semantic_basis:
    FamilyInstanceCorrespondenceSemanticBasisId(F,n0_literal,S,ell0),
  support:
    exact support body above; matching live CheckedFSConstruction and K3-B
    correspondence capabilities are checking-invocation inputs attached to
    their owner support bindings, not semantic premise facts,
  result:
    conditional affirmative FamilyInstanceCorrespondence judgment,
  live_capability:
    attenuated to specialization of this exact `(F,n0_literal,S,ell0)` only
}
```

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
    rule_source: K3CNativeRule(
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
    source_read_purposes: [AFKTargetSemanticReadManifestId(S)],
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
  than the complete specialization-context node set

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
  non_hypothesis_premise_bindings: [
    family_property_capability,instance_capability
  ],
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

AFKMemberSpecializationJudgmentSchema(F,n0_literal,S,ell0) = {
  proposition:
    AFKMemberSpecializationPropositionBody(F,n0_literal,S,ell0),
  semantic_basis:
    AFKMemberSpecializationSemanticBasisId(F,n0_literal,S,ell0),
  support: AFKMemberSpecializationSupportBody with the exact two live premise
    capabilities and their derived canonical support partition,
  result:
    conditional affirmative fixed-length member judgment only
}
```

The finite reference instrument may form these bodies, exercise exact
arithmetic at one `(n0_literal,ell0)`, and reject a changed role, query domain, formula,
hypothesis partition, or capability. It cannot establish the family property,
the correspondence's universal process premise, theorem truth, ROM security,
or any asymptotic statement.

## 9. Explicit unsupported profiles

K3-C returns `Unsupported` for QROM, malicious-verifier zero knowledge,
multi-prover independence, generic state restoration, IOP/IOR-to-concrete-Core
transforms, concrete hash security, and generic property composition. It does
not infer ordinary soundness, zero knowledge, EUF-CMA, round-by-round
soundness, or whole-protocol security from the two selected profiles.
