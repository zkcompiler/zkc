# Oracle-Commitment Construction

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Provisional owner:** `pir`
> **Authority:** None during the transition. Current normative Protocol
> semantics remain under [`docs/`](../../docs/README.md).

## 1. Contract

This page solely owns the target definition of a checked construction from one
exact admitted logical-Oracle Core to one exact independently admitted
commitment-and-opening Core. It defines identities, deterministic bounded
static elaboration and logical maps, a canonical per-run opening-evidence
coverage law, admission and outcomes, process-local authority, inert run
receipts, advice, public replay, bounds, nonclaims, and reversal conditions.

The [Interactive Core](interactive-core.md) owns both Cores, their Oracle
effects, causal execution, public-coin eligibility, and replay. The
[Commitment-Opening Verification](commitment-opening-verification.md) page
owns verifier-side setup, public commitment, query, asserted-answer, evidence,
claim-group, and opening-check meaning. This construction consumes exact
admitted verifier profiles while retaining source/target, producer, advice,
evidence-coverage, authority, and run-validation meaning. The
[Fiat--Shamir construction](fiat-shamir.md) owns challenge interpretation over
one unchanged Core. Foundation owns canonical values, profiles, algorithms,
evaluation contracts, identities, typed failures, and process-local authority.

The construction has the direction

```text
admitted native logical-Oracle Core
  -> checked oracle-commitment construction
admitted committed Core
  -> optional checked same-Core Fiat--Shamir construction
committed Fiat--Shamir Protocol
```

The first arrow changes verifier-visible interaction and therefore changes
`CoreId`. The second arrow does not change the committed Core. A commitment
root is not a logical Oracle, and a checked same-Core Fiat--Shamir construction
is not an Oracle-commitment construction.

Here **profile-wide construction** means one exact source Core, target Core,
commitment profile, advice schema, total static elaboration, and canonical
bounded runtime evidence-coverage law are checked as one structural subject.
It does not
assert that every runtime source execution
has been generated, that every advice value is sound, or that every resulting
target execution agrees. That stronger statement is deliberately absent;
Section 9 validates one exact execution pair at a time. Profile-wide does not
mean every FRI, IOP, IOR, commitment scheme, tree shape, query schedule, or
target implementation.

## 2. Foundation and profile intake

For one exact Foundation `PriorMetaAuthenticationBasis B`, this owner consumes:

- exact `AdmittedCore` handles for source and target;
- `PIRInteractionProfileId`, `PIRPublicSetupProfileId`,
  `PIRCommitmentOpeningProfileId`, and their authenticated import closure;
- exact admitted `CommitmentOpeningVerifierProfile` and
  `CommitmentOpeningUse` handles;
- authenticated `PortableAlgorithmRef` and `EvaluationContractId` pairs;
- exact `ValueType`, `CanonicalValue`, and canonical finite collections; and
- Foundation outcome and deterministic-evaluation mechanisms.

All objects use the same semantic regime and authenticated basis. The profile
directly imports exactly `PIRInteractionProfileId`,
`PIRPublicSetupProfileId`, and `PIRCommitmentOpeningProfileId` and redefines no
PIR meaning. The public-setup edge is direct even though the commitment-opening
profile also imports it, because this owner itself validates source and target
public-setup views.

The exact `PIROracleCommitmentProfile` is the compilation result of the
[`oracle-commitment` owner-source manifest](profiles/oracle-commitment.json)
under the [PIR profile publication grammar](profiles/README.md). Its family is
`"pir.oracle-commitment"`, revision is `0`, direct imports are exactly
`{PIRInteractionProfileId, PIRPublicSetupProfileId,
PIRCommitmentOpeningProfileId}`, and its supported kinds are the eleven
Oracle-commitment subjects enumerated by that manifest. The publication
records the complete body and independently reproduced
`PIROracleCommitmentProfileId`; this page does not maintain a second profile
preimage.

The declaration catalogs are nonempty and source-bound. They contain the
closed owner-body compiler, semantic laws, evaluator signature, failure
schema, selected source fragments, and generated subject-language rows. Their
imported declaration references derive all three direct edges. Concrete
algorithm and evaluation-contract references occur in the commitment-class,
advice-schema, commitment-profile, construction, and receipt-projection
fields below. The semantic law checks one exact use for every written field;
no ambient algorithm registry or role table participates in identity or
admission.

For class `c`, let `V(c)` be the exact authenticated
`CommitmentOpeningVerifierProfile` named by
`c.verifier_profile_id`, let `Setup(c)` be its dependent
`CommitmentSetupAssignmentType`, let `Context(c)` be its dependent
`CommitmentVerificationContextType`, let `ProducerGroup(c)` be the exact dependent
producer group containing `V(c).claim_count` ordered records
`{private_commitment_state,query,asserted_answer}`, and let `DecodedResponse(c)`
be the exact dependent record
`{asserted_answers in claim order,opening_evidence}`. The six class-indexed
ABIs are, in role order:

```text
[Setup(c),OracleCarrierType(c.source_oracle)] -> c.complete_material_type
[Setup(c),c.complete_material_type,c.private_advice_type]
  -> c.private_commitment_state_type
[Setup(c),c.private_commitment_state_type]
  -> V(c).public_commitment_type
[c.source_index_type] -> V(c).query_type
[Setup(c),Context(c),ProducerGroup(c),c.private_advice_type]
  -> c.opening_response_type
[c.opening_response_type] -> DecodedResponse(c)
```

The profile fields below fix the remaining seven ABIs: advice formation is
`[AdviceValueSetType(schema)] -> RootBool`; public projection is
`[AdviceValueSetType(schema),CanonicalSeq<TargetOpeningEvidenceSlot>]
-> schema.public_projection_type`; opening-evidence coverage derivation is
`[RuntimeOpeningEvidenceCoverageInputType(profile)]
-> ConcreteOpeningEvidenceCoverageType(profile)`; bound derivation
uses `ExactCorePairAndProfileShapeType -> IntrinsicConstructionBoundsType`;
static elaboration uses
`ExactCorePairAndProfileShapeType -> OracleCommitmentStaticElaborationType`;
and each receipt projection uses the exact Core completed-record public-view
type selected by that field. Every referenced evaluation contract's exact
typed-failure row is authenticated with its algorithm use. A host exception or
a failure outside the invoked contract's row cannot be treated as a declared
semantic result.

The exact owner body compiler has one arm for every advertised kind and no
default arm:

<!-- zkc-profile-source:oracle-commitment-body-dispatch:start -->

```text
OracleCommitmentBodyV0 =
    AdviceSchemaBody(ConstructionAdviceSchema)
  | CommitmentProfileBody(OracleCommitmentProfile)
  | ConstructionBody(OracleCommitmentConstruction)
  | ConsumerBody(OracleCommitmentConsumer)
  | PurposeBody(OracleCommitmentPurpose)
  | BindingPayloadBody(OracleCommitmentBindingPayload)
  | NoPolicyBody(OracleCommitmentNoPolicy)
  | PolicyClosureBody(OracleCommitmentPolicyClosure)
  | CapabilityRequirementBody(OracleCommitmentCapabilityRequirement)
  | RunReceiptBody(OracleCommitmentRunReceiptSemantic)
  | RunValidationBasisBody(OracleCommitmentRunValidationBasis)
```

Each variant tag and nested record field follows the written order.
`OracleCommitmentId<K>(x)` abbreviates
`ProfiledSemanticId<K>(B,PIROracleCommitmentProfileId,the body arm for x)` and
accepts exactly the arm assigned to `K`; an omitted arm, extra kind, alternate
compiler, or open-default dispatch is `Refused`.

<!-- zkc-profile-source:oracle-commitment-body-dispatch:end -->

An omitted required import or kind is `Refused`; an unrecognized exact profile
root is `Unsupported`; a formed reference to another regime or kind is
`KindMismatch`. No second import root, request-local catalog, or evaluator
extension participates in semantic identity.

<!-- zkc-profile-source:oracle-commitment-semantics:start -->

## 3. Exact commitment profile

### 3.1 Algorithm and type coordinates

```text
AlgorithmUse = PIRAlgorithmUse

SourcePublicCoordinate =
  {binding: BindingRef, class: Statement | SessionContext | PublicParameter}
TargetPublicCoordinate =
  {binding: BindingRef, class: Statement | SessionContext | PublicParameter}
SourceOraclePublicationRef = {
  oracle: OracleRef,
  publication: OccurrenceRef,
  origin: OracleOrigin // owner-derived from the exact source OracleDecl
}
SourceFreshRandomnessRef = {challenge: ChallengeRef}
SourceQueryOccurrenceRef = {oracle: OracleRef, query: OccurrenceRef}
SourceAnswerOccurrenceRef =
  {oracle: OracleRef, query: OccurrenceRef, answer: OccurrenceRef}
TargetCommitmentPublicationRef = {
  commitment_class_ordinal: Natural,
  occurrence: OccurrenceRef, output_ordinal: Natural
}
TargetFreshRandomnessRef = {challenge: ChallengeRef}
TargetQueryOccurrenceRef = {occurrence: OccurrenceRef}
SourcePreservedCoordinate =
    SourceCheck(CheckRef)
  | SourceClaimState(ClaimRef)
  | SourceReductionState(ReductionRef)
  | SourceTerminalMaterial(TerminalRef,input_ordinal)
  | SourceTerminalVerdict(TerminalRef)
  | SourcePublicOutput(TerminalRef,output_ordinal)

TargetPreservedCoordinate =
    TargetCheck(CheckRef)
  | TargetClaimState(ClaimRef)
  | TargetReductionState(ReductionRef)
  | TargetTerminalMaterial(TerminalRef,input_ordinal)
  | TargetTerminalVerdict(TerminalRef)
  | TargetPublicOutput(TerminalRef,output_ordinal)

OracleCommitmentSetupRoleBinding = {
  role_ordinal: Natural,
  source_public_parameter: SourcePublicCoordinate,
  target_public_parameter: TargetPublicCoordinate
}
TargetOpeningClaimCoordinate = {
  source_answer: SourceAnswerOccurrenceRef,
  commitment: TargetCommitmentPublicationRef,
  query_value: ValueRef,
  asserted_answer: ValueRef
}
TargetOpeningEvidenceSlot = {
  response_occurrence: OccurrenceRef,
  slot_ordinal: Natural,
  decoded_evidence: ValueRef
}
RuntimeLogicalOpeningClaimMaterial = {
  logical_coordinate: TargetOpeningClaimCoordinate,
  commitment_class_ordinal: Natural,
  verifier_profile_id: CommitmentOpeningVerifierProfileId,
  source_oracle: OracleRef,
  source_index: CanonicalValue<class.source_index_type>,
  public_commitment:
    CanonicalValue<verifier_profile.public_commitment_type>,
  opening_query: CanonicalValue<verifier_profile.query_type>,
  asserted_answer:
    CanonicalValue<verifier_profile.asserted_answer_type>
}
RuntimeOpeningResponseMaterial = {
  evidence_slot: TargetOpeningEvidenceSlot,
  commitment_class_ordinal: Natural,
  verifier_profile_id: CommitmentOpeningVerifierProfileId,
  verifier_use_id: CommitmentOpeningUseId,
  verifier_use_group_ordinal: Natural,
  setup_assignment:
    CanonicalValue<CommitmentSetupAssignmentType<verifier_profile>>,
  verification_context:
    CanonicalValue<CommitmentVerificationContextType<verifier_profile>>,
  decoded_claims:
    CanonicalSeq<OpeningClaimValue<verifier_profile>
                 in profile claim order>,
  opening_evidence:
    CanonicalValue<verifier_profile.opening_evidence_type>,
  claim_group_check: CheckRef,
  verification_check: CheckRef
}
RuntimeOpeningEvidenceCoverageInput = {
  logical_claim_material:
    CanonicalSeq<RuntimeLogicalOpeningClaimMaterial
                 sorted by logical_coordinate>,
  target_response_material:
    CanonicalSeq<RuntimeOpeningResponseMaterial>
    in target-record order
}
OpeningEvidenceClaimBinding = {
  logical_coordinate: TargetOpeningClaimCoordinate,
  claim_ordinal: Natural
}
OpeningEvidenceGroup = {
  evidence_slot: TargetOpeningEvidenceSlot,
  commitment_class_ordinal: Natural,
  verifier_profile_id: CommitmentOpeningVerifierProfileId,
  verifier_use_id: CommitmentOpeningUseId,
  verifier_use_group_ordinal: Natural,
  claim_group_check: CheckRef,
  verification_check: CheckRef,
  claim_bindings:
    CanonicalNonEmptySeq<OpeningEvidenceClaimBinding
                         sorted by logical_coordinate>
}
ConcreteOpeningEvidenceCoverage =
  CanonicalSeq<OpeningEvidenceGroup in target-record evidence-slot order>
  with every logical coordinate occurring exactly once, every selected
  evidence slot, claim-group check, and opening check occurring exactly once,
  and every profile claim ordinal covered at least once in its group
InsertedAuthenticationEffect =
    InsertedCommitment(TargetCommitmentPublicationRef)
  | InsertedOpeningResponse(OccurrenceRef)
  | InsertedResponseDecoding(ValueRef)
  | InsertedVerifierPacking(ValueRef)
  | InsertedClaimGroupCheck(CheckRef)
  | InsertedOpeningCheck(CheckRef)
  | InsertedPublicAdviceProjection(ValueRef)
TotalStaticMap<K,V> =
  CanonicalSeq<{source: K, target: V} sorted by the canonical K order>
  with unique source keys and key set equal to the complete derived K domain

OracleCommitmentStaticMapSchema = {
  public_source_schema: exactly SourcePublicCoordinate above,
  publication_source_tags: exactly SourceOraclePublicationRef,
  fresh_source_tags: exactly SourceFreshRandomnessRef,
  query_source_tags: exactly SourceQueryOccurrenceRef,
  answer_source_tags: exactly SourceAnswerOccurrenceRef,
  preserved_source_tags: exactly the SourcePreservedCoordinate alternatives,
  inserted_effect_tags: exactly the InsertedAuthenticationEffect alternatives,
  canonical_order: written tag order then owner occurrence order,
  logical_claim_key: TargetOpeningClaimCoordinate,
  opening_evidence_key: TargetOpeningEvidenceSlot
}

OracleCommitmentClass = {
  class_ordinal: Natural,
  source_oracle: OracleRef,
  source_origin: OracleOrigin,
  verifier_profile_id: CommitmentOpeningVerifierProfileId,
  target_verifier_use_id: CommitmentOpeningUseId,
  setup_role_bindings:
    CanonicalSeq<OracleCommitmentSetupRoleBinding in role order>,
  source_index_type: ValueType, source_element_type: ValueType,
  complete_material_type: ValueType, private_advice_type: ValueType,
  private_commitment_state_type: ValueType,
  opening_response_type: ValueType,
  encode_material: AlgorithmUse, build_commitment: AlgorithmUse,
  derive_public_commitment: AlgorithmUse, form_opening_query: AlgorithmUse,
  produce_opening_response: AlgorithmUse,
  decode_opening_response: AlgorithmUse
}
```

`RuntimeOpeningEvidenceCoverageInputType(profile)` and
`ConcreteOpeningEvidenceCoverageType(profile)` are the exact same-regime
Foundation lifts of the two dependent records above. The class ordinal selects
the value types; a mismatched ordinal or value type is `KindMismatch`.

All references above resolve in the exact admitted source or target Core. A
source coordinate, including its Oracle origin, is derived from the complete
source body, never selected by the author. Each commitment class's
`source_origin` must equal that derived origin. Its verifier profile and target
Core use are exact admitted same-regime subjects; the use names that profile
and the construction's target Core. Every setup role appears once, and its
source and target coordinates are `PublicParameter` bindings of the exact role
type, agree through the public-environment map, and equal the admitted use's
setup bindings. Every primitive target
coordinate is classified exactly once as a
direct image or an `inserted_target_effect`. Publication and logical-claim
map values may reference the corresponding inserted effects; that linkage is
not a second classification. Repeated logical answers remain distinct
`TargetOpeningClaimCoordinate`s. An asserted answer is a distinct public value,
never an extraction from evidence. A concrete evidence group or claim-to-group
coverage result is runtime material and is never a static-map entry.

Exact function ABIs and typed-failure rows are declaration-catalog data.
Admission derives and checks them against the selected source Oracle, exact
verifier profile and admitted target use, target occurrences, and value types.
The source element type equals the verifier profile's asserted-answer type,
and `form_opening_query` is the only adapter from the source index type to the
profile query type.
Every producer
algorithm that uses setup receives the exact packed setup assignment as an
explicit input. No algorithm may read ambient setup, registry state, runtime
limits, an undeclared Oracle, or advice outside its exact input.

Tree arity, cap shape, leaf grouping, salting, padding, multiproof layout,
root type, proof codec, and hash framing are profile fields expressed by the
types and algorithms above. PIR assigns none of those choices universally.

### 3.2 Advice schema

```text
AdviceRole = {
  role_ordinal: Natural, commitment_class_ordinal: Natural,
  value_type: ValueType, maximum_value_count: Natural,
  owner: ProverConstruction, lifetime: OneInvocation,
  public_projection: None | SelectedByOpening(AlgorithmUse)
}

ConstructionAdviceSchema = {
  roles: CanonicalSeq<AdviceRole>,
  public_projection_type: ValueType,
  formation_law: AlgorithmUse,
  public_projection_law: AlgorithmUse
}

AdviceValueSetType(schema) = the Foundation-lifted canonical record whose
field at role ordinal `r` is a sequence of `r.value_type` with maximum length
`r.maximum_value_count`

ConstructionAdviceSchemaId =
  OracleCommitmentId<"pir.oracle-commitment-advice-schema">(schema)
```

Every advice role is construction-owned and per invocation. Advice values,
random seeds, salts, unselected opening material, and private commitment state
do not enter the schema ID or construction ID. A deterministic fixture may
generate advice reproducibly, but that does not change its semantic ownership
or establish entropy, independence, hiding, or production suitability.

Only the exact projection selected by an opening response may become target
public material. Revealing all advice because some advice is disclosed
violates the schema.

### 3.3 Runtime opening-evidence coverage law

```text
OpeningEvidenceCoverageLaw = {
  derive: AlgorithmUse,
  logical_order: "canonical-target-opening-claim-coordinate-order",
  response_order: "target-record-evidence-slot-order",
  profile_local_grouping:
    "each group obeys its exact verifier profile and construction adapter",
  coverage:
    "all-logical-claims-and-exactly-all-selected-evidence-slots-and-checks"
}
```

The law is profile identity, but its result is not static construction data.
Admission authenticates the algorithm and contract, checks the exact dependent
ABI, and establishes from the two finite Core bodies that the logical-claim
domain, target response occurrences, response decoder, evidence-slot codec,
profile claim counts, verification checks, and intrinsic capacities are
closed. It does not evaluate a value-dependent grouping law or choose concrete
coverage.

For one run, the algorithm consumes every logical claim in canonical order
with the causal source Oracle, independently replay-checked source index and
answer, explicitly formed query, public commitment, and exact setup
assignment. It also consumes every target response in record order after the
class decoder has separated asserted-answer payloads from opening evidence.
It emits canonical evidence groups and claim-ordinal bindings. The checker
requires each group to name one exact verifier profile, setup assignment and
verification context,
admitted target Core use and use-group ordinal, evidence slot, and verification
checks; requires the use to attach that profile to the exact target Core with
the same setup, claim, context, evidence, check, and profile-local schedule;
requires its decoded claims in profile order to pass that profile's exact
claim-group law; and requires the target opening check to consume precisely the
packed setup, context, claims, and evidence selected by the group.

Every logical claim occurs exactly once in the coverage. Every selected
evidence slot, claim-group check, and opening check occurs exactly once, and
every decoded claim ordinal is covered. Several repeated logical coordinates
may cover one decoded claim ordinal only when the profile-local law and exact
decoded values permit it. A multiproof profile may instead cover distinct claims with one
evidence value. Missing, extra, duplicated, reordered, type-incompatible, or
uncovered material rejects, as does any response or group beyond the intrinsic
maximum. No universal equality key, batching algebra, or evidence-sharing rule
is implied.

The checker independently rederives this coverage during one-execution
validation. An authored table, a table cached by admission, the response
producer, or the algorithm's success bit has no authority. The former exact
equality-dedup behavior is one profile-local coverage algorithm, not this
owner's universal law.

### 3.4 Intrinsic bound law

```text
IntrinsicConstructionBounds = {
  maximum_source_oracles, maximum_source_publications,
  maximum_source_query_occurrences, maximum_source_answer_occurrences,
  maximum_target_occurrences, maximum_logical_opening_claims,
  maximum_opening_evidence_slots, maximum_opening_evidence_groups,
  maximum_opening_claim_coverage_entries, maximum_advice_values,
  maximum_public_commitment_bytes, maximum_opening_response_bytes,
  maximum_opening_evidence_bytes,
  maximum_algorithm_calls, maximum_elaboration_steps,
  maximum_static_map_entries, maximum_admission_check_steps,
  maximum_run_validation_steps,
  maximum_canonical_body_bytes: Natural
}

IntrinsicBoundLaw = {derive: AlgorithmUse,
                     declared_bounds: IntrinsicConstructionBounds}
```

The derivation input is only the authenticated source/target Core bodies,
commitment classes, exact verifier-profile closure, advice schema, static-map
schema, and opening-evidence coverage law. The derived result must equal
`declared_bounds`. Per-request
evaluator limits, actual proof size, runtime work, and observed resource use are
not identity fields.

`maximum_opening_evidence_slots` and
`maximum_opening_claim_coverage_entries` are static worst-case capacities.
They must cover every admitted logical claim without assuming runtime sharing,
must fit the target response and evidence codecs, and remain independent of a
smaller profile-local coverage result obtained for one run.

### 3.5 Profile identity

```text
OracleCommitmentProfile = {
  commitment_classes: CanonicalNonEmptySeq<OracleCommitmentClass>,
  advice_schema_id: ConstructionAdviceSchemaId,
  static_map_schema: OracleCommitmentStaticMapSchema,
  opening_evidence_coverage_law: OpeningEvidenceCoverageLaw,
  source_receipt_projection_type: ValueType, source_receipt_projection: AlgorithmUse,
  target_receipt_projection_type: ValueType, target_receipt_projection: AlgorithmUse,
  intrinsic_bound_law: IntrinsicBoundLaw
}

OracleCommitmentProfileId =
  OracleCommitmentId<"pir.oracle-commitment-profile">(profile)
```

The profile has no semantic display name or authored version. The selected
language profile, subject kind, and complete body already determine its
identity; external release metadata cannot distinguish otherwise identical
construction semantics. The profile carries no authored aggregate failure
catalog. For one exact profile or construction subject,
`ApplicableFailureCatalog(subject)` is the Foundation-canonical union of the
typed-failure rows of exactly the `AlgorithmUse` contracts reachable from that
subject's authenticated body and dependency closure. It is derived, not a
second identity-bearing field, and cannot contain an unused failure type.
Evaluation may return only a failure from the contract actually invoked.

Changing an algorithm, contract, source-Oracle origin, verifier-profile or
target-use reference, setup-role map, type, advice role, map schema, evidence-
coverage law, failure coordinate, or bound law rotates the profile ID. Runtime setup,
claim, response, evidence, coverage, advice, and limit values do not.

The two dependent portable types are not opaque aliases:

```text
ExactCorePairAndProfileShape = {
  source_core_id: CoreId, source_core_body: InteractiveCoreBody,
  target_core_id: CoreId, target_core_body: InteractiveCoreBody,
  commitment_profile_id: OracleCommitmentProfileId,
  commitment_profile_body: OracleCommitmentProfile,
  verifier_profile_closure:
    CanonicalKeySortedMap<CommitmentOpeningVerifierProfileId,
                          CommitmentOpeningVerifierProfile>,
  verifier_use_closure:
    CanonicalKeySortedMap<CommitmentOpeningUseId,
                          CommitmentOpeningUse>,
  advice_schema_id: ConstructionAdviceSchemaId,
  advice_schema_body: ConstructionAdviceSchema,
  static_map_schema: OracleCommitmentStaticMapSchema
}

ExactCorePairAndProfileShapeType =
  the exact same-regime ValueType for the recursively lifted record above
IntrinsicConstructionBoundsType =
  the exact same-regime ValueType for recursively lifted
  IntrinsicConstructionBounds
OracleCommitmentStaticElaborationType =
  the exact same-regime ValueType for recursively lifted
  OracleCommitmentStaticElaboration
```

The shape is derived from authenticated bodies and IDs and requires each
ID/body equation to hold. It contains no run, advice value, record, receipt,
request limit, or evaluator observation.

## 4. Construction subject

```text
StaticElaborationUse = {
  algorithm: PortableAlgorithmRef, evaluation_contract: EvaluationContractId,
  input_type: ExactCorePairAndProfileShapeType,
  output_type: OracleCommitmentStaticElaborationType
}

OracleCommitmentConstruction = {
  source_core_id: CoreId,
  target_core_id: CoreId,
  commitment_profile_id: OracleCommitmentProfileId,
  advice_schema_id: ConstructionAdviceSchemaId,
  elaboration: StaticElaborationUse,
  intrinsic_bound_law: IntrinsicBoundLaw
}

OracleCommitmentConstructionId =
  OracleCommitmentId<"pir.oracle-commitment-construction">(construction)
```

The body contains no Core carrier bytes beyond their IDs, authored static map,
runtime value, advice, record, receipt, evaluator, limit, or observed resource
count. Core authentication supplies their complete meaning.

Formation requires distinct source and target `CoreId`s. A same-Core subject
belongs to challenge interpretation or another same-Core construction, not
this construction.

## 5. Deterministic bounded static elaboration

Admission evaluates `construction.elaboration` over canonical shapes derived
from the exact authenticated subjects. Its result is:

```text
OracleCommitmentStaticElaboration = {
  public_environment_map: TotalStaticMap<SourcePublicCoordinate,
                                         TargetPublicCoordinate>,
  oracle_publication_map: TotalStaticMap<SourceOraclePublicationRef,
                                          TargetCommitmentPublicationRef>,
  fresh_randomness_map: TotalStaticMap<SourceFreshRandomnessRef,
                                       TargetFreshRandomnessRef>,
  query_vector_map: TotalStaticMap<SourceQueryOccurrenceRef,
                                   TargetQueryOccurrenceRef>,
  answer_claim_map:
    TotalStaticMap<SourceAnswerOccurrenceRef,TargetOpeningClaimCoordinate>,
  preserved_coordinate_map:
    TotalStaticMap<SourcePreservedCoordinate,TargetPreservedCoordinate>,
  inserted_target_effects: CanonicalSeq<InsertedAuthenticationEffect>,
  expected_target_core_body: InteractiveCoreBody,
  derived_bounds: IntrinsicConstructionBounds
}
```

`SourcePreservedCoordinate` covers source checks, claim/reduction state,
terminal material, verdict, and public output. Inserted effects cover target-
only commitments, opening responses, response decoding, advice projections,
claim-group checks, and opening checks.

The map laws are:

1. every applicable source coordinate appears exactly once;
2. every target semantic coordinate is either the exact image of one source
   coordinate or one declared inserted effect;
3. no source challenge or query choice is authored by the map;
4. source query order, labels, and multiplicity are preserved exactly;
5. the `answer_claim_map` codomain is the complete canonically ordered set of
   distinct logical opening-claim coordinates, including repeated logical
   answers;
6. every logical coordinate fixes its commitment class, exact verifier
   profile, public commitment, explicitly formed query, asserted-answer value,
   and exact dependent types, but fixes no evidence slot or concrete coverage;
7. every class setup-role map is total, names exact source and target
   `PublicParameter` bindings of the profile role type, and agrees with the
   `public_environment_map`;
8. the profile's evidence-coverage algorithm and law have the exact dependent
   ABI, and target response, evidence, group, check, and intrinsic bounds admit
   no more than their declared capacities;
9. every asserted answer has the source Oracle element type, is separate from
   opening evidence, and becomes usable only through the exact target response
   decoding and successful profile checks;
10. each preserved computation consumes mapped values in the same ordered
   semantic roles; and
11. no target occurrence, check, terminal input, or public output is left
   unexplained.

Runtime setup, query, answer, commitment, response, or evidence values are not
inputs to static elaboration. Consequently no concrete opening-evidence
coverage, profile-local sharing result, or response count appears in this
result. Section 9 derives those facts from the exact records under the
profile-owned coverage law.

The admitted conclusion is decided by one closed owner law, not by an authored
certificate or success bit:

```text
StaticElaborationCheckInput = {
  shape: ExactCorePairAndProfileShape,
  elaboration: OracleCommitmentStaticElaboration
}

StaticElaborationCheckReport =
    StaticElaborationAffirmative {
      checked_map_entries: Natural,
      checked_source_dependency_edges: Natural,
      checked_target_dependency_edges: Natural,
      checked_target_body_bytes: Natural,
      conclusion: ForwardStructurallyElaborates
    }
  | StaticElaborationNegative(OracleCommitmentConstructionDefectSet)

StaticAdmissionStepCount(shape,e) =
    number of source occurrences
  + number of target occurrences
  + number of source dependency edges
  + number of target dependency edges
  + total number of pairs in all source-keyed maps
  + length(e.inserted_target_effects)
  + byte_length(canonical(shape.target_core_body))
  + byte_length(canonical(e.expected_target_core_body))

CheckStaticElaborationV0(StaticElaborationCheckInput)
  -> StaticElaborationCheckReport
```

`CheckStaticElaborationV0` is the total algorithm fixed by this profile's
semantic-law source. In written order it independently derives every source
domain and target partition from `shape`, checks every map entry and the
complete logical-claim domain, authenticates every referenced verifier profile
and target Core use, checks each use's exact profile, target Core, setup,
claim/evidence/check wiring, and profile-local schedule, checks every setup-role
map and producer/decoder ABI, checks the evidence-
coverage algorithm ABI, target response/evidence codecs, profile claim counts,
and static capacities, checks causality and
dependency preservation, reconstructs the target body from the source plus
inserted effects, compares both canonical target bodies, derives intrinsic
bounds, and returns the complete canonical defect set. It must preflight
`StaticAdmissionStepCount <= maximum_admission_check_steps`, every map length
against `maximum_static_map_entries`, and both canonical bodies against
`maximum_canonical_body_bytes`. Exceeding the supplied evaluation limit is
`DeterministicLimitExceeded`; exceeding an intrinsic maximum is
`Negative(IntrinsicBoundMismatch)`.

The report contains independently derived counts only. A caller-supplied
report, proof object, Boolean, unchecked hash, or cached traversal grants
nothing. Because this law checks finite static structure only, it is total and
does not quantify over runtime executions or advice values.

The elaborator is a closed portable algorithm, not a callback, compiler pass,
proof generator, or authored success flag. Its worst case is preflighted before
allocating the output body.

## 6. Construction admission

```text
CheckOracleCommitmentConstruction(
  exact AdmittedCore source,
  exact AdmittedCore target,
  exact authenticated and admitted CommitmentOpeningVerifierProfile handle
    for every distinct profile.commitment_classes.verifier_profile_id,
  exact authenticated and admitted CommitmentOpeningUse handle
    for every distinct profile.commitment_classes.target_verifier_use_id,
  authenticated OracleCommitmentProfile profile and advice_schema,
  authenticated OracleCommitmentConstruction construction,
  exact PIR construction checker,
  exact typed consumer,
  exact typed purpose,
  PortableEvaluationLimitsV0 limits)
  -> Qualified<
       Affirmative({
         CheckedOracleCommitmentConstruction,
         ExactOracleCommitmentConstructionAuthorityBinding,
         CheckedOracleCommitmentConstructionCapability
       })
       | Negative(OracleCommitmentConstructionDefectSet)>
```

The checker proceeds in this order:

1. authenticate the interaction, commitment-opening, and Oracle-construction
   profile closures, every exact verifier profile and target Core use, all
   subjects, algorithms, contracts, types, catalogs, and exact Core handles;
2. require construction, profile, advice schema, source, and target IDs to
   agree exactly;
3. require every source Oracle named by a commitment class to have exact mode
   `LogicalAccess`, zero publication outputs, one typed fixation marker, an
   admitted exact-domain law, and an origin equal to the class's
   `source_origin`; both `InitialOracle` and `ProverOracle` are supported, and
   require an independently admitted concrete target;
4. derive exact elaboration and bounds and require canonical completion;
5. evaluate `CheckStaticElaborationV0` over the exact derived shape and
   elaboration, independently of any caller report;
6. check totality, target classification, types, order, labels, multiplicity,
   and the complete logical-claim domain for every static map;
7. require each derived source publication coordinate--including its exact
   origin--to map to a target commitment publication before every dependent
   mapped Fresh coin, without treating the logical fixation marker as a
   commitment or publication value;
8. require all mapped query randomness to remain Fresh randomness owned by
   the Core rather than a transcript byte seed;
9. require each class to name one exact admitted verifier profile and exact
   admitted use of that profile on the target Core; require every coverage
   group to name an in-range group of that use and exactly its setup, context,
   claim, evidence, checks, and profile-local schedule; require its
   setup-role map to exhaust that profile's roles through matching source and
   target `PublicParameter` coordinates; require every producer algorithm to
   receive the exact packed setup assignment; require every mapped logical
   claim to name an earlier commitment, exact query value, and distinct
   asserted-answer value; require response decoding to separate claim payloads
   from evidence; require exact profile claim-group and opening-check wiring,
   the profile-owned evidence-coverage algorithm and law, target response and
   evidence codecs, and intrinsic capacities, but derive no concrete coverage;
10. require mapped fold, scalar or other terminal material, checks, claims,
   reductions, terminal verdict, and public outputs to be structurally
   preserved;
11. require the reconstructed `expected_target_core_body` to equal the exact
    admitted target Core body byte for byte;
12. require every target accepting sink to close over target public inputs,
    public history, Fresh coins, decoded asserted answers, exact claim-group
    checks, and proof-supplied opening evidence;
13. require no complete source Oracle, source-carrier digest, private advice,
    private commitment state, or owner-only generation carrier to reach target
    public replay, a static map, or a portable construction identity;
14. require the static check report to be affirmative with all counts equal to
    independently recomputed counts; and
15. require all sums, step counts, and bodies to fit Foundation, Core, profile,
    and construction bounds.

Admission establishes typed algorithm wiring, a complete static logical-claim
map, exact setup-role wiring, and an exact canonical runtime evidence-coverage
law with intrinsic maximum bounds, exact target reconstruction, and public-
replay shape. It establishes no concrete claim-to-evidence coverage. It does
not execute the construction
over every source run, prove extensional equality of portable programs, or
establish a universal source/target behavioral theorem. Section 9 is the only
operation here that derives and checks runtime setup assignments, decoded
responses, opening-evidence coverage, algorithm outputs, and terminal
agreement, and it does so for one exact source/target execution
pair. Neither operation gives an arbitrary target proof a unique source or an
extractor.

## 7. Closed defects and outcomes

```text
OracleCommitmentConstructionDefect =
    SourceCoreIdentityMismatch | TargetCoreIdentityMismatch
  | CommitmentProfileMismatch | VerifierProfileMismatch | VerifierUseMismatch
  | AdviceSchemaMismatch | ElaborationContractMismatch
  | SourceLogicalModeMismatch | SourceOracleOriginMismatch
  | LogicalSourcePublicationOutputMismatch
  | PublicEnvironmentMapIncomplete | SetupRoleMapMismatch
  | ProducerSetupInputMismatch | OraclePublicationMapIncomplete
  | FreshRandomnessMapMismatch | QueryVectorMapIncomplete | AnswerClaimMapIncomplete
  | PreservedCoordinateMapIncomplete | TargetCoordinateUnclassified | CoordinateTypeMismatch
  | CausalityViolation | LogicalMultiplicityLost
  | ResponseDecoderMismatch | AssertedAnswerEvidenceConflation
  | ClaimGroupWiringMismatch | OpeningEvidenceCoverageLawMismatch
  | OpeningEvidenceCapacityMismatch
  | OpeningAuthenticationMismatch | AdviceOwnershipMismatch | ConfidentialAdviceLeak
  | PublicReplayClosureFailure | ExactTargetBodyMismatch | StaticCheckMismatch
  | TerminalPreservationFailure
  | IntrinsicBoundMismatch

OracleCommitmentConstructionDefectSet =
  CanonicalNonEmptySortedUniqueSeq<
    OracleCommitmentConstructionDefect in written tag order>
```

Before a defect is defined, malformed carriers are `Malformed`, a formed wrong
kind/regime/ABI is `KindMismatch`, an unrecognized exact profile or algorithm
is `Unsupported`, and missing authority is `MissingDependency`.

A formed authenticated candidate that fails a closed predicate returns
`Negative(defect_set)`. Insufficient limits give `DeterministicLimitExceeded`;
provider, ABI, evaluator, or checker inconsistency gives `CheckerFailure`.
Neither returns partial output or authority.

## 8. Checked result and live authority

The construction checker uses one closed capability family and owner-profiled
authority bodies:

```text
OracleCommitmentAuthorityFamily =
  "checked-oracle-commitment-construction"

OracleCommitmentDownstreamCoordinate =
  one exact same-regime SemanticContentId<K> for any exact kind K

OracleCommitmentConsumer = {
  family: OracleCommitmentAuthorityFamily,
  downstream_coordinate: OracleCommitmentDownstreamCoordinate
}
OracleCommitmentPurpose = {
  family: OracleCommitmentAuthorityFamily,
  downstream_coordinate: OracleCommitmentDownstreamCoordinate
}

OracleCommitmentConsumerId =
  OracleCommitmentId<"pir.oracle-commitment-consumer">(consumer)
OracleCommitmentPurposeId =
  OracleCommitmentId<"pir.oracle-commitment-purpose">(purpose)

OracleCommitmentBindingPayload = {
  owner_domain: "pir",
  family: OracleCommitmentAuthorityFamily,
  source_core_id: CoreId, target_core_id: CoreId,
  commitment_profile_id: OracleCommitmentProfileId,
  advice_schema_id: ConstructionAdviceSchemaId,
  construction_id: OracleCommitmentConstructionId,
  result_schema: "ForwardStructurallyElaborates-v1",
  consumer_id: OracleCommitmentConsumerId,
  purpose_id: OracleCommitmentPurposeId
}

OracleCommitmentNoPolicy = {
  family: OracleCommitmentAuthorityFamily,
  payload_id: OracleCommitmentBindingPayloadId,
  disposition: "owner-defines-no-additional-operation-policy"
}

OracleCommitmentCapabilityRequirement = {
  family: OracleCommitmentAuthorityFamily,
  payload_id: OracleCommitmentBindingPayloadId,
  consumer_id: OracleCommitmentConsumerId,
  purpose_id: OracleCommitmentPurposeId,
  bearer_law: "fresh-identical-bearer-capability"
}

OracleCommitmentPolicyClosure = {
  family: OracleCommitmentAuthorityFamily,
  payload_id: OracleCommitmentBindingPayloadId,
  no_policy_id: OracleCommitmentNoPolicyId,
  requirement_id: OracleCommitmentCapabilityRequirementId
}

OracleCommitmentBindingPayloadId =
  OracleCommitmentId<"pir.oracle-commitment-binding-payload">(payload)
OracleCommitmentNoPolicyId =
  OracleCommitmentId<"pir.oracle-commitment-no-policy">(no_policy)
OracleCommitmentCapabilityRequirementId =
  OracleCommitmentId<"pir.oracle-commitment-capability-requirement">(requirement)
OracleCommitmentPolicyClosureId =
  OracleCommitmentId<"pir.oracle-commitment-policy-closure">(closure)
```

Formation requires identical family, payload, consumer, and purpose references
throughout these bodies. The downstream coordinate remains typed by its owner;
PIR wraps but does not reinterpret it. Swapped roles, a different construction,
an extra policy, a reconstructed bearer, or a wrong-regime coordinate refuses.

`CheckedOracleCommitmentConstructionResultRef` is a collision-free opaque
process-local coordinate allocated for one affirmative occurrence.
`ExactOracleCommitmentConstructionAuthorityBinding` is exactly a Foundation
`OwnerLocalSourceAuthorityBinding` whose owner is `"pir"`, family is
`OracleCommitmentAuthorityFamily`, local coordinate is that result ref, payload
is the exact binding-payload ID above, policy is the exact no-policy
disposition, closure is the exact derived closure ID, and requirement is the
matching Foundation wrapper. It has no canonical body or semantic ID.

```text
CheckedOracleCommitmentConstruction = {
  source_core_id: CoreId, target_core_id: CoreId,
  commitment_profile_id: OracleCommitmentProfileId,
  advice_schema_id: ConstructionAdviceSchemaId,
  construction_id: OracleCommitmentConstructionId,
  exact_static_elaboration: OracleCommitmentStaticElaboration,
  conclusion: ForwardStructurallyElaborates
}
```

The checked result has no semantic ID. Each affirmative checking occurrence
creates:

- one collision-free owner-local
  `CheckedOracleCommitmentConstructionResultRef`;
- one exact Foundation `OwnerLocalSourceAuthorityBinding`; and
- one fresh opaque `CheckedOracleCommitmentConstructionCapability`.

The binding owner is `"pir"`, its family is
`"checked-oracle-commitment-construction"`, and its local coordinate is the
result ref. Its exact `OracleCommitmentBindingPayloadId`,
`OwnerDefinesNoPolicy(OracleCommitmentNoPolicyId)`, policy-closure ID, and
Foundation `OwnerCapabilityRequirement("pir",family,requirement_id)` bind both
Cores, profile, advice schema, construction, result schema, consumer, and
purpose. The binding contains no live token, evaluator, request limit, or
observed result.

The capability retains the live admitted Core, verifier-profile, verifier-use,
Oracle-profile, advice-schema, and construction handles, result, binding,
checker/evaluator, consumer, purpose, occurrence, and evaluation control. It is
process-local, noncopyable, nonserializable, noncacheable, non-FFI-safe, and
exact-purpose. Equal data, an inert ref or receipt, stale authority, or another
consumer or purpose grants nothing.

Cold use readmits every subject and reruns the check; serialization never
transports the capability.

## 9. One-execution validation and inert receipt

Construction admission and execution validation are different operations:

```text
ValidateOracleCommitmentRun(
  exact checked result and authority binding,
  matching fresh CheckedOracleCommitmentConstructionCapability,
  exact source CoreInvocation and CompletedProtocolRecord,
  identical live source CausalGenerationCapability,
  exact target CoreInvocation and CompletedProtocolRecord,
  exact source and target PublicSetupInvocationView values and matching fresh
    capabilities,
  exact owner-local ConstructionAdvice values,
  exact source replay capabilities,
  exact target replay capabilities,
  source ExecutionEvaluationControl,
  target ExecutionEvaluationControl,
  construction ExecutionEvaluationControl)
    -> Qualified<Affirmative(OracleCommitmentRunReceipt)
                 | Negative(OracleCommitmentRunDefectSet)>
```

The source causal capability must be the one minted with the identical source
Protocol, invocation, completed record, and immutable Oracle handles. For an
`InitialOracle` it retains the exact prepared input handle; for a
`ProverOracle` it retains the exact handle admitted from that run's strategy
move. A source replay capability is still required to check every recorded
query and answer, but its candidate carrier cannot select or replace this
causal carrier.

Source replay, target replay, and construction-law evaluation proceed under
three separate evaluators, limits, and resource accounts. Validation derives
each class's exact source and target setup assignments from the two authorized
public-setup views, requires the role maps and values to agree, and supplies
the source assignment explicitly to material encoding, commitment formation,
public-commitment derivation, and opening-response production. It derives each
response group's exact verification context from the admitted target use and
record and supplies that context explicitly to response production. It obtains the
complete runtime logical claim material from the exact causal source handles,
verifies the source record against those handles, forms every query, decodes
the exact target responses into distinct asserted-answer and evidence values,
and independently invokes and rechecks the profile-owned canonical evidence-
coverage law.
Only then does it check every map coordinate, coverage group and binding,
profile claim-group and opening check, response-production result, advice
projection, preserved computation, terminal, and exact record exhaustion. A
target-provided selector table, producer-authored coverage, or decoder success
bit is evidence to compare, never the derivation authority.
The semantic-law source counts one validation step for each canonical source
record entry, target record entry, checked static-map coordinate, checked
logical claim, decoded response and evidence slot, evidence group, coverage
binding, setup-role value, and completed profile-algorithm call. Validation
preflights that exact sum against
`maximum_run_validation_steps`; exceeding it is an intrinsic-bound defect,
while insufficient evaluator limits produce `DeterministicLimitExceeded`.

```text
RunResourceBasis = {
  evaluation_contract_closure: CanonicalSortedUniqueSet<EvaluationContractId>,
  supplied_limits: PortableEvaluationLimitsV0,
  completed_resource_vector: PortableEvaluationChargeV0
}

OracleCommitmentRunReceiptSemantic = {
  construction_id: OracleCommitmentConstructionId,
  source_core_id: CoreId, target_core_id: CoreId,
  source_invocation_id: CoreInvocationId, target_invocation_id: CoreInvocationId,
  source_record_projection: CanonicalValue<profile.source_receipt_projection_type>,
  target_record_projection: CanonicalValue<profile.target_receipt_projection_type>,
  checked_logical_opening_claim_coordinates:
    CanonicalSeq<TargetOpeningClaimCoordinate>,
  concrete_opening_evidence_coverage:
    ConcreteOpeningEvidenceCoverage,
  public_advice_projection:
    CanonicalValue<advice_schema.public_projection_type>,
  conclusion: ThisExecutionForwardMapped
}

OracleCommitmentRunReceiptId =
  OracleCommitmentId<"pir.oracle-commitment-run-receipt">(semantic_receipt)

OracleCommitmentRunValidationBasis = {
  receipt_id: OracleCommitmentRunReceiptId,
  validation_operation: "ValidateOracleCommitmentRun-v1",
  source_resource_basis: RunResourceBasis,
  target_resource_basis: RunResourceBasis,
  construction_resource_basis: RunResourceBasis
}

OracleCommitmentRunValidationBasisId =
  OracleCommitmentId<"pir.oracle-commitment-run-validation-basis">(
    validation_basis)

OracleCommitmentRunReceipt = {
  semantic_receipt: OracleCommitmentRunReceiptSemantic,
  semantic_receipt_id: OracleCommitmentRunReceiptId,
  validation_basis: OracleCommitmentRunValidationBasis,
  validation_basis_id: OracleCommitmentRunValidationBasisId
}
```

The aggregate serializable receipt is inert and has no third ID. Its semantic
receipt ID commits to the exact construction, invocations, typed record
projections, checked logical coordinates, their run-derived concrete opening-
evidence coverage, public advice projection, and one-execution conclusion.
Supplied limits, completed charges, evaluator capacity, wall time, and host
observations
are validation/evidence basis only; they are excluded from the semantic receipt
body and from every construction identity. Changing only those fields preserves
`OracleCommitmentRunReceiptId` and rotates
`OracleCommitmentRunValidationBasisId`.

Run validation requires both ID/body equations, derives all three resource
bases from the independently completed evaluations, and rejects a validation
basis naming another receipt. Admission checks the record-projection,
response-decoding, setup-packing, and evidence-coverage algorithms and types;
run validation derives their values from the two live invocations and completed
records and requires the coverage domain to equal the admitted logical-claim
domain. It also requires every evidence slot, group, claim ordinal, and
coverage entry to fit the intrinsic maxima. The projections and coverage
neither serialize nor replace Core-owned runtime records.
Visibility follows the projections; private advice and state are excluded.

```text
OracleCommitmentRunDefect =
    ConstructionAuthorityMismatch | SourceCausalAuthorityMismatch
  | SourceReplayMismatch
  | TargetReplayMismatch | RuntimeSetupMismatch | RuntimeAdviceMismatch
  | LogicalOpeningClaimRunMismatch | OpeningResponseDecodeMismatch
  | AssertedAnswerRunMismatch | OpeningEvidenceCoverageMismatch
  | ClaimGroupRunMismatch | AuthenticationRunMismatch
  | PreservedComputationRunMismatch | TerminalRunMismatch
  | ResourceBasisMismatch

OracleCommitmentRunDefectSet =
  CanonicalNonEmptySortedUniqueSeq<
    OracleCommitmentRunDefect in written tag order>
```

A receipt validates one run only. It cannot replace live authority, authorize
another run, replace construction admission, reverse-extract, or strengthen
security. Cold verification can reauthenticate the receipt and replay its
public record projections, but cannot reconstruct the original causal source
carrier or mint this one-run conclusion. A new affirmative run receipt requires
a new matching live causal source execution.

## 10. Public replay closure

The committed target is public-replay closed only when accepted execution is
reconstructed from the exact public invocation and public-setup view, ordered
public commitments, Fresh challenge values or a separate admitted same-Core
Fiat--Shamir reconstruction, public queries, decoded asserted answers, opening
evidence, profile claim-group and opening checks, and the concrete evidence
coverage independently rederived from those public values under the profile
law, together with exact target checker capabilities.

Public target replay excludes complete source Oracles, source replay witnesses,
source causal capabilities, confidential initial-Oracle views, private advice
and state, unselected salts, owner inputs, goldens, and prior receipts.

This structural result proves no concrete conformance, binding, hiding,
collision resistance, or proof-system soundness.

<!-- zkc-profile-source:oracle-commitment-semantics:end -->

## 11. Worked-profile witness

The bounded
[`evaluation/native-fri-ior/`](../../evaluation/native-fri-ior/README.md)
instrument exercises a Goldilocks-field, order-64 FRI profile with one initial and two
later logical Oracles, three publications mapped to three single Merkle roots,
three Fresh fold challenges, a scalar terminal before query randomness, four
labelled draws, twelve logical layer-answer/opening-claim coordinates, and
profile-local canonical equality coverage into a smaller response/evidence
table. Each decoded response keeps its asserted leaf answer distinct from its
Merkle evidence. Static admission fixes all twelve logical coordinates, the
exact Merkle verifier profile, response decoder, coverage algorithm and law,
and maximum table sizes; one-run validation derives the actual smaller
evidence coverage from the run values.

Those cardinalities test totality, causal order, scalar-terminal preservation,
logical multiplicity, and profile-local evidence sharing. They are not PIR
grammar constants.
A cap, forest, vector commitment, unsalted tree, different leaf grouping,
different query count, or different finite Core requires another exact profile
and construction identity.

That instrument is finite inhabitance and falsification evidence. It does not
implement this durable checker or capability lifecycle and cannot substitute
for an admitted construction or one-run causal validation.

<!-- zkc-profile-source:oracle-commitment-nonclaims:start -->

## 12. Nonclaims

Neither admission nor a receipt proves commitment binding, hiding,
extractability, collision resistance, source existence or uniqueness behind an
arbitrary target proof, or reverse extraction. It proves no FRI proximity,
completeness, soundness, knowledge, round-by-round soundness, restoration, or
rewinding premise; no literal BCS correspondence or theorem preservation; and
no Fiat--Shamir ROM/QROM or grinding result. It also proves no outer relation,
implementation conformance, side-channel isolation, production safety, OIR or
backend realization, deployment, evidence grade, or family-wide support.

Analysis owns the exact property question, theorem source, assumptions,
applicability, loss, and property transport. Relations owns source/target
relation grounding and any outer-relation conclusion. Evidence owns observed
implementation and replay claims.

<!-- zkc-profile-source:oracle-commitment-nonclaims:end -->

## 13. Reversal conditions

Reopen the source/target construction boundary if executable pressure shows
any of the following after an exact profile has been attempted:

1. public target replay necessarily requires a confidential complete source
   Oracle even when all exact asserted answers and opening evidence are present;
2. no total typed static map can preserve every labelled logical answer, or no
   canonical bounded per-run law can derive complete logical-claim-to-evidence
   coverage from exact replayed values under exact verifier profiles;
3. the exact finite construction requires runtime creation of an occurrence,
   answer-dependent routing, an opaque callback, or Core rewind;
4. public setup cannot be supplied explicitly through preserved
   `PublicParameter` bindings, or commitment advice cannot remain construction-
   owned and per invocation without changing the source logical-Oracle relation;
5. the target cannot be independently admitted or cannot be reconstructed
   exactly from source, profile, maps, and inserted authentication effects;
6. Fresh execution of the committed target and Fiat--Shamir execution require
   different target Core semantics rather than different challenge
   interpretations;
7. a terminal scalar or other preserved terminal can be represented only by
   inventing an Oracle publication, root, or vacuous acceptance check; or
8. profile-wide checking can be expressed only by elevating one-run receipts,
   runtime advice, host implementation behavior, or evaluator conclusions to
   semantic authority.

Conditions 1, 3, 5, and 6 reopen the factorization; 2 and 7 first reopen map or
terminal vocabulary; 4 and 8 reopen authority. Migration cost is not reversal evidence.
