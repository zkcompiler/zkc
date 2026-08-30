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
static elaboration and logical maps, a canonical per-run physical-opening
binding law, admission and outcomes, process-local authority, inert run
receipts, advice, public replay, bounds, nonclaims, and reversal conditions.

The [Interactive Core](interactive-core.md) owns both Cores, their Oracle
effects, causal execution, public-coin eligibility, and replay. The
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
bounded runtime binding law are checked as one structural subject. It does not
assert that every runtime source execution
has been generated, that every advice value is sound, or that every resulting
target execution agrees. That stronger statement is deliberately absent;
Section 9 validates one exact execution pair at a time. Profile-wide does not
mean every FRI, IOP, IOR, commitment scheme, tree shape, query schedule, or
target implementation.

## 2. Foundation and profile intake

For one exact Foundation `PriorMetaAuthenticationBasis B`, this owner consumes:

- exact `AdmittedCore` handles for source and target;
- `PIRInteractionProfileId` and its authenticated import closure;
- authenticated `PortableAlgorithmRef` and `EvaluationContractId` pairs;
- exact `ValueType`, `CanonicalValue`, and canonical finite collections; and
- Foundation outcome and deterministic-evaluation mechanisms.

All objects use the same semantic regime and authenticated basis. The profile
imports exactly `PIRInteractionProfileId` and redefines no PIR meaning.

```text
PIROracleCommitmentProfile = SemanticLanguageProfile {
  profile_family: "pir.oracle-commitment",
  revision: 1,
  profile_imports: {PIRInteractionProfileId},
  supported_subject_kinds: {
    "pir.oracle-commitment-profile", "pir.oracle-commitment-construction",
    "pir.oracle-commitment-advice-schema", "pir.oracle-commitment-consumer",
    "pir.oracle-commitment-purpose", "pir.oracle-commitment-binding-payload",
    "pir.oracle-commitment-no-policy",
    "pir.oracle-commitment-policy-closure",
    "pir.oracle-commitment-capability-requirement",
    "pir.oracle-commitment-run-receipt",
    "pir.oracle-commitment-run-validation-basis"
  },
  declaration_catalogs: OracleCommitmentDeclarationCatalog,
  semantic_law_source: exact nonempty bytes for this page
}

PIROracleCommitmentProfileId =
  SemanticContentId<"foundation.semantic-language-profile">(
    B, SemanticLanguageProfileBody(PIROracleCommitmentProfile))
```

The declaration catalog and body compiler are closed. Algorithm declarations
are indexed by the following sum; class-indexed alternatives occur exactly
once per commitment class and the remaining alternatives occur exactly once:

```text
OracleCommitmentAlgorithmRole =
    EncodeMaterial(class_ordinal)
  | BuildCommitment(class_ordinal)
  | DerivePublicCommitment(class_ordinal)
  | FormOpeningRequest(class_ordinal)
  | Open(class_ordinal)
  | VerifyOpening(class_ordinal)
  | ExtractAnswers(class_ordinal)
  | CheckAdviceFormation | ProjectPublicAdvice
  | DerivePhysicalOpeningBindings | DeriveIntrinsicBounds
  | ElaborateStaticTarget | ProjectSourceReceipt | ProjectTargetReceipt

OracleCommitmentAlgorithmDeclaration = {
  role: OracleCommitmentAlgorithmRole,
  input_types: CanonicalSeq<ValueType>,
  output_type: ValueType,
  totality: TotalDeterministicBounded,
  typed_failure_row: CanonicalSortedUniqueSet<TypedFailureCoordinate>
}

OracleCommitmentDeclarationCatalog =
  CanonicalKeySortedMap<OracleCommitmentAlgorithmRole,
                        OracleCommitmentAlgorithmDeclaration>
  with exactly the domain above
```

For class `c`, the seven class-indexed ABIs are, in role order:

```text
[OracleCarrierType(c.source_oracle)] -> c.complete_material_type
[c.complete_material_type,c.private_advice_type]
  -> c.private_commitment_state_type
[c.private_commitment_state_type] -> c.public_commitment_type
[c.source_index_type] -> c.opening_request_type
[c.private_commitment_state_type,c.opening_request_type,c.private_advice_type]
  -> c.public_opening_type
[c.public_commitment_type,c.opening_request_type,c.public_opening_type]
  -> RootBool
[c.public_opening_type] -> c.opened_answer_type
```

The profile fields below fix the remaining seven ABIs: advice formation is
`[AdviceValueSetType(schema)] -> RootBool`; public projection is
`[AdviceValueSetType(schema),CanonicalSeq<TargetPhysicalOpeningSlot>]
-> schema.public_projection_type`; physical-opening binding derivation is
`[RuntimeOpeningBindingInputType(profile)]
-> ConcretePhysicalOpeningBindingsType(profile)`; bound derivation
uses `ExactCorePairAndProfileShapeType -> IntrinsicConstructionBoundsType`;
static elaboration uses
`ExactCorePairAndProfileShapeType -> OracleCommitmentStaticElaborationType`;
and each receipt projection uses the exact Core completed-record public-view
type selected by that field. The catalog's typed-failure rows must equal the
applicable coordinates in `profile.exact_failure_catalog`; a host exception or
unlisted failure cannot be treated as a declared semantic result.

The exact owner body compiler has one arm for every advertised kind and no
default arm:

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

An omitted required import or kind is `Refused`; an unrecognized exact profile
root is `Unsupported`; a formed reference to another regime or kind is
`KindMismatch`. No second import root, request-local catalog, or evaluator
extension participates in semantic identity.

## 3. Exact commitment profile

### 3.1 Algorithm and type coordinates

```text
AlgorithmUse = {algorithm: PortableAlgorithmRef,
                evaluation_contract: EvaluationContractId}

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

TargetLogicalOpeningCoordinate = {
  source_answer: SourceAnswerOccurrenceRef,
  commitment: TargetCommitmentPublicationRef,
  request_occurrence: OccurrenceRef,
  opening_occurrence: OccurrenceRef,
  verification_check: CheckRef, extracted_value: ValueRef
}
TargetPhysicalOpeningSlot =
  {opening_occurrence: OccurrenceRef, slot_ordinal: Natural}
RuntimeLogicalOpeningMaterial = {
  logical_coordinate: TargetLogicalOpeningCoordinate,
  commitment_class_ordinal: Natural,
  source_oracle: OracleRef,
  source_index: CanonicalValue<class.source_index_type>,
  opened_value: CanonicalValue<class.source_element_type>,
  public_commitment: CanonicalValue<class.public_commitment_type>
}
RuntimePhysicalOpeningMaterial = {
  physical_slot: TargetPhysicalOpeningSlot,
  commitment_class_ordinal: Natural,
  source_oracle: OracleRef,
  source_index: CanonicalValue<class.source_index_type>,
  opened_value: CanonicalValue<class.source_element_type>,
  public_commitment: CanonicalValue<class.public_commitment_type>
}
RuntimeOpeningBindingInput = {
  logical_material:
    CanonicalSeq<RuntimeLogicalOpeningMaterial
                 sorted by logical_coordinate>,
  target_physical_material:
    CanonicalSeq<RuntimePhysicalOpeningMaterial>
    in target-record order
}
ConcretePhysicalOpeningBinding = {
  logical_coordinate: TargetLogicalOpeningCoordinate,
  physical_slot: TargetPhysicalOpeningSlot
}
ConcretePhysicalOpeningBindings =
  CanonicalSeq<ConcretePhysicalOpeningBinding sorted by logical_coordinate>
  with unique logical coordinates and domain exactly equal to the admitted
  answer-opening map codomain
InsertedAuthenticationEffect =
    InsertedCommitment(TargetCommitmentPublicationRef)
  | InsertedOpeningRequest(OccurrenceRef)
  | InsertedPublicOpening(OccurrenceRef)
  | InsertedOpeningCheck(CheckRef)
  | InsertedAnswerExtraction(ValueRef)
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
  logical_opening_key: TargetLogicalOpeningCoordinate
}

OracleCommitmentClass = {
  class_ordinal: Natural,
  source_oracle: OracleRef,
  source_origin: OracleOrigin,
  source_index_type: ValueType, source_element_type: ValueType,
  complete_material_type: ValueType, private_advice_type: ValueType,
  private_commitment_state_type: ValueType, public_commitment_type: ValueType,
  opening_request_type: ValueType, public_opening_type: ValueType,
  opened_answer_type: ValueType,
  encode_material: AlgorithmUse, build_commitment: AlgorithmUse,
  derive_public_commitment: AlgorithmUse, form_opening_request: AlgorithmUse,
  open: AlgorithmUse, verify_opening: AlgorithmUse,
  extract_answers: AlgorithmUse
}
```

`RuntimeOpeningBindingInputType(profile)` and
`ConcretePhysicalOpeningBindingsType(profile)` are the exact same-regime
Foundation lifts of the two dependent records above. The class ordinal selects
the value types; a mismatched ordinal or value type is `KindMismatch`.

All references above resolve in the exact admitted source or target Core. A
source coordinate, including its Oracle origin, is derived from the complete
source body, never selected by the author. Each commitment class's
`source_origin` must equal that derived origin. Every primitive target
coordinate is classified exactly once as a
direct image or an `inserted_target_effect`. Publication and logical-opening
map values may reference the corresponding inserted effects; that linkage is
not a second classification. Repeated logical answers remain distinct
`TargetLogicalOpeningCoordinate`s. A concrete physical slot or a concrete
logical-to-physical binding is runtime material and is never a static-map
entry.

Exact function ABIs and typed-failure rows are declaration-catalog data.
Admission derives and checks them against the selected source Oracle, target
occurrences, and value types. No algorithm may read ambient state, runtime
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

Only the exact projection selected by a public opening may become target
public material. Revealing all advice because some advice is opened violates
the schema.

### 3.3 Runtime physical-opening binding law

```text
PhysicalOpeningBindingLaw = {
  derive: AlgorithmUse,
  logical_order: "canonical-target-logical-opening-coordinate-order",
  equivalence_key:
    "commitment-class,source-oracle,index,value,public-commitment",
  allocation: "distinct-first-occurrence-keys-match-target-record-slot-order",
  coverage: "all-logical-coordinates-and-exactly-all-selected-physical-slots"
}
```

The law is profile identity, but its result is not static construction data.
Admission authenticates the algorithm and contract, checks the exact dependent
ABI, and establishes from the two finite Core bodies that the logical domain,
target opening occurrences, slot codec, and intrinsic maximum slot count are
closed. It does not evaluate a value-dependent equivalence class or choose a
physical slot.

For one run, the algorithm consumes every logical coordinate in canonical
order with the causal source Oracle, independently replay-checked index and
value, and public commitment, plus the exact physical material decoded from
the target record. It forms the
distinct logical equivalence keys in first-occurrence order and requires that
sequence to equal the physical-material key sequence in target-record order.
Every logical coordinate is then bound to the unique slot for its key. It
rejects unequal keys sharing a slot, equal keys occupying different slots, an
uncovered selected slot, a missing or extra logical coordinate, reordered
input, duplicate physical keys, or any slot beyond
`maximum_physical_opening_slots`. Thus deduplication is deterministic and
canonical without pretending that runtime equality is a static fact.

The checker independently rederives this table during one-execution validation.
An authored table, a table cached by admission, or the algorithm's success bit
has no authority.

### 3.4 Intrinsic bound law

```text
IntrinsicConstructionBounds = {
  maximum_source_oracles, maximum_source_publications,
  maximum_source_query_occurrences, maximum_source_answer_occurrences,
  maximum_target_occurrences, maximum_logical_opening_coordinates,
  maximum_physical_opening_slots, maximum_advice_values,
  maximum_public_commitment_bytes, maximum_public_opening_bytes,
  maximum_algorithm_calls, maximum_elaboration_steps,
  maximum_static_map_entries, maximum_admission_check_steps,
  maximum_run_validation_steps,
  maximum_canonical_body_bytes: Natural
}

IntrinsicBoundLaw = {derive: AlgorithmUse,
                     declared_bounds: IntrinsicConstructionBounds}
```

The derivation input is only the authenticated source/target Core bodies,
commitment classes, advice schema, static-map schema, and physical-opening
binding law. The derived result must equal `declared_bounds`. Per-request
evaluator limits, actual proof size, runtime work, and observed resource use are
not identity fields.

`maximum_physical_opening_slots` is the static worst-case capacity: it must
cover the case in which every logical opening has a distinct equivalence key,
must not exceed the target opening codec's finite capacity, and is independent
of the smaller slot count that a particular run may obtain by deduplication.

### 3.5 Profile identity

```text
OracleCommitmentProfile = {
  profile_name: BoundedSymbol,
  profile_version: PositiveNatural,
  commitment_classes: CanonicalNonEmptySeq<OracleCommitmentClass>,
  advice_schema_id: ConstructionAdviceSchemaId,
  static_map_schema: OracleCommitmentStaticMapSchema,
  physical_opening_binding_law: PhysicalOpeningBindingLaw,
  source_receipt_projection_type: ValueType, source_receipt_projection: AlgorithmUse,
  target_receipt_projection_type: ValueType, target_receipt_projection: AlgorithmUse,
  intrinsic_bound_law: IntrinsicBoundLaw,
  exact_failure_catalog: CanonicalSortedUniqueSet<TypedFailureCoordinate>
}

OracleCommitmentProfileId =
  OracleCommitmentId<"pir.oracle-commitment-profile">(profile)
```

Changing an algorithm, contract, source-Oracle origin, type, advice role, map
schema, binding law, failure coordinate, or bound law rotates the profile ID.
Runtime material and limits do not.

The two dependent portable types are not opaque aliases:

```text
ExactCorePairAndProfileShape = {
  source_core_id: CoreId, source_core_body: InteractiveCoreBody,
  target_core_id: CoreId, target_core_body: InteractiveCoreBody,
  commitment_profile_id: OracleCommitmentProfileId,
  commitment_profile_body: OracleCommitmentProfile,
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
  answer_opening_map:
    TotalStaticMap<SourceAnswerOccurrenceRef,TargetLogicalOpeningCoordinate>,
  preserved_coordinate_map:
    TotalStaticMap<SourcePreservedCoordinate,TargetPreservedCoordinate>,
  inserted_target_effects: CanonicalSeq<InsertedAuthenticationEffect>,
  expected_target_core_body: InteractiveCoreBody,
  derived_bounds: IntrinsicConstructionBounds
}
```

`SourcePreservedCoordinate` covers source checks, claim/reduction state,
terminal material, verdict, and public output. Inserted effects cover target-
only commitments, openings, advice projections, extraction, and authentication.

The map laws are:

1. every applicable source coordinate appears exactly once;
2. every target semantic coordinate is either the exact image of one source
   coordinate or one declared inserted effect;
3. no source challenge or query choice is authored by the map;
4. source query order, labels, and multiplicity are preserved exactly;
5. the `answer_opening_map` codomain is the complete canonically ordered set of
   distinct logical opening coordinates, including repeated logical answers;
6. every logical coordinate fixes its commitment class, target opening
   occurrence, authentication check, extraction, and exact dependent types,
   but fixes no physical slot;
7. the profile's physical-binding algorithm and law have the exact dependent
   ABI, and the target opening codec and intrinsic bounds admit no more than
   `maximum_physical_opening_slots` runtime slots;
8. every extracted answer has the source Oracle index and element type;
9. each preserved computation consumes mapped values in the same ordered
   semantic roles; and
10. no target occurrence, check, terminal input, or public output is left
   unexplained.

Runtime equality of indices, values, or commitments is not an input to static
elaboration. Consequently no concrete physical-opening projection, sharing
class, or slot count appears in this result. Section 9 derives those facts from
the exact records under the profile-owned binding law.

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
complete logical-opening domain, checks the binding algorithm ABI, canonical
deduplication law, target codec, and static slot capacity, checks causality and
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

1. authenticate the profile closure, subjects, algorithms, contracts, types,
   catalog, and exact Core handles;
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
   and complete logical-opening coverage for every static map;
7. require each derived source publication coordinate--including its exact
   origin--to map to a target commitment publication before every dependent
   mapped Fresh coin, without treating the logical fixation marker as a
   commitment or publication value;
8. require all mapped query randomness to remain Fresh randomness owned by
   the Core rather than a transcript byte seed;
9. require each logical opening to name an exact target check wired to its
   earlier commitment, request, and public opening, with extraction usable only
   after that check and only declared public advice exposed; require the
   profile-owned physical-binding algorithm, canonical deduplication law,
   target slot codec, and intrinsic maximum, but derive no concrete binding;
10. require mapped fold, scalar or other terminal material, checks, claims,
   reductions, terminal verdict, and public outputs to be structurally
   preserved;
11. require the reconstructed `expected_target_core_body` to equal the exact
    admitted target Core body byte for byte;
12. require every target accepting sink to close over target public inputs,
    public history, Fresh coins, and proof-supplied public openings;
13. require no complete source Oracle, source-carrier digest, private advice,
    private commitment state, or owner-only generation carrier to reach target
    public replay, a static map, or a portable construction identity;
14. require the static check report to be affirmative with all counts equal to
    independently recomputed counts; and
15. require all sums, step counts, and bodies to fit Foundation, Core, profile,
    and construction bounds.

Admission establishes typed algorithm wiring, a complete static logical
coordinate map, an exact canonical runtime-binding law with intrinsic maximum
bounds, exact target reconstruction, and public-replay shape. It establishes
no concrete logical-to-physical binding. It does not execute the construction
over every source run, prove extensional equality of portable programs, or
establish a universal source/target behavioral theorem. Section 9 is the only
operation here that derives and checks physical bindings, algorithm outputs,
and terminal agreement, and it does so for one exact source/target execution
pair. Neither operation gives an arbitrary target proof a unique source or an
extractor.

## 7. Closed defects and outcomes

```text
OracleCommitmentConstructionDefect =
    SourceCoreIdentityMismatch | TargetCoreIdentityMismatch
  | CommitmentProfileMismatch | AdviceSchemaMismatch | ElaborationContractMismatch
  | SourceLogicalModeMismatch | SourceOracleOriginMismatch
  | LogicalSourcePublicationOutputMismatch
  | PublicEnvironmentMapIncomplete | OraclePublicationMapIncomplete
  | FreshRandomnessMapMismatch | QueryVectorMapIncomplete | AnswerOpeningMapIncomplete
  | PreservedCoordinateMapIncomplete | TargetCoordinateUnclassified | CoordinateTypeMismatch
  | CausalityViolation | LogicalMultiplicityLost
  | PhysicalOpeningBindingLawMismatch | PhysicalOpeningCapacityMismatch
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

The capability retains the live admitted handles, result, binding,
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
three separate evaluators, limits, and resource accounts. Validation obtains
the complete runtime logical opening material from the exact causal source
handles, verifies the source record against those handles, decodes the exact
target physical material, and independently invokes and rechecks the
profile-owned canonical binding law.
Only then does it check every map coordinate, concrete binding, opening,
advice projection, preserved computation, terminal, and exact record
exhaustion. A target-provided selector table or producer-authored binding is
evidence to compare, never the derivation authority.
The semantic-law source counts one validation step for each canonical source
record entry, target record entry, checked static-map coordinate, checked
logical opening, decoded physical slot, concrete binding, and completed
profile-algorithm call. Validation preflights that exact sum against
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
  checked_logical_opening_coordinates:
    CanonicalSeq<TargetLogicalOpeningCoordinate>,
  concrete_physical_opening_bindings:
    ConcretePhysicalOpeningBindings,
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
projections, checked logical coordinates, their run-derived concrete physical
bindings, public advice projection, and one-execution conclusion. Supplied
limits, completed charges, evaluator capacity, wall time, and host observations
are validation/evidence basis only; they are excluded from the semantic receipt
body and from every construction identity. Changing only those fields preserves
`OracleCommitmentRunReceiptId` and rotates
`OracleCommitmentRunValidationBasisId`.

Run validation requires both ID/body equations, derives all three resource
bases from the independently completed evaluations, and rejects a validation
basis naming another receipt. Admission checks the record-projection and
physical-binding algorithms and types; run validation derives their values
from the two live completed records and requires the binding domain to equal
the admitted logical-opening domain. It also requires the distinct physical
slot count and every slot ordinal to fit the intrinsic maximum. The projections
and bindings neither serialize nor replace Core-owned runtime records.
Visibility follows the projections; private advice and state are excluded.

```text
OracleCommitmentRunDefect =
    ConstructionAuthorityMismatch | SourceCausalAuthorityMismatch
  | SourceReplayMismatch
  | TargetReplayMismatch | RuntimeAdviceMismatch
  | LogicalOpeningRunMismatch | PhysicalOpeningBindingMismatch
  | PhysicalOpeningCoverageMismatch | AuthenticationRunMismatch
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
reconstructed from the exact public invocation, ordered public commitments,
Fresh challenge values or a separate admitted same-Core Fiat--Shamir
reconstruction, public queries and proof openings, the concrete binding table
independently rederived from those public values under the profile law, and
exact target checker capabilities.

Public target replay excludes complete source Oracles, source replay witnesses,
source causal capabilities, confidential initial-Oracle views, private advice
and state, unselected salts, owner inputs, goldens, and prior receipts.

This structural result proves no concrete conformance, binding, hiding,
collision resistance, or proof-system soundness.

## 11. Worked-profile witness

The bounded
[`evaluation/native-fri-ior/`](../../evaluation/native-fri-ior/README.md)
instrument exercises a Goldilocks-field, order-64 FRI profile with one initial and two
later logical Oracles, three publications mapped to three single Merkle roots,
three Fresh fold challenges, a scalar terminal before query randomness, four
labelled draws, twelve logical layer-answer/opening coordinates, and
profile-local canonical runtime deduplication into a smaller physical opening
table. Static admission fixes all twelve logical coordinates, the deduplication
algorithm and law, and the maximum table size; one-run validation derives the
actual smaller table from the run values.

Those cardinalities test totality, causal order, scalar-terminal preservation,
logical multiplicity, and physical sharing. They are not PIR grammar constants.
A cap, forest, vector commitment, unsalted tree, different leaf grouping,
different query count, or different finite Core requires another exact profile
and construction identity.

That instrument is finite inhabitance and falsification evidence. It does not
implement this durable checker or capability lifecycle and cannot substitute
for an admitted construction or one-run causal validation.

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

## 13. Reversal conditions

Reopen the source/target construction boundary if executable pressure shows
any of the following after an exact profile has been attempted:

1. public target replay necessarily requires a confidential complete source
   Oracle even when all exact openings are present;
2. no total typed static map can preserve every labelled logical answer, or no
   canonical bounded per-run law can derive complete physical opening sharing
   from exact replayed values;
3. the exact finite construction requires runtime creation of an occurrence,
   answer-dependent routing, an opaque callback, or Core rewind;
4. commitment advice cannot remain construction-owned and per invocation
   without changing the source logical-Oracle relation;
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
