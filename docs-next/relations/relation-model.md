# Relation model

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-B target
> **Provisional owner:** `relations`
> **Authority:** This page specifies the selected `docs-next/` Relations
> model. It is not normative until explicit consolidation and cutover. The
> current specification under [`docs/`](../../docs/README.md) remains
> authoritative.
>
> **Dependency state:** This page is reconstructed against
> [Executable Semantic Foundations](../foundation/executable-foundations.md)
> and [Interactive Core and Causal Execution](../pir/interactive-core.md).
> The companion [Protocol Correspondence](protocol-correspondence.md) page owns
> checked questions over this algebra. It imports these exact subjects and may
> neither redefine them nor create a second PIR source vocabulary.

## 1. Purpose and boundary

Relations describes an independently meaningful predicate boundary and its
checked correspondence to an exact Protocol. It keeps five statements
separate:

1. a relation definition and Interface are well formed;
2. a public relation instance is well formed;
3. one confidential witness occurrence satisfies that instance under one
   exact semantic model;
4. relation occurrences correspond structurally or at one run to exact
   Protocol or Plan occurrences; and
5. a relation transform preserves satisfaction in one declared direction.

None implies another. In particular, Interface admission does not establish
definition truth, a Protocol binding does not establish satisfaction, an
accepting Protocol run does not establish relation satisfaction, and a
structural K2 reduction does not establish a proof-theoretic reduction.

The model has no universal proof-system ontology and no generic Protocol
object. It uses exact typed K1 values and the typed K2 coordinates already
owned by PIR. Extension occurs through semantic-module declarations and
separately checked relations, not through untyped labels or ambient
registries.

## 2. Reused foundations and common rules

### 2.1 K1 identity, language profile, and values

Relations selects one standalone K1 language profile. It is an ordinary
same-regime semantic subject, not an ambient registry entry or a declaration
inside a relation module. The following display fixes the profile owner and
symbolic target fields; the catalog and law-source phrases are obligations,
not a published complete six-field preimage:

~~~text
RelationsProfile = {
  profile_family: "zkc.relations.correspondence",
  revision: 0,
  profile_imports: {PIRInterfacePlanProfileId},
  supported_subject_kinds: RelationsSemanticSubjectKindCatalogV0,
  declaration_catalogs: [],
  semantic_law_source: the exact Relations v0 law source, including
    RelationsDeclarationContractKindCatalogV0 and its Section 2.4 body dispatch
}

RelationsProfileId =
  SemanticLanguageProfileId(B, RelationsProfile)

RelationsId<K>(B, b: MetaValueV0) =
  ProfiledSemanticId<K>(B, RelationsProfileId, b)
~~~

`RelationsSemanticSubjectKindCatalogV0` is the following exact canonical
sorted-unique sequence. It is the complete semantic-subject namespace selected
by this target; prose mentions and executable fixtures cannot add entries to
it:

~~~text
RelationsSemanticSubjectKindCatalogV0 = [
  "relations.artifact-comparison-question",
  "relations.artifact-observation",
  "relations.artifact-profile",
  "relations.artifact-profile-count-question",
  "relations.commitment-grounding",
  "relations.correspondence-question",
  "relations.definition",
  "relations.definition-model-question",
  "relations.grounding-equation",
  "relations.instance",
  "relations.interface",
  "relations.plan-witness-binding",
  "relations.protocol-binding",
  "relations.refinement-question",
  "relations.semantic-model",
  "relations.source-binding-payload",
  "relations.source-capability-requirement",
  "relations.source-consumer",
  "relations.source-no-policy",
  "relations.source-policy-closure",
  "relations.source-purpose",
  "relations.transform",
  "relations.value-bridge"
]
~~~

The six `relations.source-*` entries are ordinary Relations-profiled semantic
subjects. Their exact bodies and formation laws are owned by
[Protocol Correspondence, Section 4.3](protocol-correspondence.md#43-exact-relations-source-authority-subjects).
They are not module declarations, live capabilities, receipts, or a second
authority carrier. A kind absent from this sequence is unsupported as a
Relations semantic subject; it cannot be admitted through a declaration
catalog or an open-default body compiler.

Relations selects no profile-local declarations: all 14 extensible contracts
are module-owned `ModuleDeclarationRef` grammar and therefore belong to the
Relations semantic law, not to Foundation's `ProfileDeclarationCatalog`
field. This page must still publish the complete owner-local
`SemanticLanguageProfileBody`, including the exact semantic-law-source bytes,
together with its independently reconstructible full typed
`RelationsProfileId`. The bounded executable fixture's deterministic
profile object tests the selected topology, authentication, and rotation laws;
it is evidence and does not own Relations meaning. Publication is required
before any dependent K4 ID is treated as persistent and before K5 freeze.

The imported profile edge is exact and no-extra. It authenticates the
Interface/Plan vocabulary that Relations coordinates may cite; it does not
import a concrete Interface, Plan, or Protocol subject and does not grant
their authority. Changing the exact Interface/Plan language law rotates this
profile and its subjects. Changing an unrelated profile does not. An evaluator
supports this exact `RelationsProfileId`, never merely its family name or
revision, and authenticates the complete profile-import preimage closure
before admitting a Relations subject.

Every domain body contains only canonical K1 values, references, sequences,
maps, and variants. K1 places `RelationsProfileId` beside that body in the
outer `ProfiledSemanticBody`; the body definitions below do not repeat it. A
subject that directly cites a module-owned type, algorithm,
declaration, or other extensible meaning additionally contains:

- `used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>`;
- the exact `DeclarationRef<K>` for every directly cited extensible meaning;
  and
- the exact `ValueType` for every directly declared value position.

For such a subject, `used_modules` equals the exact direct owner-module set
derived from its body, and the K1 module-preimage bundle is the least import
closure of that set. The pure proposition/question bodies
`DefinitionModelCorrespondenceQuestion`, `RelationRefinementQuestion`, and
`ArtifactProfileCountQuestion` contain only nested semantic IDs and therefore
have no direct `used_modules` field. Their direct module set is empty at that
layer;
formation authenticates the nested IDs, and checking consumes the referenced
admitted subjects whose own bodies retain their exact module closures. A nested
closure is never copied into the question and never becomes a hidden direct
dependency. A missing, extra, cross-regime, unauthenticated, unsupported, or
ambiguously resolved direct or referenced declaration refuses admission. There
is no authored totality claim, ABI placeholder, dependency closure, or
semantic-regime alias.

All value equality in this page is K1 equality at the same exact `ValueType`.
Equal carrier bytes, equal digests, or equal mathematical values under
different types are not equality. Cross-regime preservation is a separate
future checked translation and never transfers source authority; K3-B returns
`Unsupported` for it as fixed in Section 2.4.

### 2.2 References and occurrences

An outward relation reference is always scoped by the exact subject that owns
its ordinal:

~~~text
RelationRef<S, R> = {
  owner_id: RelationsId<S>,
  role: R,
  canonical_ordinal: Natural
}
~~~

The owning body's ordered role sequence determines the ordinal. A diagnostic
name is outside identity. Distinct references remain distinct even when their
types and values are equal.

Runtime secret material uses fresh owner-local occurrence references instead
of content IDs. Equal secret bodies may have distinct occurrences; an
occurrence is never deduplicated by value.

~~~text
OwnerLocalOccurrence<T> = {
  fresh UnlinkableLocalRef,
  exact owner-and-process-generation-local single-valued association to T
}
~~~

The reference and association are created atomically and have no durable
encoding. `SecretValueCapability<T>` below is an opaque holder-issued live
capability whose read yields one exact canonical value of `T`; it likewise has
no semantic ID or body encoding.

### 2.3 Outcomes and authority

Relations operations use the project qualified-outcome split:

~~~text
Completed(Affirmative | Negative(exact disagreements, retained agreements))
Unsupported(exact unsupported meaning)
MissingDependency(exact named durable preimage absent after its coordinate forms)
CannotAnswer(exact supported formed operation lacks a required semantic
             premise, live read, or authority)
KindMismatch(exact formed coordinate has the wrong namespace, kind, regime,
             arity, or ABI)
Refused(exact authority or policy failure)
Malformed(exact structural or framing defect)
DeterministicLimitExceeded(exact exhausted K1 or owner-driver limit)
CheckerFailure(exact operational failure; no semantic conclusion)
~~~

Only a completed affirmative or negative may create the operation's exact
fresh process-local checked capability. Stored IDs and result records are
inert. They locate preimages but grant no authority. Export through a Foundation
`PortableSourceAuthorityBinding` or `OwnerLocalSourceAuthorityBinding` is a
separate owner decision and forms only when an exact Relations source family,
payload, manifest, policy closure, and requirement have been published. The
five currently selected source families are closed in the companion
[source-authority section](protocol-correspondence.md#43-exact-relations-source-authority-subjects);
none is a generic checked-result family. Missing support, missing secret
material, an unread fact, an unavailable evaluator, or an execution limit is
never negative truth.

The partition follows Foundation's shared meanings. An absent exact named
profile, module, subject, declaration, or algorithm preimage after its typed
coordinate forms is `MissingDependency`. A formed supported operation whose
authenticated semantic inputs exist but whose exact premise, live value read,
or live bearer cannot be obtained is `CannotAnswer`. Neither may be folded into
the other, and a wrong typed coordinate is `KindMismatch` rather than either
absence class. Each operation below fixes its own payload and precedence.

This page relies on the generic owner admission, purpose-bound view,
checked-result, and replay lifecycle defined by K1, with Project supplying only
the cross-domain completeness discipline. It specializes operands and laws
below rather than restating the Foundation envelope for every subject.

### 2.4 Closed declaration-contract catalog

The string in a `ModuleDeclarationRef<"relations.*">` is not an open plugin
name. Relations recognizes exactly the following version-`0` bodies and no
others. `DT` below is one exact module-local `DeclarationValueType`; admission
lifts it through its authenticated owner module to the outward `ValueType`.
`PA` is an exact same-regime `PortableAlgorithmRef`. `Assumptions` is a sorted
unique sequence of `relations.model-assumption` references. Every algorithm
ABI below has the written input order, the written success type, and an empty
typed-failure row unless the result is explicitly a tagged ordinary value.
`Lift(DT)` denotes the unique outward K1 `ValueType` obtained by resolving that
declaration-local type through its exact admitted owner module; it is a
derived function, not a caller-supplied cast.

The declaration-kind namespace is this second exact canonical sorted-unique
sequence:

~~~text
RelationsDeclarationContractKindCatalogV0 = [
  "relations.artifact-fact",
  "relations.artifact-format",
  "relations.artifact-interpreter",
  "relations.commitment-construction",
  "relations.definition-language",
  "relations.definition-model-law",
  "relations.loss-export",
  "relations.loss-source-premise",
  "relations.model-assumption",
  "relations.oracle-access-law",
  "relations.private-transform-contract",
  "relations.refinement-law",
  "relations.satisfaction-evaluator",
  "relations.value-bridge-law"
]

set(RelationsSemanticSubjectKindCatalogV0)
  intersect set(RelationsDeclarationContractKindCatalogV0) = {}
~~~

The disjointness equation is an admission invariant, not documentation
advice. A declaration kind is resolved only at an authenticated module
ordinal and has no `RelationsId<K>` body grammar. A semantic-subject kind is
formed only under `RelationsProfileId` and cannot be supplied as a module
declaration. Moving a name between these catalogs changes Relations language
meaning and therefore requires a profile/law revision; a consumer cannot
reinterpret one namespace as the other. This 14-kind sequence and the dispatch
below are committed through `semantic_law_source`; they are not entries in the
profile's empty `declaration_catalogs` field.

~~~text
DefinitionLanguageContractV0 = {
  version: 0,
  payload_type: DT,
  model_program_type: DT
}

OracleAccessLawContractV0 = {
  version: 0,
  public_binding_type: DT,
  material_type: DT,
  index_type: DT,
  answer_type: DT,
  bind: PA,                         // material -> public_binding
  lookup: PA                        // (material,index) -> answer
}

ModelAssumptionContractV0 = {
  version: 0,
  evidence_type: DT,
  predicate: PA                     // evidence -> Bool
}

DefinitionModelLawContractV0 = {
  version: 0,
  proposition_type: DT,
  certificate_type: DT,
  assumptions: Assumptions,
  verifier: PA                      // (proposition,certificate,evidence-record)
                                    //   -> Bool
}

SatisfactionEvaluatorContractV0 = {
  version: 0,
  language: ModuleDeclarationRef<"relations.definition-language">,
  public_input_types: CanonicalSeq<DT>,
  oracle_ports: CanonicalSeq<{
    public_binding_type: DT,
    index_type: DT,
    answer_type: DT
  }>,
  phase_input_types: CanonicalSeq<DT>,
  private_witness_types: CanonicalSeq<DT>,
  machine_state_type: DT,
  model_program: CanonicalValue<ModelProgramType(language)>,
  start: PA,
  resume: CanonicalSeq<PA>
}

PrivateTransformContractV0 = {
  version: 0,
  input_private_types: NonEmptyCanonicalSeq<DT>,
  parameter_types: CanonicalSeq<DT>,
  output_private_types: NonEmptyCanonicalSeq<DT>,
  derive: PA                         // (input-private-record,parameters)
                                     //   -> output-private-record
}

RefinementLawContractV0 = {
  version: 0,
  proposition_type: DT,
  certificate_type: DT,
  assumptions: Assumptions,
  verifier: PA                       // (proposition,certificate,evidence-record)
                                     //   -> Bool
}

ValueBridgeLawContractV0 = {
  version: 0,
  proposition_type: DT,
  certificate_type: DT,
  assumptions: Assumptions,
  verifier: PA                       // (proposition,certificate,evidence-record)
                                     //   -> Bool
}

LossSourcePremiseContractV0 = {
  version: 0,
  premise_input_type: DT,
  source_anchor_type: DT,
  anchor: PA,                         // premise-input -> source-anchor
  predicate: PA                      // premise-input -> Bool
}

LossExportContractV0 = {
  version: 0,
  exported_fact_type: DT,
  export: PA
    // RelationsCheckedLossyUseFactTypeV0(B) -> Lift(exported_fact_type)
}

ArtifactFactContractV0 = {
  version: 0,
  fact_class: StructuralMetaFact | SemanticValueFact,
  value_type: DT
}

ArtifactFormatContractV0 = {
  version: 0,
  artifact_bytes_type: DT
}

ArtifactInterpreterContractV0 = {
  version: 0,
  format: ModuleDeclarationRef<"relations.artifact-format">,
  fields: CanonicalSeq<{
    fact: ModuleDeclarationRef<"relations.artifact-fact">,
    value_type: DT,
    max_count: Natural
  }>,
  interpreter: PA
    // artifact-bytes -> ArtifactInterpreterCompletionType(fields)
}

CommitmentConstructionContractV0 = {
  version: 0,
  material_types: NonEmptyCanonicalSeq<DT>,
  commitment_type: DT,
  construct: PA                     // material-record -> commitment
}
~~~

For an admitted satisfaction-evaluator contract `C`, Relations derives the
following exact K1 types. `RoleRecordType` preserves the written role order;
an empty role sequence yields the empty root record. Command tag `0` is
`Decide`. Command tag `1 + o` is the query for Oracle ordinal `o`, so a
zero-Oracle contract has only the `Decide` alternative and an empty `resume`
sequence.

~~~text
RoleRecordType([T0,...,Tn-1]) =
  RootRecord<[(0,Lift(T0)),...,(n-1,Lift(Tn-1))]>

SatisfactionMachineInputType(C) = RootRecord<[
  (0, ModelProgramType(C.language)),
  (1, PayloadType(C.language)),
  (2, RoleRecordType(C.public_input_types)),
  (3, RoleRecordType(map(C.oracle_ports, public_binding_type))),
  (4, RoleRecordType(C.phase_input_types)),
  (5, RoleRecordType(C.private_witness_types))
]>

SatisfactionMachineCommandType(C) = RootVariant<[
  (0, RootBool),
  (1 + o, RootRecord<[
    (0, Lift(C.machine_state_type)),
    (1, Lift(C.oracle_ports[o].index_type))
  ]>) for each Oracle ordinal o in written order
]>

SatisfactionMachineResumeInputType(C,o) = RootRecord<[
  (0, Lift(C.machine_state_type)),
  (1, Lift(C.oracle_ports[o].answer_type))
]>
~~~

The declaration's `start` algorithm has exact ABI
`SatisfactionMachineInputType(C) -> SatisfactionMachineCommandType(C)`.
`resume` has exactly one entry per Oracle ordinal, and entry `o` has exact ABI
`SatisfactionMachineResumeInputType(C,o) ->
SatisfactionMachineCommandType(C)`. Every algorithm is same-regime, total,
and has the K1-derived empty semantic-failure row. These algorithms define the
evaluator denotation; no callback or implementation-supplied Boolean does.

~~~text
ArtifactRejectionReasonType = RootSymbol[256]

RelationsStructuralFactTypeV0(B) = RootBytes[0,2^20] in B
RelationsCheckedLossyUseFactTypeV0(B) = RootBytes[0,2^20] in B

ArtifactFieldObservationType(field) = RootVariant<[
  (0, RootUnit),
  (1, RootSeq<Lift(field.value_type), field.max_count>)
]>

ArtifactInterpreterCompletionType(fields) = RootVariant<[
  (0, RootRecord<[
    (field_ordinal, ArtifactFieldObservationType(field))
      for every field in written order
  ]>),
  (1, ArtifactRejectionReasonType)
]>
~~~

`ArtifactInterpreterCompletionType(fields)`, every proposition type, and every
evidence-record type above are closed K1 record or variant types derived by
Relations from the resolved declaration body. `AssumptionRef(law)` ranges over
the exact ordered `assumptions` in that law body and `EvidenceType(a)` is lifted
from its admitted assumption contract. None is a provider-selected alias. An
interpreter completion is exactly
`Interpreted(TotalMap<field ordinal, Unread | Observed(value sequence)>) |
RejectedBytes(reason)`; `RejectedBytes` is operational interpretation
noncompletion and never semantic Negative.

An admitted `relations.artifact-fact` declaration whose class is
`StructuralMetaFact` must lift its `value_type` to exactly
`RelationsStructuralFactTypeV0(B)`. A `SemanticValueFact` may declare any
admitted same-regime K1 value type. Thus a raw `MetaValueV0` is never treated as
a canonical fact value without an exact K1 carrier.

An admitted `relations.loss-source-premise` anchor has the exact ABI
`Lift(premise_input_type) -> Lift(source_anchor_type)` and its predicate has
the exact ABI `Lift(premise_input_type) -> RootBool`. An admitted
`relations.loss-export` algorithm has the exact ABI
`RelationsCheckedLossyUseFactTypeV0(B) -> Lift(exported_fact_type)`. The
checked-use input carrier and its canonical encoding are Relations-owned; a
module cannot replace either with an opaque fact type or alternate encoder.

For `definition-model-law`, `refinement-law`, and `value-bridge-law`, the lifted
`proposition_type` must equal the exact owner
`RelationsPropositionTypeV0(B)` defined in Section 13. No module may substitute
an opaque proposition carrier.

`AdmitRelationsDeclaration(ref, module_bundle)` authenticates the module and
ordinal, strictly decodes exactly the body selected by this table, requires
`version = 0`, lifts every `DT`, resolves every nested declaration, derives and
checks every algorithm/verifier ABI and empty failure row, derives the exact
direct module set and checks every member against the authenticated owner
module/import closure, and issues
an owner-local admitted-declaration capability. A malformed known-kind body is
`Malformed`; wrong owner/kind/regime is `KindMismatch`; a well-formed same-kind
version or exact contract not implemented by the selected evaluator is
`Unsupported`; a failed closed typing or compatibility predicate is `Refused`.
No consumer may derive `PayloadType`, `ModelProgramType`, `CertificateType`,
assumption evidence type, selector result type, or construction ABI without
this admitted result.

K3-B supports only same-regime declarations, values, and portable algorithms.
Any `CrossRegimeTranslation` request is `Unsupported`; it cannot appear in an
admitted Relations body, equation, recipe, or bridge. Cross-regime meaning, if
added later, requires a separately versioned owner contract and does not
inherit any K3-B law result.

## 3. Relation definitions, Interfaces, and instances

### 3.1 Definition

One relation definition is a K1 semantic value under an admitted relation
language declaration:

~~~text
RelationDefinition = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  language: ModuleDeclarationRef<"relations.definition-language">,
  payload: CanonicalValue<PayloadType(language)>
}

RelationDefinitionId =
  RelationsId<"relations.definition">(B, RelationDefinitionBody)

DefinitionPayloadType(d) =
  PayloadType(AdmittedRelationDefinition(d).language)
~~~

The admitted language contract derives `PayloadType(language)` and
`ModelProgramType(language)`. The payload must have exactly the first type.
The contract fixes the payload language and the model-program language; the
separate semantic-model contract below fixes one evaluator meaning.
The declaration module is in `used_modules`. A large external definition may
use a language-owned authenticated content-root value, but the root has no
meaning without the language's exact byte-authentication and interpretation
contract.

An importer may produce a `RelationDefinition` candidate and a checked
source-to-definition correspondence. Import success alone establishes neither
the source predicate nor that correspondence. External IDs are never silently
rehoused as K1 IDs.

#### 3.1.1 Exact definition-field owner view

Consumers do not copy fixed setup out of a definition payload or replace it
with an equal caller-authored record. Relations exposes definition leaves by
the same owner-coordinate pattern used by the K2 PIR static views:

~~~text
RelationDefinitionViewCoordinate = {
  definition_id: RelationDefinitionId,
  semantic_language_profile_id: RelationsProfileId
}

RelationDefinitionFieldCoordinate = {
  view_coordinate: RelationDefinitionViewCoordinate,
  selector: TypedValueSelector
}

RelationDefinitionReadManifest =
  CanonicalNonEmptySortedUniqueSeq<RelationDefinitionFieldCoordinate>

RelationDefinitionView = {
  coordinate: RelationDefinitionViewCoordinate,
  manifest: RelationDefinitionReadManifest,
  entries: CanonicalMap<RelationDefinitionFieldCoordinate,
                        exact selected definition-payload leaf>
}
~~~

Every selector forms only when it selects one atomic leaf of the admitted
definition payload with its exact derived type. Every manifest coordinate has
the same `definition_id` and `RelationsProfileId`; the returned entries equal
every and only the requested coordinates in canonical order. Missing,
duplicate, reordered, interior, wrong-definition, or wrong-profile coordinates
do not form an affirmative view.

Definition-view failure classification has this precedence. A malformed
coordinate or manifest carrier is `Malformed`. A structurally formed
coordinate in the wrong namespace, subject kind, or semantic regime is
`KindMismatch`. A formed same-kind definition or Relations-profile coordinate
that differs from the admitted source is an authenticated-owner substitution
and is `Refused`. Duplicate, reordered, interior, or extra selectors are
`Malformed` after coordinate formation. A wrong-kind coordinate therefore
does not fall through to an absent-source result, and a same-kind substitution
is not mislabeled as a framing defect.

~~~text
IssueRelationDefinitionView(
  exact admitted RelationDefinition,
  exact RelationDefinitionReadManifest,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> CorrespondenceOwnerViewIssueOutcome<RelationDefinitionView>
~~~

`IssueRelationDefinitionView` authenticates and admits the exact definition,
derives the leaves from that owner object, and returns a K1
`OwnerLocalSourceAuthorityBinding` plus a fresh identical-bearer capability
bound to the exact consumer and purpose. The binding must satisfy the companion
`RelationsSourceAuthorityBindingMatches` predicate for family
`"relation-definition-view"`, source
`DefinitionViewSource(view.coordinate)`, and
manifest `DefinitionViewFields(view.manifest)`; its local coordinate is the
identical issued view object. The view, binding, capability, and issuance
aggregate are process-local and nonserializable. Equal values, a reconstructed
binding, a copied capability, another profile, or another definition cannot
authorize consumption.

The selected Schnorr pressure case uses one admitted definition-language
payload with the exact typed leaves
`generator : Natural`, `scalar_modulus : Natural`, and
`group_modulus : Natural`. Its bounded executable witness additionally checks
`1 < generator < group_modulus`, `scalar_modulus > 1`, and
`generator^scalar_modulus mod group_modulus = 1`. Those checks establish only
formation of this selected fixed-setup payload; they do not establish
primality, exact generator order, relation satisfaction, or a Schnorr security
theorem. K3-C may read these leaves only through the issued owner view.

### 3.2 Four non-collapsible Interface roles

~~~text
RelationValueDecl = { value_type: ValueType }

RelationOracleStatementDecl = {
  public_binding_type: ValueType,
  material_type: ValueType,
  index_type: ValueType,
  answer_type: ValueType,
  access_law:
    ModuleDeclarationRef<"relations.oracle-access-law">
}

RelationInterface = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  definition_id: RelationDefinitionId,
  public_instance: CanonicalSeq<RelationValueDecl>,
  private_witness: CanonicalSeq<RelationValueDecl>,
  oracle_statements: CanonicalSeq<RelationOracleStatementDecl>,
  phase_inputs: CanonicalSeq<RelationValueDecl>
}

RelationInterfaceId =
  RelationsId<"relations.interface">(B, RelationInterfaceBody)
~~~

For every Oracle declaration, the four written types equal the four lifted
types of its admitted `OracleAccessLawContractV0` in the same order. Repeating
them is intentional Interface commitment, not provider authority: a mismatch
refuses Interface admission. The contract's `bind` and `lookup` ABIs are also
checked here.

The roles mean:

- `PublicInstance`: externally meaningful public relation input;
- `PrivateWitness`: prover-held existential material;
- `OracleStatement`: public binding plus privately supplied logical oracle
  material available through the declared access law; and
- `PhaseInput`: a public value supplied after the initial statement, commonly
  from a verifier challenge or an earlier public reduction result.

`PhaseInput` is required for randomized AIR and phased reductions. It is not a
public instance input because it need not exist when the initial statement is
formed, and it is not witness because the prover does not control its source.
`OracleStatement` is not witness: its public binding, private material, and
restricted verifier access have different security meanings.

Outward references are:

~~~text
RelationPublicRef  = RelationRef<RelationInterface, PublicInstance>
RelationWitnessRef = RelationRef<RelationInterface, PrivateWitness>
RelationOracleRef  = RelationRef<RelationInterface, OracleStatement>
RelationPhaseRef   = RelationRef<RelationInterface, PhaseInput>

ResolvedPublicDecl(r) =
  AdmittedRelationInterface(r.owner_id).public_instance[r.canonical_ordinal]
ResolvedWitnessDecl(r) =
  AdmittedRelationInterface(r.owner_id).private_witness[r.canonical_ordinal]
ResolvedOracleDecl(r) =
  AdmittedRelationInterface(r.owner_id).oracle_statements[r.canonical_ordinal]
ResolvedPhaseDecl(r) =
  AdmittedRelationInterface(r.owner_id).phase_inputs[r.canonical_ordinal]
~~~

Structured matrices, traces, vectors, polynomials, proof objects, and oracle
materials remain one exact K1 `ValueType` when that is their semantic shape.
They are not exploded into scalar ports. An exact typed value selector may
name:

~~~text
TypedValueSelector = Whole | Path(NonEmptyCanonicalSeq<SelectorStep>)

SelectorStep =
    RecordField(field_ordinal)
  | VariantPayload(case_ordinal)
  | SequenceElement(element_ordinal)
~~~

Formation walks the exact K1 `FiniteSchema`: each record/case ordinal is in
range, each sequence index is below the schema bound, and the complete path
derives one exact selected `ValueType`. Callers cannot assert that type. At
value selection a wrong active variant case yields `CaseAbsent`; it is a
meaningful value disagreement when the question asserted that path, not
permission to read another case.

### 3.3 Public instance

~~~text
RelationInstance = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  interface_id: RelationInterfaceId,
  public_values:
    TotalMap<RelationPublicRef, CanonicalValue<declared type>>,
  oracle_public_bindings:
    TotalMap<RelationOracleRef,
             CanonicalValue<declared public_binding_type>>,
  phase_values:
    TotalMap<RelationPhaseRef, CanonicalValue<declared type>>
}

RelationInstanceId =
  RelationsId<"relations.instance">(B, RelationInstanceBody)
~~~

Every map is total and extra-key-free for the exact Interface. A phase-valued
instance can be formed only after those phase values exist. A pre-challenge
template that omits them is not an admitted `RelationInstance` and cannot be
used as satisfaction or run-grounding authority.

The public identity commits only to public instance values, public oracle
bindings, phase values, and the exact Interface. It never commits to witness
or oracle material.

### 3.4 Admission claims

Definition admission establishes K1 formation and the definition-language
contract. Interface admission establishes exact roles, types, oracle access
ABIs, reference domains, and dependency closure. Instance admission
establishes exact total assignments and domain membership.

These admissions do not establish:

- fidelity of an imported source language;
- fidelity of a semantic model to a relation definition;
- satisfiability or satisfaction;
- existence or possession of private material; or
- correspondence to any Protocol, external Interface, Plan, or artifact.

Each stronger proposition has a separate question and result.

## 4. Confidential assignments and satisfaction

### 4.1 Owner-local private occurrences

~~~text
PrivateWitnessAssignmentBody = {
  instance_id: RelationInstanceId,
  values:
    TotalSecretMap<RelationWitnessRef, SecretValueCapability<declared type>>
}

OracleMaterialAssignmentBody = {
  instance_id: RelationInstanceId,
  values:
    TotalSecretMap<RelationOracleRef,
                   SecretValueCapability<declared material_type>>
}

PrivateWitnessAssignment =
  OwnerLocalOccurrence<PrivateWitnessAssignmentBody>

OracleMaterialAssignment =
  OwnerLocalOccurrence<OracleMaterialAssignmentBody>
~~~

Allocation is fresh, atomic, process-local, unlinkable, and nonserializable.
The owner retains one exact occurrence-to-body association. A missing,
multiply associated, wrong-generation, or body-mismatched reference is
malformed. No public semantic object, binding, artifact observation, or
structural correspondence may inspect these assignments.

Witness generation, nonce/advice generation, oracle storage, and endpoint
supply remain outside Relations. A Plan may expose their typed sources, but it
does not create Relations references or authority.

### 4.2 Semantic model

~~~text
RelationSemanticModel = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  definition_id: RelationDefinitionId,
  interface_id: RelationInterfaceId,
  evaluator:
    ModuleDeclarationRef<"relations.satisfaction-evaluator">,
  assumptions:
    CanonicalSortedUniqueSeq<
      ModuleDeclarationRef<"relations.model-assumption">>
}

RelationSemanticModelId =
  RelationsId<"relations.semantic-model">(B, RelationSemanticModelBody)

DefinitionModelCorrespondenceQuestion = {
  definition_id: RelationDefinitionId,
  semantic_model_id: RelationSemanticModelId
}

RelationModelLawBasis<Q> = CheckedModelCertificate {
  law: ModuleDeclarationRef<"relations.definition-model-law">,
  proposition:
    CanonicalValue<PropositionType(law)> =
      RelationsPropositionValue(
        DefinitionModelLawProposition(
          Q.definition_id, Q.semantic_model_id)),
  certificate:
    CanonicalValue<CertificateType(law)>,
  assumption_evidence:
    TotalMap<AssumptionRef(law),
             CanonicalValue<EvidenceType>>
}

DefinitionModelCorrespondenceQuestionId =
  RelationsId<"relations.definition-model-question">(
    B, DefinitionModelCorrespondenceQuestionBody(Q))

CertificateCheckDisposition =
    CertificateVerified
  | CertificateVerifierFalse

CheckedDefinitionModelCorrespondence = {
  question_id: DefinitionModelCorrespondenceQuestionId,
  question: DefinitionModelCorrespondenceQuestion,
  validation_basis: RelationModelLawBasis<question>,
  disposition: CertificateCheckDisposition
}

CheckDefinitionModelCorrespondence(
  admitted DefinitionModelCorrespondenceQuestion Q with exact ID,
  exact RelationModelLawBasis<Q>,
  exact admitted law, assumption, K1 evaluation, and checker authority)
  -> Qualified<CheckedDefinitionModelCorrespondence>
~~~

The question identifies the stable proposition; the certificate and evidence
are external validation basis and do not enter its body or either semantic
subject ID. The basis binds the exact encoded proposition, total checked
assumption evidence, and the admitted law contract's own verifier. No question-
supplied checker has authority. The law assumption sequence equals the model's
assumption sequence exactly; each evidence value has the admitted assumption's
derived type and its contract predicate must complete with true. A completed
verifier `true` is Affirmative and `false` is Negative; all other qualified
outcomes retain their class. K3-B has no exhaustive definition/model lane:
adding one requires an exact definition interpreter, a complete finite-
assignment derivation, quantifier semantics, and deterministic bounds.
The portable checked result binds the exact question body and ID, law
reference, proposition, certificate, complete assumption-evidence map, and
closed disposition. Its fresh capability additionally retains the exact law
and assumption admission views, their process generations, and checker
authority. A serialized result is inert; replay reauthenticates every subject
and declaration and reruns all assumption predicates and the contract-owned
verifier. No partial checked result is formed on qualified noncompletion.

Model admission requires the admitted Interface's `definition_id` to equal the
model's `definition_id`, and requires the evaluator contract's `language` to
equal the admitted definition's `language`. Its model program has exactly
`ModelProgramType(language)`. It additionally requires exact written-order
equality between the evaluator contract's four role vectors and the admitted
Interface's public-instance types, Oracle
`(public_binding_type,index_type,answer_type)` triples, phase-input types, and
private-witness types. Declaration admission has already checked the exact
`start` and per-Oracle `resume` ABIs. Thus a model cannot pair a definition
with an unrelated Interface or evaluator while remaining well formed, and no
Interface ID need enter a module declaration and create an identity cycle.
Model admission checks the exact assumption references. It does not by itself
establish that the model faithfully interprets the definition;
`CheckDefinitionModelCorrespondence` owns that proposition.

~~~text
RestrictedOracleAccessCapability<I,o> =
  opaque owner-local capability exposing only
    Lookup(CanonicalValue<index_type(o)>)
      -> CanonicalValue<answer_type(o)>

IssueRestrictedOracleAccess(
  admitted RelationInstance I,
  fresh OracleMaterialAssignment M for I,
  every admitted OracleAccessLawContractV0,
  exact evaluation authority and limits)
  -> Qualified<RestrictedOracleAccessSet>
~~~

For each Oracle `o`, issuance reads its material once under the assignment
capability, evaluates `bind(material)`, and requires exact K1 equality with
`I.oracle_public_bindings[o]`. Inequality is a completed Negative binding
check; no access capability is issued. On success, `Lookup(i)` evaluates only
the declared `lookup(material,i)` and returns its exact answer. The capability
does not expose `material`, and its invocation record retains Oracle ref,
index, answer, contract, instance, and secret-occurrence source binding for
confidential replay. Wrong instance/generation or substituted law refuses.

The Relations owner, not an evaluator callback, runs the exact deterministic
command machine:

~~~text
RunSatisfactionMachine(C, immutable_input_snapshot, access_set, controls):
  command := EvaluateK1(C.start, immutable_input_snapshot, controls.start)
  loop:
    Decide(b) -> complete with b
    Query_o({state,index}) ->
      answer := access_set[o].Lookup(index)
      command := EvaluateK1(C.resume[o], {state,answer}, controls.resume[o])
~~~

The immutable input snapshot contains the model program, exact definition
payload, public values, public Oracle bindings, phase values, and private
witness values in the contract's role order. It is captured once after all
model, instance, secret-assignment, assumption, and Oracle-binding checks. The
driver dispatches only by the closed command tag, uses the same-ordinal access
capability and resume algorithm, and retains an owner-local ordered trace.
Portable algorithms receive neither a capability nor Oracle material. The
machine state, witness values, query indices, answers, and trace have no public
durable encoding.

### 4.3 Occurrence-local satisfaction

~~~text
RelationSatisfactionDisposition = DecideTrue | DecideFalse

SatisfactionEvaluatorFor(M) =
  the exact admitted SatisfactionEvaluatorContractV0 body named by the
  evaluator field of the exact admitted RelationSemanticModel M

SatisfactionMachineStepBinding<C> =
    StartStep {
      algorithm: exact admitted evaluator start algorithm,
      input: SatisfactionMachineInputType(C),
      completed_k1_evaluation: exact completed K1 result binding
    }
  | ResumeStep {
      oracle_ordinal: Natural,
      algorithm: exact admitted evaluator resume[oracle_ordinal] algorithm,
      input: SatisfactionMachineResumeInputType(C,oracle_ordinal),
      completed_k1_evaluation: exact completed K1 result binding
    }

CheckedRelationSatisfaction<C> =
  owner-local nonserializable association of {
    semantic_model_id: RelationSemanticModelId,
    evaluator: exact admitted satisfaction-evaluator declaration/body C and
      matching fresh admission capability,
    definition_model_result:
      exact fresh affirmative CheckedDefinitionModelCorrespondence binding,
    instance_id: RelationInstanceId,
    witness_assignment: exact PrivateWitnessAssignment occurrence and
      fresh source binding,
    oracle_material_assignment: exact OracleMaterialAssignment occurrence and
      fresh source binding,
    assumption_evidence_and_checks: exact total admitted-model binding,
    restricted_access: exact fresh RestrictedOracleAccessSet binding,
    immutable_input_snapshot: SatisfactionMachineInputType(C),
    trace: FiniteSeq<SatisfactionMachineStepBinding<C>>,
    controls_and_limits: exact evaluation contracts, request limits, and
      machine-transition limit,
    disposition: RelationSatisfactionDisposition
  }

CheckRelationSatisfaction(
  admitted RelationSemanticModel M,
  affirmative CheckedDefinitionModelCorrespondence,
  admitted RelationInstance,
  fresh PrivateWitnessAssignment,
  fresh OracleMaterialAssignment,
  exact total assumption-evidence map for M.assumptions,
  affirmative same-occurrence Oracle binding checks,
  fresh RestrictedOracleAccessSet,
  exact K1 evaluation support and immutable dependency snapshot,
  exact start/resume evaluation contracts and request limits,
  finite machine-transition limit)
  -> Qualified<CheckedRelationSatisfaction<SatisfactionEvaluatorFor(M)>>
~~~

The result is affirmative exactly when the owner driver reaches
`Decide(true)`, and negative exactly when it reaches `Decide(false)`. It binds the
exact model, definition-model result, instance, both private occurrence
coordinates, assumption evidence and checks, restricted-access issuance and
lookup trace, evaluator contract and algorithms, immutable snapshots, control
contracts and limits, and completed evaluation facts. Exhausting a K1 budget
or the machine-transition limit is `DeterministicLimitExceeded`; unavailable
support or lookup cannot answer; an evaluator implementation disagreement is
`CheckerFailure`. None is Boolean false or may mint a partial checked result.
The machine is therefore an exact deterministic partial decision procedure.
The trace is nonempty. A `StartStep` must be first and occurs exactly once; each following
`ResumeStep` is the one response to the preceding `Query_o`, uses that exact
ordinal, state, index, restricted-access answer, and admitted resume algorithm,
and no step follows a `Decide`. Only the terminal completed `Decide` command
selects the disposition. The association has no semantic ID, `RB` case, or
portable result body.
A future claim that every admitted model decides a total Boolean predicate
requires a separately checked termination basis; an authored step bound is not
such a proof.

Because its complete premise is confidential and occurrence-sensitive, the
live result and source binding are owner-local. A public attempt summary may
disclose policy-permitted facts, but is inert and cannot recreate the premise
or capability. Replay requires a new confidential occurrence and a complete
rerun; equal secret values do not recreate the old result.

Satisfaction says nothing about Protocol acceptance, witness knowledge,
soundness, completeness, zero knowledge, or endpoint behavior.

## 5. Relation transforms and refinements

Value representation, relation transformation, and proof reduction are three
different algebras.

### 5.1 Typed relation transform

For Interface `I`, let `PublicInstanceType(I)` be the K1 record type derived
in canonical role order from its public values, oracle public bindings, and
phase values.

~~~text
RelationTransform = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  input_interfaces: NonEmptyCanonicalSeq<RelationInterfaceId>,
  parameter_types: CanonicalSeq<ValueType>,
  output_interfaces: NonEmptyCanonicalSeq<RelationInterfaceId>,
  public_derivation: PortableAlgorithmRef,
  private_derivation:
    Optional<ModuleDeclarationRef<"relations.private-transform-contract">>
}

RelationTransformId =
  RelationsId<"relations.transform">(B, RelationTransformBody)
~~~

The public algorithm ABI is:

~~~text
(PublicInstanceType(input_interfaces[0]), ...,
 parameter_types...)
  -> Record<PublicInstanceType(output_interfaces[0]), ...>
~~~

It derives output instances; it is not a per-value representation bridge. A
private-transform contract describes how an authorized holder may derive
output witness or oracle-material occurrences without putting secrets in the
transform identity. When present, its input/output private record-type
sequences and parameter sequence must equal those derived from the transform's
ordered Interfaces and `parameter_types`, and only its admitted `derive`
algorithm has the written ABI. Its existence is not a witness-possession claim.

### 5.2 Directional refinement

~~~text
RelationRefinementDirection =
    ForwardSatisfaction
  | BackwardSatisfaction

RelationRefinementQuestion = {
  transform_id: RelationTransformId,
  direction: RelationRefinementDirection,
  input_models:
    TotalMap<input_ordinal, RelationSemanticModelId>,
  output_models:
    TotalMap<output_ordinal, RelationSemanticModelId>
}

RelationRefinementQuestionId =
  RelationsId<"relations.refinement-question">(
    B, RelationRefinementQuestionBody(Q))

RelationRefinementLawBasis<Q> = CheckedRefinementCertificate {
  law: ModuleDeclarationRef<"relations.refinement-law">,
  proposition:
    CanonicalValue<PropositionType(law)> =
      RelationsPropositionValue(
        RefinementLawProposition(
          Q.transform_id, Q.direction,
          Q.input_models, Q.output_models)),
  certificate: CanonicalValue<CertificateType(law)>,
  assumption_evidence:
    TotalMap<AssumptionRef(law), CanonicalValue<EvidenceType>>
}

CheckedRelationRefinement = {
  question_id: RelationRefinementQuestionId,
  question: RelationRefinementQuestion,
  validation_basis: RelationRefinementLawBasis<question>,
  disposition: CertificateCheckDisposition
}

CheckRelationRefinement(
  admitted RelationRefinementQuestion Q with exact ID,
  exact RelationRefinementLawBasis<Q>,
  exact admitted law, assumption, K1 evaluation, and checker authority)
  -> Qualified<CheckedRelationRefinement>
~~~

`ForwardSatisfaction` asks whether satisfying input occurrences admit
transform-consistent satisfying output occurrences. `BackwardSatisfaction`
asks whether satisfying transform-consistent output occurrences entails the
named input satisfaction proposition. Full equivalence is the pair of two
separately checked directional results, never a subtype or inferred inverse.
The question body contains only the stable proposition. Its certificate and
assumption evidence are an external validation basis bound into the checked
result, not semantic identity. K3-B invokes only the admitted refinement-law
contract's exact verifier over the exact encoded proposition and checked
assumption evidence. It has no exhaustive refinement lane: such a lane also
requires exact quantifier order, transform-consistency semantics, complete
owner-derived assignment domains, and deterministic bounds.
`CertificateVerified` is Affirmative and `CertificateVerifierFalse` is
Negative. The portable result binds the complete question and exact external
validation basis. Its fresh capability retains the exact law and assumption
admission views, their process generations, and checker authority. Missing
support, failed assumption evaluation, malformed evidence, limit exhaustion,
and checker failure retain their qualified classes and produce no partial
checked result. Replay reauthenticates every subject and declaration and
reruns all assumption predicates and the contract-owned verifier.

This pure relation proposition is distinct from a K2 `ReductionRef`.
Probabilistic error, adversarial strategy, transcript dependence, proof
soundness/completeness, and quantitative loss remain Analysis judgments. A
Protocol reduction may be structurally attached to a transform or refinement
without establishing either.

## 6. Exactly three value-bridge lanes

A value bridge relates two exact same-regime value representations. It never
denotes a commitment, relation transform, Protocol reduction, or semantic
implication. Literal equality of one exact `ValueType` needs no bridge.

~~~text
SameRegimeTotalAlgorithm<A,B> =
  admitted PortableAlgorithmRef with exact A -> B ABI and empty failure row

BridgeLawProposition =
    EquivalenceLaw {
      source_type, target_type, forward, backward
    }
  | EmbeddingLaw {
      source_type, target_type, embed, in_image, recover
    }
  | LossyCollisionLaw {
      source_type, target_type, project, collision_relation
    }

ValueBridgeLawBasis<P> =
    DerivedExhaustive {
      maximum_value_checks: Natural,
      per_request_limits: PortableEvaluationLimitsV0
    }
  | CheckedCertificate {
      law: ModuleDeclarationRef<"relations.value-bridge-law">,
      proposition: CanonicalValue<PropositionType(law)> =
        RelationsPropositionValue(BridgeLawPropositionValue(P)),
      certificate: CanonicalValue<CertificateType(law)>,
      assumption_evidence:
        TotalMap<AssumptionRef(law), CanonicalValue<EvidenceType>>
    }

ValueEquivalence<A,B> = {
  forward: SameRegimeTotalAlgorithm<A,B>,
  backward: SameRegimeTotalAlgorithm<B,A>
}

ValueEmbedding<A,B> = {
  embed: SameRegimeTotalAlgorithm<A,B>,
  in_image: SameRegimeTotalAlgorithm<B,Bool>,
  recover: SameRegimeTotalAlgorithm<B,InImage(A) | OutsideImage>
}

LossyProjection<A,B> = {
  project: SameRegimeTotalAlgorithm<A,B>,
  collision_relation: SameRegimeTotalAlgorithm<(A,A),Bool>,
  source_premise:
    ModuleDeclarationRef<"relations.loss-source-premise">,
  quantitative_export:
    ModuleDeclarationRef<"relations.loss-export">
}

ValueBridge = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  source_type: ValueType,
  target_type: ValueType,
  lane:
      Equivalence(ValueEquivalence<source_type,target_type>)
    | Embedding(ValueEmbedding<source_type,target_type>)
    | LossyProjection(LossyProjection<source_type,target_type>)
}

ValueBridgeId = RelationsId<"relations.value-bridge">(B, ValueBridgeBody)

AuthenticatedValueBridgeCandidate = {
  body: ValueBridge,
  bridge_id: ValueBridgeId computed from that exact body,
  exact authenticated module/declaration/algorithm dependency preimages,
  exact admitted dependency views and ABI bindings,
  no bridge-admission or bridge-law authority
}

AuthenticateValueBridge(
  exact canonical ValueBridge body,
  exact dependency preimages,
  exact admitted dependency views and matching fresh capabilities)
  -> Qualified<AuthenticatedValueBridgeCandidate>

BridgeLawClause =
    EquivalenceBackwardAfterForward
  | EquivalenceForwardAfterBackward
  | EmbeddingForwardInImage
  | EmbeddingForwardRecovery
  | EmbeddingImageRecoveryAgreement
  | EmbeddingOutsideImageAgreement
  | LossyCollisionCharacterization

BridgeLawCheckDisposition =
    DerivedExhaustiveVerified { evaluated_clause_inputs: Natural }
  | DerivedExhaustiveViolation {
      clause: BridgeLawClause,
      canonical_input_ordinal: Natural
    }
  | CertificateVerified
  | CertificateVerifierFalse

CheckedBridgeLawBasis = {
  candidate_bridge_id: ValueBridgeId,
  candidate_body: ValueBridge,
  proposition: BridgeLawProposition derived from candidate_body,
  validation_basis: ValueBridgeLawBasis<proposition>,
  disposition: BridgeLawCheckDisposition
}

CheckBridgeLawBasis(
  exact AuthenticatedValueBridgeCandidate,
  exact ValueBridgeLawBasis derived for that candidate proposition,
  for CheckedCertificate: exact admitted bridge-law declaration, every exact
    admitted assumption declaration, and matching fresh admission/checker
    capabilities,
  exact K1 evaluator support, immutable dependency snapshot, and limits)
  -> Qualified<CheckedBridgeLawBasis>

AdmitValueBridge(
  exact AuthenticatedValueBridgeCandidate,
  exact matching affirmative CheckedBridgeLawBasis and fresh capability,
  exact dependency views and matching fresh capabilities)
  -> QualifiedAdmission<AdmittedValueBridge>

ValueRelation =
    SameExactType
  | ApplyBridge(ValueBridgeId, Forward | Backward)
~~~

`AuthenticateValueBridge` strictly forms the body and computes its ID before
any bridge law is claimed. `used_modules` must be exactly the direct module set
of both endpoint types, every lane algorithm, every premise/export declaration,
and their immediate typed dependencies. Every dependency view and algorithm
ABI is already admitted, all semantic dependencies carry the candidate's exact
regime, and cross-regime meaning is `Unsupported`. For a lossy candidate, the
lifted `source_anchor_type` of the exact admitted `source_premise` contract must
equal `source_type` exactly. Authentication records that compatibility and
admission rechecks it. Neither step may infer a bridge law from structural
formation alone.

A validation law, certificate, assumption evidence, evaluation contract, or
request limit is deliberately absent from `ValueBridgeId`: it is bound by the
fresh law check. `CheckBridgeLawBasis` derives `P` from the complete exact
`AuthenticatedValueBridgeCandidate`, including its computed ID and admitted
dependency/ABI views; it does not require or create an admitted bridge. The
basis is an external validation request and never changes bridge meaning or
identity. For a derived-exhaustive basis, Relations itself enumerates every
canonical value exactly once in ascending `M(datum)`-byte order, the K1
canonical-body order, but only for
types whose complete domain follows mechanically from the closed K1 root
grammar. It refuses an authored enumerator, checks the exact written equations,
and applies the request's explicit bound and K1 limits. A non-derived domain is
`Unsupported`; bound exhaustion is `DeterministicLimitExceeded`. For a
certificate basis, the admitted law contract's proposition value must equal
`RelationsPropositionValue(BridgeLawPropositionValue(P))` exactly, its
assumption map must be total and extra-key-free, every assumption predicate
must evaluate true, and its contract-owned verifier evaluates
`(proposition,certificate,evidence-record) -> Bool`. The body cannot substitute
another verifier. The supplied law declaration must be the exact declaration
named by the basis, and the admitted assumption-declaration domain must be
every and only its ordered `AssumptionRef` domain with matching evidence types;
an ID or evidence value cannot substitute for those admission capabilities.
False is Negative; unavailable evaluation is noncompletion.
The portable checked result binds the candidate's complete body, computed ID,
proposition, exact validation basis, and closed disposition; its basis names
the certificate lane's law and assumptions but grants no live authority. Its
fresh capability retains their exact admission views, matching generations,
and checker authority. `AdmitValueBridge` reauthenticates the
candidate and dependencies and consumes a matching fresh affirmative result;
a Negative or merely stored result cannot admit it. After admission,
`ApplyValueRelation` requires both the exact `AdmittedValueBridge` and a fresh
affirmative law-result capability bound to that same candidate and basis.
Reusing a certificate, candidate, or checked result for another body, bridge
ID, or basis refuses. The dependency direction is therefore candidate -> law
check -> admission -> application, with no admission/law cycle.

The clause order is exactly the written `BridgeLawClause` order restricted to
the candidate lane. Derived checking orders each clause's canonical input
domain lexicographically by K1 canonical-body order and reports only the first
false clause/input pair; its ordinal must be in that derived finite domain.
`DerivedExhaustiveVerified` and `CertificateVerified` are Affirmative.
`DerivedExhaustiveViolation` and `CertificateVerifierFalse` are Negative.
Malformed ordinals or lane-inapplicable clauses are `Malformed`; unavailable
support and limit exhaustion remain qualified noncompletion and produce no
partial `CheckedBridgeLawBasis`.

The checked propositions are exactly:

~~~text
EquivalenceLaw:
  forall a:A. backward(forward(a)) = a
  forall b:B. forward(backward(b)) = b

EmbeddingLaw:
  forall a:A. in_image(embed(a)) = true
              and recover(embed(a)) = InImage(a)
  forall b:B. in_image(b) = true
    iff recover(b) = InImage(a) for one a with embed(a) = b
  forall b:B. in_image(b) = false iff recover(b) = OutsideImage

LossyCollisionLaw:
  forall a1,a2:A.
    collision_relation(a1,a2) =
      (a1 != a2 and project(a1) = project(a2))
~~~

No inverse or image law exists for lossy projection. The tagged embedding
recovery result is an ordinary success value, so an out-of-image input can
produce a meaningful correspondence Negative.

`ApplyValueRelation` is one exact operation, not ambient notation:

~~~text
ForwardAlgorithm(b) =
  match lane(b) with
    Equivalence(e)     -> e.forward
    Embedding(e)       -> e.embed
    LossyProjection(e) -> e.project

ApplyValueRelation(SameExactType, x:T, y:T) = K1Equal_T(x,y)

ApplyValueRelation(ApplyBridge(b,Forward), x:source_type(b),
                   y:target_type(b)) =
  K1Equal_target(Evaluate(ForwardAlgorithm(b),x), y)

ApplyValueRelation(ApplyBridge(b,Backward), x:target_type(b),
                   y:source_type(b)) =
  match lane(b) with
    Equivalence(e) -> K1Equal_source(Evaluate(e.backward,x),y)
    Embedding(e)   -> K1Equal(InImage(y),Evaluate(e.recover,x))
    LossyProjection(e) -> Unsupported
~~~

Wrong endpoint type/direction is malformed question formation. Missing
admission, module support, evaluation, or law-basis authority is qualified
noncompletion, never inequality. Only a completed Boolean becomes Affirmative
or Negative.

Every actual directed use is addressed without `ObjectRef`:

~~~text
BridgeUseCoordinate =
    ProtocolStatementEdge(ProtocolRelationBindingId, edge_ordinal)
  | ProtocolPhaseEdge(ProtocolRelationBindingId, edge_ordinal)
  | ProtocolOracleEdge(ProtocolRelationBindingId, edge_ordinal)
  | PlanWitnessEdge(PlanWitnessBindingId, edge_ordinal)
  | ArtifactComparisonClause(ArtifactComparisonQuestionId, clause_ordinal)

BridgeUseEndpoint =
    RelationPublicValue(RelationPublicRef, TypedValueSelector)
  | RelationPhaseValue(RelationPhaseRef, TypedValueSelector)
  | RelationOraclePublicBindingValue(RelationOracleRef, TypedValueSelector)
  | RelationWitnessValue(RelationWitnessRef, TypedValueSelector)
  | ProtocolRunValue(ProtocolId, ProtocolValueCoordinate,
                     TypedValueSelector)
  | PlanWitnessValue(PlanWitnessSurfaceId, WitnessSurfaceKey,
                     TypedValueSelector)
  | ArtifactValue(ArtifactFactSelector)
  | DefinitionPayloadValue(RelationDefinitionId, TypedValueSelector)

BridgeUseDescriptor = {
  coordinate: BridgeUseCoordinate,
  left_endpoint: BridgeUseEndpoint,
  right_endpoint: BridgeUseEndpoint,
  left_type: ValueType,
  right_type: ValueType,
  value_relation: ApplyBridge(ValueBridgeId, Forward | Backward)
}

ProtocolCoordinateValueType(protocol_id,c) =
  the exact CanonicalValue payload type obtained by the Section 8.4 closed
  resolution of c to the admitted protocol's PIR RelationRunFact, including
  the one written projection for TerminalPublicOutput

ResolvedPlanWitnessSurfaceEntry(surface_id,key) =
  the exact entry at key in the authenticated PIR-owned
  PlanWitnessSurfaceBody preimage of surface_id

BridgeUseEndpointType(RelationPublicValue(r,p)) =
  SelectedValueType(ResolvedPublicDecl(r).value_type,p)
BridgeUseEndpointType(RelationPhaseValue(r,p)) =
  SelectedValueType(ResolvedPhaseDecl(r).value_type,p)
BridgeUseEndpointType(RelationOraclePublicBindingValue(r,p)) =
  SelectedValueType(ResolvedOracleDecl(r).public_binding_type,p)
BridgeUseEndpointType(RelationWitnessValue(r,p)) =
  SelectedValueType(ResolvedWitnessDecl(r).value_type,p)
BridgeUseEndpointType(ProtocolRunValue(protocol_id,c,p)) =
  SelectedValueType(ProtocolCoordinateValueType(protocol_id,c),p)
BridgeUseEndpointType(PlanWitnessValue(surface_id,key,p)) =
  SelectedValueType(
    ResolvedPlanWitnessSurfaceEntry(surface_id,key).value_type,p)
BridgeUseEndpointType(ArtifactValue(s)) = ArtifactSelectorType(s)
BridgeUseEndpointType(DefinitionPayloadValue(d,p)) =
  SelectedValueType(DefinitionPayloadType(d),p)

CheckedBridgeUse = {
  coordinate: BridgeUseCoordinate,
  left_endpoint: BridgeUseEndpoint,
  right_endpoint: BridgeUseEndpoint,
  left_type: ValueType,
  right_type: ValueType,
  bridge_id: ValueBridgeId,
  direction: Forward | Backward
}

BridgeUseScope = {
  protocol_bindings:
    CanonicalSortedUniqueSeq<ProtocolRelationBindingId>,
  plan_witness_bindings:
    CanonicalSortedUniqueSeq<PlanWitnessBindingId>,
  artifact_questions:
    CanonicalSortedUniqueSeq<ArtifactComparisonQuestionId>
}

BridgeUseSet = {
  scope: BridgeUseScope,
  entries: CanonicalSortedUniqueSeq<CheckedBridgeUse>
}

CheckBridgeUseSet(
  exact BridgeUseScope,
  exact admitted subject for every ID in that scope,
  exact admitted ValueBridge and declaration dependencies for every
    ApplyBridge occurrence,
  matching fresh affirmative bridge-law authority for every used bridge)
  -> Qualified<BridgeUseSet>
~~~

`BridgeUseEndpointType` is a closed owner-derived function. Relation arms
select from the exact admitted Interface role type; `ProtocolRunValue` selects
from the exact K2 value-producing coordinate type in the named admitted
Protocol; `PlanWitnessValue` selects from the exact entry type in the named
admitted surface; `ArtifactValue` uses `ArtifactSelectorType`; and
`DefinitionPayloadValue` selects from `DefinitionPayloadType`. Every selector
is checked by Section 3.2. No caller supplies an endpoint type.

`BridgeUseDescriptor(c)` is likewise closed. For a Protocol edge it resolves
the named admitted binding and edge ordinal, puts the relation endpoint on the
left, converts the written `StatementTarget`, `PhaseTarget`, or `OracleTarget`
to its one exact `ProtocolValueCoordinate` on the right, and copies the edge's
selectors and `value_relation`. For a Plan edge it puts the relation witness
endpoint on the left and the named surface entry on the right. For an artifact
semantic clause it puts the artifact selector on the left and the
`DefinitionPayload` selector on the right. A structural artifact clause or a
`SameExactType` occurrence has no bridge-use descriptor. Owner admission and
ordinal resolution precede descriptor construction.

`CheckBridgeUseSet` enumerates every and only `ApplyBridge` occurrence in every
exact admitted binding and Relations-owned artifact question named by its
scope,
derives `BridgeUseDescriptor` for each, requires descriptor endpoint types to
equal the admitted bridge endpoint types in the written direction, rejects
duplicates or omitted/extra occurrences, and copies only those derived fields
into one immutable checked set. A lossy bridge may occur only in `Forward`
direction; `Backward` is `Unsupported` because the lane defines no inverse.
`BridgeUseCardinality(set,b)` is the derived number of `set.entries` for `b`; there
is no authored count.

A consuming question or operation derives its required `BridgeUseScope` from
its own admitted operands and requires exact scope equality before using the
set capability. A caller-selected subset cannot authorize a count for the
larger consumer. The result record is inert; only its fresh capability binds
the complete scope, entries, admitted owners, bridge/declaration dependencies,
and law authorities.
An exactly derived valid set completes Affirmative. A wrong scope, owner,
ordinal, endpoint, or duplicate is malformed or refused; missing support or
law authority is qualified noncompletion. None is a semantic value
disagreement.

A lossy entry may be inspected structurally without a source premise. Before a
value-consuming operation may use it or Analysis may consume its selected
cardinality, however, every coordinate in that consumer's owner-derived exact
complete `LossyUseSelection` additionally requires the occurrence-local
grounding, premise, export, and consumer-source join defined in Section 10.2.
An inert checked-use record, bridge coordinate, equal source value at another
occurrence, or authored count cannot substitute for that path. K3-B closes
this consumer join only for run-grounded relation instance values;
structural/coverage, Plan, and artifact questions neither consume a count nor
imply a checked source premise. Their future live-value operations must define
their own exact selection and source binding before quantitative use.
Relations exports its fixed checked-use facts and selected cardinality only at
the closed run-grounded seam; the whole-scope `BridgeUseCardinality` remains
inert, and Analysis alone owns games, reductions, and quantitative loss. In
particular, `sha256-216` cannot acquire a
collision-resistance term unless every source occurrence counted at that seam
completes its required preimage-hash premise.

## 7. Cycle-free Protocol and Plan attachments

### 7.1 Occurrence edges, not value maps

Correspondence is a canonical graph over exact typed occurrences:

~~~text
RelationEndpoint = {
  relation_ref: RelationPublicRef | RelationOracleRef | RelationPhaseRef,
  selector: TypedValueSelector
}

ProtocolValueEndpoint = {
  source: ProtocolValueCoordinate,
  selector: TypedValueSelector
}

OccurrenceEdge<R, P> = {
  relation: R,
  protocol: P,
  value_relation: ValueRelation
}
~~~

Edges are sorted and exact duplicates reject. There is no global injectivity
or surjectivity law in edge admission. One structured Statement may expose
several selected relation values; one relation value may be repeated in
several Protocol occurrences. Equal values do not merge occurrences.

Functional, injective, partition, and whole-surface requirements belong to the
exact correspondence question.

### 7.2 Protocol relation binding

~~~text
StatementTarget = {
  binding: BindingRef restricted to class Statement,
  selector: TypedValueSelector
}

PhaseTarget =
    ChallengeValue(ChallengeRef, TypedValueSelector)
  | PublicOccurrenceOutput(OccurrenceRef, output_ordinal,
                           TypedValueSelector)

OracleAccessTarget = {
  query_occurrence: OccurrenceRef,
  answer_occurrence: OccurrenceRef
}

OracleTarget = {
  oracle: OracleRef,
  publication_occurrence: OccurrenceRef,
  public_binding_output: (publication_occurrence, output_ordinal = 0),
  public_binding_selector: TypedValueSelector,
  public_accesses: CanonicalSeq<OracleAccessTarget>
}

StatementEdge = OccurrenceEdge<
  { ref: RelationPublicRef, selector: TypedValueSelector },
  StatementTarget>

PhaseEdge = OccurrenceEdge<
  { ref: RelationPhaseRef, selector: TypedValueSelector },
  PhaseTarget>

OraclePublicBindingEdge = OccurrenceEdge<
  { ref: RelationOracleRef, selector: TypedValueSelector },
  OracleTarget>

ProtocolRelationBinding = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  protocol_id: ProtocolId,
  relation_interfaces:
    NonEmptyCanonicalSortedUniqueSeq<RelationInterfaceId>,
  statement_edges: CanonicalSeq<StatementEdge>,
  phase_edges: CanonicalSeq<PhaseEdge>,
  oracle_edges: CanonicalSeq<OraclePublicBindingEdge>,
  claim_meanings: CanonicalSeq<ClaimMeaningBinding>,
  reduction_meanings: CanonicalSeq<ReductionMeaningBinding>,
  commitment_groundings:
    CanonicalSortedUniqueSeq<CommitmentGroundingId>
}

ProtocolRelationBindingId =
  RelationsId<"relations.protocol-binding">(
    B, ProtocolRelationBindingBody)
~~~

The base binding depends only on one exact `ProtocolId` and its relation
Interfaces. It never depends on a `ProtocolInterfaceId`, Plan, OIR, artifact
observation, run, or checked result. External Interface correspondence is a
later independent question. This direction prevents Protocol, Interface, or
Plan from acquiring a back-reference to Relations.

The binding may cite only K2 source coordinates already owned by the admitted
Protocol. It cannot create a second transcript declaration, claim flow,
oracle lifecycle, effect, or terminal meaning.

Its `relation_interfaces` set equals every and only Interface reached from its
edges, recipes, transforms, and commitment material. Every grounding run slot
names the binding's exact `ProtocolId`. Missing, unused, extra, wrong-Protocol,
or wrong-Interface entries refuse admission; these closure checks do not
precompute mapped or whole-surface correspondence.

For each `OraclePublicBindingEdge` to K2 Oracle `o`, structural admission
requires exactly one `PublishOracle(o)` at the named occurrence; equal Oracle
and occurrence scope; publication-before-query; and every entry of
`public_accesses` to name one later `QueryOracle(o)` plus its unique later
`AnswerOracle(query)`, both with K2 visibility `Public`, equal scope, compatible
guards, and no duplicate query or answer occurrence. The relation Oracle's material,
index, and answer types must equal `OracleCarrierType(o)`, `o.index_type`, and
`OracleLookupResultType(o)` exactly. Its public-binding edge compares against
`OraclePublicationOutputType(o)` through the written `ValueRelation`. Both the
Relations access contract and K2 publication/binding algorithms must be
admitted at their exact ABIs. These are structural type, scope, occurrence, and
access-shape requirements only; equality of the two binding meanings, BCS
correspondence, salting, openings, and cryptographic binding remain the
post-K3-B K4 P02 obligation.

### 7.3 Claim and reduction meaning

~~~text
RecipeInputInstanceDecl = { interface_id: RelationInterfaceId }
RecipeParameterDecl = { value_type: ValueType }

RecipeInputInstanceRef = canonical ordinal in `input_instances`
RecipeParameterRef = canonical ordinal in `parameters`

TypedDerivationSource =
    Protocol(ProtocolValueCoordinate)
  | InputInstance(RecipeInputInstanceRef,
                  RelationPublicRef | RelationOracleRef | RelationPhaseRef,
                  TypedValueSelector)
  | Parameter(RecipeParameterRef)
  | Constant(CanonicalValue)

TypedDerivationRef = Source(source_ordinal) | Step(step_ordinal)

TypedDerivationStep = {
  inputs: CanonicalSeq<TypedDerivationRef>,
  output_type: ValueType,
  algorithm: PortableAlgorithmRef
}

TypedAcyclicDerivation = {
  sources: CanonicalSeq<TypedDerivationSource>,
  steps: CanonicalSeq<TypedDerivationStep>
}

DerivationInstanceFieldType(r,p) =
  match r with
    RelationPublicRef ->
      SelectedValueType(ResolvedPublicDecl(r).value_type,p)
    RelationOracleRef ->
      SelectedValueType(ResolvedOracleDecl(r).public_binding_type,p)
    RelationPhaseRef ->
      SelectedValueType(ResolvedPhaseDecl(r).value_type,p)

DerivationSourceType(binding,recipe,Protocol(c)) =
  ProtocolCoordinateValueType(binding.protocol_id,c)
DerivationSourceType(binding,recipe,InputInstance(i,r,p)) =
  DerivationInstanceFieldType(r,p), provided
  r.owner_id = recipe.input_instances[i].interface_id
DerivationSourceType(binding,recipe,Parameter(i)) =
  recipe.parameters[i].value_type
DerivationSourceType(binding,recipe,Constant(v)) =
  the exact ValueType carried by canonical value v

DerivationRefType(binding,recipe,d,k,Source(i)) =
  DerivationSourceType(binding,recipe,d.sources[i])
DerivationRefType(binding,recipe,d,k,Step(j)) =
  d.steps[j].output_type, provided j < k

DerivationInputType(binding,recipe,d,k) =
  RootRecord<[(i,DerivationRefType(
    binding,recipe,d,k,d.steps[k].inputs[i]))
    for every input ordinal i in written order]>

RelationInstanceRecipe = {
  interface_id: RelationInterfaceId,
  input_instances: CanonicalSeq<RecipeInputInstanceDecl>,
  parameters: CanonicalSeq<RecipeParameterDecl>,
  derivation: TypedAcyclicDerivation,
  outputs: TotalMap<
    RelationPublicRef | RelationOracleRef | RelationPhaseRef,
    TypedDerivationRef>
}

RecipeParameterSource =
    Protocol(ProtocolValueCoordinate)
  | Constant(CanonicalValue)

ClaimMeaningBinding = {
  claim: ClaimRef,
  instance_recipe: RelationInstanceRecipe,
  input_bindings:
    TotalMap<RecipeInputInstanceRef, ClaimMeaningLocalRef>,
  parameter_bindings:
    TotalMap<RecipeParameterRef, RecipeParameterSource>
}

ClaimMeaningLocalRef = canonical ordinal in `claim_meanings`

TransformInputBinding = {
  transform_input_ordinal: Natural,
  meaning: ClaimMeaningLocalRef
}

TransformOutputBinding = {
  transform_output_ordinal: Natural,
  meaning: ClaimMeaningLocalRef
}

ReductionParameterSource =
    SideInput(side_input_ordinal: Natural, value: ValueRef)
  | RequiredChallenge(challenge_ordinal: Natural, challenge: ChallengeRef)
  | RequiredPublication(
      publication_ordinal: Natural,
      requirement: ReductionPublicationRequirement,
      value: ProtocolValueCoordinate)

TransformParameterBinding = {
  transform_parameter_ordinal: Natural,
  parameter_type: ValueType,
  source: ReductionParameterSource
}

ReductionMeaningBinding = {
  reduction: ReductionRef,
  input_bindings: NonEmptyCanonicalSeq<TransformInputBinding>,
  output_bindings: CanonicalSeq<TransformOutputBinding>,
  transform: RelationTransformId,
  side_inputs: CanonicalSeq<ValueRef>,
  required_challenges: CanonicalSeq<ChallengeRef>,
  required_publications:
    CanonicalSeq<ReductionPublicationRequirement>,
  parameter_bindings: CanonicalSeq<TransformParameterBinding>
}
~~~

Several local meanings may cite one K2 claim, but each remains a distinct
occurrence in the canonical graph. For an initial claim, K2 requires
`InitialClaim(BindingRef)` and the recipe
must include that exact Statement occurrence. For a reduction output, the
claim source must be `ReductionOutput(reduction, output_ordinal)`. The meaning's
`side_inputs`, `required_challenges`, and complete
`(publication,next_challenge)` records equal the K2 `ReductionDecl` sequences
element for element; a bare publication occurrence is insufficient.

Claim meanings are topologically ordered. Every recipe input binding is total
and extra-key-free, names an earlier local meaning, and its Interface equals
the corresponding `RecipeInputInstanceDecl`. Every recipe parameter binding is
total and extra-key-free and its selected Protocol value or constant has the
declared parameter type. For each reduction output meaning, its recipe input
bindings equal that reduction meaning's ordered transform inputs, and any
recipe parameter sourced from a reduction side input, challenge, or publication
must equal the corresponding transform-parameter source binding. This closes
the declarations to actual occurrence sources without putting run values in
the durable recipe.

The four arguments written explicitly in `DerivationInputType` are the unique
enclosing admitted Protocol binding, recipe, derivation, and current step;
there is no ambient owner lookup. Its record fields preserve input order and
their ordinals are exactly `0..n-1`; an empty input sequence yields the empty
root record. Every source ordinal must exist, every instance role must belong
to the declared input Interface, every selector must type-check, and every
step reference must name an earlier step. During binding admission, for every
recipe derivation `d` and step ordinal `k`, Relations authenticates the stored
algorithm as the exact
`SameRegimeTotalAlgorithm<DerivationInputType(binding,recipe,d,k),
d.steps[k].output_type>` under the binding's regime and exact dependency
views. An unresolved, out-of-range, cross-Interface, or forward reference is
malformed rather than an unknown input type.

`input_bindings` is ordered by transform input ordinal and its meaning's claim
equals K2 `input_claims` at the same ordinal. `output_bindings` is ordered by
transform output ordinal and its meaning's claim is exactly
`ReductionOutput(reduction,ordinal)` with the K2 `output_contracts[ordinal]`.
For each input/output position, the recipe `interface_id` equals the admitted
transform's corresponding Interface exactly. There are no missing, extra,
duplicate, or reordered positions.

`parameter_bindings` is total and extra-key-free for the transform parameter
sequence, ordered by transform parameter ordinal, and repeats the exact derived
parameter type at that position. Every source ordinal resolves to the identical
entry of this meaning's exact copied K2 sequence. A publication-valued
parameter must use a value-producing `RelationRunCoordinate` for the identical
publication occurrence; its requirement retains the identical
`next_challenge`. The selected source type equals the transform parameter type.
These bindings do not assert that every K2 side input or publication has a
mathematical role beyond the K2 contract; they ensure none is erased from the
structural meaning.

The structural check proves only reference, complete K2 role-set preservation,
order, type, recipe, and transform-ABI agreement. At a qualified run the recipe
may derive exact input and output `RelationInstance` occurrences. Equality of
derived outputs with another claimed instance is a separate run-grounded output
agreement; satisfaction preservation is a separate `RelationRefinement`
question. Neither is admitted from structure, and neither proves witness
evolution, reduction soundness, or reduction completeness.

### 7.4 Plan witness binding

PIR owns the purpose-bound `PlanWitnessSurface` defined in
[Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md#5-planwitnesssurface).
It is source-ID-free:

Each binding edge uses the exact `WitnessSurfaceKey` in the binding's one
`PlanWitnessSurfaceId`. The key names only the public surface entry. It does
not embed `ProverPlanId`,
a Plan-local node/reference, producer coordinate, or private source mapping.
PIR's live `CheckedPlanWitnessSurfaceExtraction` retains those source facts.
The Relations-owned dependent subject commits to the normalized surface, not
to the full Plan:

~~~text
PlanWitnessEdge = OccurrenceEdge<
  { ref: RelationWitnessRef, selector: TypedValueSelector },
  { ref: WitnessSurfaceKey, selector: TypedValueSelector }>

PlanWitnessBinding = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  plan_witness_surface_id: PlanWitnessSurfaceId,
  relation_interface_id: RelationInterfaceId,
  witness_edges: CanonicalSeq<PlanWitnessEdge>
}

PlanWitnessBindingId =
  RelationsId<"relations.plan-witness-binding">(
    B, PlanWitnessBindingBody)
~~~

Every target must resolve to a `WitnessIngress` or `DerivedWitnessExport`
entry through the exact owner `PlanWitnessOccurrenceRef =
(plan_witness_surface_id,WitnessSurfaceKey)`, with the exact selected type and
owner-declared `SuppliedForGeneration | ProducedWhenSourceDecisionActive`
occurrence class. Advice, confidential context,
nonce/randomness, search state, and mutable state are absent from this surface
and cannot be silently forced into the relation witness image. An explicitly
exported derived witness is nameable by `WitnessSurfaceKey`. Oracle material
is supplied through its separate owner-local assignment; this witness surface
does not reclassify it. The Plan never cites a relation Interface or Relations
reference.

## 8. Exact PIR read surfaces and correspondence questions

### 8.1 REL-Q1: Statement occurrence table

PIR derives from `PublicBindingView`:

~~~text
StatementOccurrence = {
  binding: BindingRef,
  scope: ScopeRef,
  value_origin: ValueRef,
  value_type: ValueType
}

StatementOccurrenceTable =
  CanonicalSeq<every and only PublicBindingDecl with class Statement>
~~~

`MappedStatementCorrespondence` checks every requested edge and nothing else.
`WholeStatementCoverage` separately asks whether the edge targets form the
question's exact nonoverlapping cover of the complete Statement table. A
strict subset can therefore pass the mapped question and return a meaningful
negative to whole coverage.

`WholeRelationPublicCoverage` is the independent source-side question: every
selected leaf or whole occurrence of every `RelationPublicRef` must be covered
under the fixed `ExactNonoverlappingCover` and `SelectorPartition` law in
[Protocol Correspondence](protocol-correspondence.md#31-local-references-and-policies).
The question carries no caller-selected partition policy. Neither source-side
nor target-side coverage implies the other. A profile that requires bijective
whole-surface correspondence requests both and additionally requires each
side's selected partition to be one-to-one.

K2 `PublicParameter` and `SessionContext` bindings are not Statement entries.
Leaving one unmapped does not refute whole-*Statement* coverage. A later
external-Interface question may separately require total exposure of all
externally supplied public inputs.

### 8.2 REL-Q2: relation-facing private surface

`MappedPlanWitnessCorrespondence` consumes the exact admitted
`PlanWitnessBinding`, a PIR-issued source-ID-free `PlanWitnessSurface`, and its
live `CheckedPlanWitnessSurfaceExtraction`. It checks entry kind, key,
selector, type, and value-relation compatibility for requested edges. The
private Plan source coordinate remains inside PIR's extraction authority and
is not copied into the Relations subject.

`WholeRelationWitnessCoverage` and `WholePlanWitnessSurfaceCoverage` are
separate source- and target-side questions. Neither quantifies over all private
Plan inputs. A private nonwitness cannot become a relation witness merely
because it is confidential, and an exported derived witness cannot disappear
because it is not a Protocol input.

### 8.3 REL-Q3: execution-issued run view

Relations imports the exact `RunBoundary`, `RelationRunCoordinate`,
`RelationRunReadManifest`, `RelationRunFact`, `RelationRunObservation`,
`RelationRunSelectedEntry`, `RelationClaimHistory`,
`RelationReductionHistory`, `RelationRunView`, and issuance law from
[Interactive Core and Causal Execution](../pir/interactive-core.md#135-execution-issued-relation-grounding-view).
It does not define a parallel view or qualification vocabulary.

PIR issues one immutable process-local `RelationRunView` from an admitted
Protocol, exact invocation, identical `CompletedProtocolRecord`, finite
manifest, and
either the still-live causal generation capability or a fresh affirmative
`CheckedReplayMatch` result. Relations imports the exact two owner alternatives
`ReplayQualified` and `CausallyGenerated`; it does not redeclare their type.

The fresh capability binds the complete body and owner source. The view omits
unrequested data and all private strategy state. A caller tuple, raw record,
record ID, invocation ID, serialized view, equal value at another occurrence,
or replay bytes alone cannot mint it.

`ReplayQualified` is sufficient to answer what the verifier consumed.
Questions about the causal producer must require `CausallyGenerated`. A
terminal-result question cannot pass over an interpretation-failure record,
and a partial run cannot masquerade as a `CompletedProtocolRecord`.

Claim correspondence reads `ClaimHistory(claim,boundary)`, never a collapsed
final liveness bit. Its source fact therefore retains initial or reduction
creation, every ordered reusable reduction use through that boundary, and the
exact optional terminal `Consume | Discharge` disposition. Reduction
correspondence similarly reads `ReductionHistory(reduction,boundary)`. A check
at completion cannot silently substitute for the history at the reduction
boundary.

### 8.4 REL-Q4: closed read vocabulary

Relations defines selectors over that one owner view; it does not redefine the
view coordinates. Value-producing selectors are:

~~~text
ProtocolValueCoordinate =
    BindingValue(BindingRef)
  | OccurrenceOutput(OccurrenceRef, output_ordinal)
  | ChallengeValue(ChallengeRef)
  | OraclePublication(OracleRef, OccurrenceRef)
  | PublicOracleQuery(OracleRef, OccurrenceRef)
  | PublicOracleAnswer(OracleRef, OccurrenceRef)
  | TerminalPublicOutput(TerminalRef, OccurrenceRef, output_ordinal)
  | PublicModuleObservation(OccurrenceRef, output_ordinal)
~~~

Each arm resolves through the identically named PIR
`RelationRunCoordinate`, except `TerminalPublicOutput(t,o,k)`, which resolves
only through `TerminalResult(t,o)` and projects public output `k`. There is no
second way to address that output. Structural/meta selectors are:

~~~text
ProtocolStructuralSource =
    ClaimHistory(ClaimRef, RunBoundary)
  | ReductionHistory(ReductionRef, RunBoundary)
  | CheckResult(CheckRef, OccurrenceRef)
  | TerminalVerdict(TerminalRef, OccurrenceRef)
~~~

`TerminalVerdict(t,o)` likewise resolves only through
`TerminalResult(t,o)` and projects the verdict. It is a structural meta-fact,
not a canonical semantic value and cannot be passed to `ValueRelation`.
`TerminalPublicOutput` is a typed semantic value and cannot be used as a
verdict. This split gives each fact one canonical Relations address while
retaining the exact single PIR source coordinate.

Every source is resolved through the exact PIR owner view. A raw carrier path,
event label, integer ordinal without its typed family, ambient lookup, or
invented `ObjectRef` is malformed or refused.

## 9. Artifact facts and comparison

Artifact interpretation is optional and expectation-free. It observes typed
facts about exact bytes; it does not admit a relation or prove satisfaction.

### 9.1 Fact profile

~~~text
ArtifactFactDecl =
  ModuleDeclarationRef<"relations.artifact-fact">

ArtifactFactField = {
  declaration: ArtifactFactDecl,
  fact_class: StructuralMetaFact | SemanticValueFact
    derived from declaration,
  value_type: ValueType derived from declaration,
  min_count: Natural,
  max_count: Natural
}

RelationArtifactProfile = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  format:
    ModuleDeclarationRef<"relations.artifact-format">,
  fields: CanonicalSeq<ArtifactFactField>
}

RelationArtifactProfileId =
  RelationsId<"relations.artifact-profile">(
    B, RelationArtifactProfileBody)

ArtifactFieldRef =
  RelationRef<RelationArtifactProfile, ArtifactFactField>

AdmitRelationArtifactProfile(
  exact authenticated RelationArtifactProfile body and computed ID,
  exact admitted `relations.artifact-format` declaration and fresh capability,
  exact map of every and only admitted `relations.artifact-fact` declaration
    named by the fields, with matching fresh capabilities)
  -> QualifiedAdmission<AdmittedRelationArtifactProfile>

ResolvedArtifactProfile(profile_id) =
  the exact body retained by the matching admitted profile capability

ResolvedArtifactFormat(profile_id) =
  the admitted ArtifactFormatContractV0 body named by
  ResolvedArtifactProfile(profile_id).format

ResolvedArtifactField(field) =
  the exact in-bounds field occurrence selected from
  ResolvedArtifactProfile(field.owner_id).fields

ResolvedArtifactFactDeclaration(field) =
  the admitted ArtifactFactContractV0 body named by
  ResolvedArtifactField(field).declaration

ArtifactFieldValueType(field) =
  Lift(ResolvedArtifactFactDeclaration(field).value_type)

ArtifactFieldClass(field) =
  ResolvedArtifactFactDeclaration(field).fact_class

ArtifactFieldMaximum(field) = ResolvedArtifactField(field).max_count
~~~

`min_count <= max_count`, and both obey the K1 constitutional bound. Field
order is semantic; mnemonic names are diagnostic. Module declarations make
the algebra extensible without a universal hardcoded fact list. Profile
admission requires every field's written `fact_class` and `value_type` to equal
the exact values derived above, requires its format and all fact declarations
to share the profile regime, and checks `used_modules` as their exact direct
module closure. A missing declaration, wrong owner, stale capability, or
out-of-bounds field cannot form a resolved helper.
The selected format declaration derives one bounded K1 byte value type,
and admission requires it to be a K1 root byte type:

~~~text
ArtifactBytesType(profile_id) =
  Lift(ResolvedArtifactFormat(profile_id).artifact_bytes_type)
~~~

This function is defined only for the exact admitted profile and its exact
admitted format declaration; a caller-supplied byte schema has no standing.

### 9.2 Owner-issued observation and absence

~~~text
ArtifactFactObservation =
    Unread
  | Observed(CanonicalSeq<CanonicalValue<declared type>>)

RelationArtifactObservation = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  profile_id: RelationArtifactProfileId,
  artifact_value_id: CanonicalValueId<"relations.artifact-bytes">,
  interpreter:
    ModuleDeclarationRef<"relations.artifact-interpreter">,
  fields: TotalMap<ArtifactFieldRef, ArtifactFactObservation>
}

RelationArtifactObservationId =
  RelationsId<"relations.artifact-observation">(
    B, RelationArtifactObservationBody)

ArtifactByteSourceBinding = OwnerLocalOccurrence<{
  profile_id: RelationArtifactProfileId,
  artifact_value:
    CanonicalValue<ArtifactBytesType(profile_id)>,
  artifact_value_id:
    CanonicalValueId<"relations.artifact-bytes">(
      B, ArtifactBytesType(profile_id), artifact_value.datum)
}>

InterpretRelationArtifact(
  admitted RelationArtifactProfile,
  admitted ArtifactInterpreterContractV0 whose format and ordered
    (fact,value_type,max_count) fields equal the profile,
  exact ArtifactByteSourceBinding,
  exact K1 evaluator support, immutable dependency snapshot, and limits)
  -> Qualified<RelationArtifactObservation>
~~~

`Observed([])` means the interpreter read the field class and observed no
occurrence. `Unread` means it made no observation and is never evidence of
absence. Multiplicity is retained; repeated equal values do not collapse.
The exact admitted `interpreter` algorithm is evaluated only at the contract
ABI `artifact-bytes -> ArtifactInterpreterCompletionType(fields)`.
`Interpreted` must return exactly one entry
for every profile field and no others. Every `Observed` value has the field's
exact type and the observed sequence length is at most `max_count`; every count
is retained. A wrong type/key, extra field, or over-maximum output cannot be a
well-typed K1 completion; an evaluator implementation producing one is
`CheckerFailure`. `RejectedBytes`, unavailable evaluator support, budget
exhaustion, and unread source are qualified noncompletion. The
operation never emits semantic Negative.

`min_count` is checked by one closed profile-wide proposition so that an
honest `Observed([])` remains available as evidence of observed absence:

~~~text
ArtifactProfileCountQuestion = {
  profile_id: RelationArtifactProfileId,
  observation_id: RelationArtifactObservationId
}

ArtifactProfileCountQuestionId =
  RelationsId<"relations.artifact-profile-count-question">(
    B, ArtifactProfileCountQuestionBody)

ArtifactProfileCountManifest(question) =
  CanonicalSeq<every ArtifactFieldRef in the admitted profile's written order>

ArtifactProfileCountAgreement = CountAtLeastMinimum {
  field: ArtifactFieldRef,
  observed_count: Natural,
  minimum: Natural
}

ArtifactProfileCountDisagreement = CountBelowMinimum {
  field: ArtifactFieldRef,
  observed_count: Natural,
  minimum: Natural
}

CheckedArtifactProfileCounts = {
  question_id: ArtifactProfileCountQuestionId,
  manifest: CanonicalSeq<ArtifactFieldRef>,
  agreements: CanonicalSeq<ArtifactProfileCountAgreement>,
  disagreements: CanonicalSeq<ArtifactProfileCountDisagreement>
}

CheckArtifactProfileCounts(
  exact admitted ArtifactProfileCountQuestion,
  exact admitted RelationArtifactProfile,
  exact owner-issued RelationArtifactObservation,
  matching fresh interpretation-or-replay authority)
  -> Qualified<CheckedArtifactProfileCounts>
~~~

Question formation requires both nested IDs to authenticate, the
observation's `profile_id` to equal the question's `profile_id`, and no direct
module dependency; the nested subjects retain their own module closures. The
operation derives `ArtifactProfileCountManifest` itself. A caller cannot omit,
duplicate, reorder, or add a field. Any `Unread` field yields `CannotAnswer`
and no partial checked record. Otherwise the operation retains the exact
observed count and profile `min_count` for every field. All counts at or above
their minima produce Affirmative with an empty disagreement sequence; one or
more below-minimum counts produce Negative with every unaffected agreement
retained. Interpretation continues to own exact key/type/maximum checks and
this operation never changes the observation.

The checked record and its fresh capability bind the exact question,
observation, byte-source authority, interpreter, and complete derived
manifest. Serialized question, observation, or result bytes are inert.
Replay reauthenticates the profile and bytes, reruns the same interpreter to
obtain fresh observation authority, and reruns the complete count
question. Equal IDs or equal field values under another source binding do not
recreate authority.

The observation's `artifact_value_id` must equal the exact ID recomputed in the
supplied `ArtifactByteSourceBinding`; the absent raw byte field is never
invented during observation formation. The observation repeats the exact
profile ID, byte value ID, and interpreter declaration from the source and
invocation; `used_modules` is their exact
direct module set. `ReplayRelationArtifactObservation` reauthenticates the
profile, declaration and bytes, reissues a fresh read, reruns the same
contract algorithm under adequate limits, and compares the complete observation
body including every `Unread`/`Observed` tag, value, order, and multiplicity.
Only an affirmative replay result recreates checked observation authority. An
observation ID or equal bytes under another source binding does not.

### 9.3 Selectors and comparison

~~~text
ArtifactFactSelector =
    At(ArtifactFieldRef, occurrence_ordinal)
  | Whole(ArtifactFieldRef)

ArtifactSelectorType(At(field,_)) = ArtifactFieldValueType(field)
ArtifactSelectorType(Whole(field)) =
  RootSeq<ArtifactFieldValueType(field), ArtifactFieldMaximum(field)>

ArtifactSelectorClass(At(field,_)) = ArtifactFieldClass(field)
ArtifactSelectorClass(Whole(field)) = ArtifactFieldClass(field)

RelationFactSelector =
    DefinitionId(RelationDefinitionId)
  | DefinitionPayload(RelationDefinitionId, TypedValueSelector)
  | InterfaceId(RelationInterfaceId)
  | PublicType(RelationPublicRef)
  | WitnessType(RelationWitnessRef)
  | OraclePublicBindingType(RelationOracleRef)
  | OracleMaterialType(RelationOracleRef)
  | OracleIndexType(RelationOracleRef)
  | OracleAnswerType(RelationOracleRef)
  | PhaseType(RelationPhaseRef)

RelationFactSelectorClass(DefinitionPayload(_,_)) = SemanticValueFact
RelationFactSelectorClass(any other arm) = StructuralMetaFact

RelationFactSelectorType(DefinitionPayload(d,p)) =
  SelectedValueType(DefinitionPayloadType(d), p)
RelationFactSelectorType(any structural arm) =
  RelationsStructuralFactTypeV0(B)

RelationFactStructuralBody(DefinitionId(d)) = O(ContentRefV0(d))
RelationFactStructuralBody(InterfaceId(i)) = O(ContentRefV0(i))
RelationFactStructuralBody(PublicType(r)) =
  CanonicalValueTypeBody(ResolvedPublicDecl(r).value_type)
RelationFactStructuralBody(WitnessType(r)) =
  CanonicalValueTypeBody(ResolvedWitnessDecl(r).value_type)
RelationFactStructuralBody(OraclePublicBindingType(r)) =
  CanonicalValueTypeBody(ResolvedOracleDecl(r).public_binding_type)
RelationFactStructuralBody(OracleMaterialType(r)) =
  CanonicalValueTypeBody(ResolvedOracleDecl(r).material_type)
RelationFactStructuralBody(OracleIndexType(r)) =
  CanonicalValueTypeBody(ResolvedOracleDecl(r).index_type)
RelationFactStructuralBody(OracleAnswerType(r)) =
  CanonicalValueTypeBody(ResolvedOracleDecl(r).answer_type)
RelationFactStructuralBody(PhaseType(r)) =
  CanonicalValueTypeBody(ResolvedPhaseDecl(r).value_type)

RelationFactSelectorValue(DefinitionPayload(d,p)) =
  SelectCanonicalValue(AdmittedRelationDefinition(d).payload, p)
    // Available(CanonicalValue<RelationFactSelectorType(...)>) | CaseAbsent
RelationFactSelectorValue(s where RelationFactSelectorClass(s)
                                  = StructuralMetaFact) =
  Available(CanonicalValue<RelationsStructuralFactTypeV0(B)>(
    O(M(RelationFactStructuralBody(s)))))

ArtifactComparisonClause =
    StructuralMetaEquality {
      artifact: ArtifactFactSelector selecting StructuralMetaFact,
      relation: RelationFactSelector selecting StructuralMetaFact
    }
  | SemanticValueComparison {
      artifact: ArtifactFactSelector selecting SemanticValueFact,
      relation: RelationFactSelector selecting SemanticValueFact,
      value_relation: ValueRelation
    }

ArtifactComparisonQuestion = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  clauses: NonEmptyCanonicalSeq<ArtifactComparisonClause>
}

ArtifactComparisonQuestionId =
  RelationsId<"relations.artifact-comparison-question">(
    B, ArtifactComparisonQuestionBody)
~~~

Every selector function above is total after owner, reference, and typed-path
admission. Reference ordinals must resolve in the selected admitted definition
or Interface; `SelectedValueType` walks the complete K1 schema and enforces the
Section 3.2 path bounds. `SelectCanonicalValue` returns `CaseAbsent` only for a
well-typed path through a different active variant; it cannot return a value of
another type. `RelationFactStructuralBody` is a closed total function over only
the written structural selector arms. It admits no arbitrary `MetaValueV0`
input, and formation requires its encoded owner reference or value-type body to
fit the structural-fact carrier.

Every admitted artifact fact derives the exact result class and type. `At`
requires its ordinal to be below the field's declared `max_count`; `Whole`
returns the complete ordered observed sequence with the exact bounded K1
sequence type above. Clause admission requires equal selector classes. A
`StructuralMetaEquality` additionally requires
`ArtifactSelectorType(artifact) = RelationFactSelectorType(relation)` and uses
K1 equality at that exact carrier. A `SemanticValueComparison` requires the
artifact and relation selector types to be the exact endpoints of its written
`ValueRelation` direction. `DefinitionPayload` is the one K3-B relation-side
semantic-value source; every other arm returns the structural carrier over its
exact canonical owner reference or value-type body. An `Unread` selected field
yields `CannotAnswer`; `CaseAbsent`, an observed absence, or a completed
inequality is Negative. The checked result is field-factored and says nothing
about unrequested fields, artifact provenance, relation truth, or any law
beyond its exact clause.

## 10. Typed grounding equations

### 10.1 Value sources

~~~text
GroundingInstanceSlotDecl = { interface_id: RelationInterfaceId }
GroundingArtifactSlotDecl = { profile_id: RelationArtifactProfileId }
GroundingRunSlotDecl = { protocol_id: ProtocolId }

GroundingInstanceSlotRef = canonical ordinal in `instance_slots`
GroundingArtifactSlotRef = canonical ordinal in `artifact_slots`
GroundingRunSlotRef = canonical ordinal in `run_slots`

GroundingSourceSelector =
    InstancePublic(GroundingInstanceSlotRef,
                   RelationPublicRef, TypedValueSelector)
  | InstanceOracleBinding(GroundingInstanceSlotRef,
                          RelationOracleRef, TypedValueSelector)
  | InstancePhase(GroundingInstanceSlotRef,
                  RelationPhaseRef, TypedValueSelector)
  | WitnessValue(GroundingInstanceSlotRef,
                 RelationWitnessRef, TypedValueSelector)
  | OracleMaterialValue(GroundingInstanceSlotRef,
                        RelationOracleRef, TypedValueSelector)
  | ArtifactFact(GroundingArtifactSlotRef, ArtifactFactSelector)
  | ProtocolValue(GroundingRunSlotRef,
                  ProtocolValueCoordinate, TypedValueSelector)
  | Constant(CanonicalValue)

GroundingOperandSource =
    RelationInstance(RelationInstanceId)
  | WitnessOccurrence(PrivateWitnessAssignment)
  | OracleMaterialOccurrence(OracleMaterialAssignment)
  | ArtifactObservation(RelationArtifactObservationId)
  | QualifiedRun(RelationRunView)

GroundingOperandSlot =
    InstanceSlot(GroundingInstanceSlotRef)
  | WitnessSlot(GroundingInstanceSlotRef)
  | OracleMaterialSlot(GroundingInstanceSlotRef)
  | ArtifactSlot(GroundingArtifactSlotRef)
  | RunSlot(GroundingRunSlotRef)

GroundingOperandSlotForSource(InstancePublic(slot,_,_)) = InstanceSlot(slot)
GroundingOperandSlotForSource(InstanceOracleBinding(slot,_,_)) =
  InstanceSlot(slot)
GroundingOperandSlotForSource(InstancePhase(slot,_,_)) = InstanceSlot(slot)
GroundingOperandSlotForSource(WitnessValue(slot,_,_)) = WitnessSlot(slot)
GroundingOperandSlotForSource(OracleMaterialValue(slot,_,_)) =
  OracleMaterialSlot(slot)
GroundingOperandSlotForSource(ArtifactFact(slot,_)) = ArtifactSlot(slot)
GroundingOperandSlotForSource(ProtocolValue(slot,_,_)) = RunSlot(slot)
GroundingOperandSlotForSource(Constant(_)) = None

RequiredGroundingOperandSlots(equation) =
  the canonical set of nonconstant owner slots derived from every selector

GroundingInvocation = {
  equation_id: GroundingEquationId,
  operands:
    ExactMap<GroundingOperandSlot, GroundingOperandSource>
}
~~~

`GroundingEquation` contains selectors, never a run, instance, observation, or
secret occurrence. `GroundingInvocation` supplies those operands later under
the exact checked question. Witness and oracle-material selectors may appear
only in a confidential owner-local invocation. Portable results cannot
serialize or cold-replay their premise.

### 10.2 Acyclic equation DAG

~~~text
GroundingValueRef = Source(source_ordinal) | Step(step_ordinal)

GroundingStep = {
  inputs: CanonicalSeq<GroundingValueRef>,
  output_type: ValueType,
  algorithm: PortableAlgorithmRef
}

GroundingEquality = {
  left: GroundingValueRef,
  right: GroundingValueRef,
  value_type: ValueType
}

GroundingEquation = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  instance_slots: CanonicalSeq<GroundingInstanceSlotDecl>,
  artifact_slots: CanonicalSeq<GroundingArtifactSlotDecl>,
  run_slots: CanonicalSeq<GroundingRunSlotDecl>,
  sources: NonEmptyCanonicalSeq<GroundingSourceSelector>,
  steps: CanonicalSeq<GroundingStep>,
  equalities: NonEmptyCanonicalSeq<GroundingEquality>
}

GroundingEquationId =
  RelationsId<"relations.grounding-equation">(B, GroundingEquationBody)

GroundingSourceType(e,InstancePublic(slot,r,p)) =
  SelectedValueType(ResolvedPublicDecl(r).value_type,p)
GroundingSourceType(e,InstanceOracleBinding(slot,r,p)) =
  SelectedValueType(ResolvedOracleDecl(r).public_binding_type,p)
GroundingSourceType(e,InstancePhase(slot,r,p)) =
  SelectedValueType(ResolvedPhaseDecl(r).value_type,p)
GroundingSourceType(e,WitnessValue(slot,r,p)) =
  SelectedValueType(ResolvedWitnessDecl(r).value_type,p)
GroundingSourceType(e,OracleMaterialValue(slot,r,p)) =
  SelectedValueType(ResolvedOracleDecl(r).material_type,p)
GroundingSourceType(e,ArtifactFact(slot,s)) = ArtifactSelectorType(s)
GroundingSourceType(e,ProtocolValue(slot,c,p)) =
  SelectedValueType(
    ProtocolCoordinateValueType(e.run_slots[slot].protocol_id,c),p)
GroundingSourceType(e,Constant(v:CanonicalValue<T>)) = T

GroundingOutputCoordinate = {
  equation_id: GroundingEquationId,
  value: GroundingValueRef
}

GroundingValueType(equation, Source(k)) =
  GroundingSourceType(equation,equation.sources[k])
GroundingValueType(equation, Step(k)) =
  equation.steps[k].output_type

GroundingInputType(equation,inputs) =
  RootRecord<[(i,GroundingValueType(equation,inputs[i]))
              for every input ordinal i in written order]>

GroundingEqualityAgreement = EqualityTrue(equality_ordinal)
GroundingEqualityDisagreement = EqualityFalse(equality_ordinal)

CheckedGroundingEvaluation = {
  equation_id: GroundingEquationId,
  agreements: CanonicalSeq<GroundingEqualityAgreement>,
  disagreements: CanonicalSeq<GroundingEqualityDisagreement>
}

EvaluateGroundingEquation(
  exact admitted GroundingEquation,
  exact GroundingInvocation,
  every required exact source-authority binding and matching fresh source
    capability,
  exact K1 evaluator support, immutable dependency snapshot, and limits)
  -> Qualified<CheckedGroundingEvaluation>
~~~

Sources are read in sequence. Steps are topologically ordered and may cite
only sources or earlier steps. Each step algorithm is admitted as the exact
same-regime total ABI
`GroundingInputType(equation,step.inputs) -> step.output_type`, with the input
record in written input order and an empty failure row.
Equalities are evaluated in sequence under K1 same-type equality. Algorithms
used directly in an equation must complete on every admitted input; a
meaningful partial condition is encoded as an ordinary tagged result value or
Boolean predicate, not as an operational failure.

Each `GroundingSourceType` case is defined only when its slot ordinal is in
bounds, the slot's Interface/profile/Protocol equals the referenced owner, the
reference and selector resolve, and the selected Protocol coordinate is
value-producing. Any owner mismatch, out-of-range ordinal, structural
Protocol coordinate, or wrong selector refuses equation formation rather than
leaving a dynamically asserted type.

An `ArtifactFact` source must select a `SemanticValueFact`; structural
meta-facts cannot enter a value DAG. A `ProtocolValue` source must resolve one
exact available canonical value through the imported run view. The equation's
`used_modules` equals the direct modules of all slot Interfaces/profiles,
source and step types, algorithms, and constants.

The invocation's operand-key set equals
`RequiredGroundingOperandSlots(equation)`. The operation receives every
operand's exact inert source binding and a separately fresh capability; those
live inputs are not fields of the equation or invocation. Every relation
selector resolves through the one exact
instance and, where requested, its same-instance local assignments. Every
artifact selector resolves through an observation with the named profile.
Every Protocol selector resolves through the one exact run view. Mixing
instances, runs, profiles, generations, or authority bindings refuses before
evaluation.

Every equality true is Affirmative. Any false equality is Negative and names
the exact clause plus unaffected equalities. Missing or unread sources,
unsupported evaluation, K1 `DomainFailure`, authority failure, and operational
limit failure are qualified noncompletion, never false equality.

`GroundingOutputCoordinate` formation authenticates its equation, resolves the
written source or step ordinal, and derives the exact type above; a caller
cannot supply a type. `EvaluateGroundingEquation` is the owner-level operation
used by the companion correspondence checker as well as by the lossy-use path
below. Its fresh checked capability retains the exact invocation, every source
binding and generation, and the complete computed value table; the portable
result record retains only equality facts. An affirmative capability permits
an owner-local `ReadGroundingOutput` at a matching coordinate and yields the
one computed `CanonicalValue<GroundingValueType>` under that same authority.
A result record, coordinate, equal value, or negative evaluation cannot mint
that read. Confidential source or intermediate values are never serialized.

The lossy-use path is closed as follows:

`AdmittedGroundingEquation` and `AdmittedValueBridge` below are the exact
owner-issued admitted-subject views of those already defined subject families.
`AdmittedRelationsDeclaration<K>` is the owner-local admitted-declaration view
issued by `AdmitRelationsDeclaration` for exact kind `K`. These are input-view
aliases with matching fresh admission capabilities, not new durable subjects
or identity constructors.

~~~text
LossyUsePremiseBinding = {
  use_coordinate: BridgeUseCoordinate,
  source_anchor_ordinal: Natural,
  premise_output: GroundingOutputCoordinate
}

LossyUsePremiseRequest = {
  binding: LossyUsePremiseBinding,
  invocation: GroundingInvocation
}

LossyGroundingAdmissionSet =
  ExactMap<GroundingEquationId, AdmittedGroundingEquation>

LossyBridgeSemanticAdmission = {
  bridge: AdmittedValueBridge,
  source_premise:
    AdmittedRelationsDeclaration<"relations.loss-source-premise">,
  quantitative_export:
    AdmittedRelationsDeclaration<"relations.loss-export">
}

LossyBridgeSemanticAdmissionSet =
  ExactMap<ValueBridgeId, LossyBridgeSemanticAdmission>

LossySourceSelector(equations,request) =
  equations[request.binding.premise_output.equation_id]
    .sources[request.binding.source_anchor_ordinal]

LossySourceOccurrence(equations,request) =
  request.invocation.operands[
    GroundingOperandSlotForSource(LossySourceSelector(equations,request))]

LossySourceAuthorityBinding =
    RelationInstanceFieldSource {
      endpoint:
        RelationPublicValue | RelationPhaseValue |
        RelationOraclePublicBindingValue,
      instance_id: RelationInstanceId,
      consumer: RelationsDownstreamCoordinate,
      purpose: RelationsDownstreamCoordinate,
      authority:
        exact PortableSourceAuthorityBinding satisfying
          RelationsSourceAuthorityBindingMatches(
            "relation-instance-field",
            InstanceSource(instance_id),
            InstanceField(endpoint),
            consumer,
            purpose,
            authority)
    }
  | PrivateWitnessFieldSource {
      endpoint: RelationWitnessValue,
      instance_id: RelationInstanceId,
      assignment_occurrence: PrivateWitnessAssignment,
      consumer: RelationsDownstreamCoordinate,
      purpose: RelationsDownstreamCoordinate,
      authority:
        exact OwnerLocalSourceAuthorityBinding satisfying
          RelationsSourceAuthorityBindingMatches(
            "private-witness-field",
            PrivateWitnessSource(instance_id),
            PrivateWitnessField(endpoint),
            consumer,
            purpose,
            authority)
    }
  | ArtifactObservationFieldSource {
      endpoint: ArtifactValue,
      observation_id: RelationArtifactObservationId,
      consumer: RelationsDownstreamCoordinate,
      purpose: RelationsDownstreamCoordinate,
      authority:
        exact PortableSourceAuthorityBinding satisfying
          RelationsSourceAuthorityBindingMatches(
            "artifact-observation-field",
            ArtifactObservationSource(observation_id),
            ArtifactObservationField(endpoint),
            consumer,
            purpose,
            authority)
    }

LossySourceBinding =
  owner-local nonserializable association of {
    use_coordinate: BridgeUseCoordinate,
    source_endpoint: BridgeUseEndpoint,
    operand_source: GroundingOperandSource,
    exact_source_authority_binding: LossySourceAuthorityBinding,
    exact owner occurrence, process generation, and fresh capability
      association
  }

LossyUseSelection = {
  bridge_use_set: BridgeUseSet,
  coordinates: CanonicalSortedUniqueSeq<BridgeUseCoordinate>
}

SelectedBridgeUseCardinality(selection,b) =
  the derived number of selection.coordinates whose checked use names b

LossyUsePremiseRequestSet =
  ExactMap<BridgeUseCoordinate, LossyUsePremiseRequest>

RelationsCheckedLossyUseFactV0 = {
  bridge_id: ValueBridgeId,
  use_coordinate: BridgeUseCoordinate,
  premise_output: GroundingOutputCoordinate,
  source_anchor_ordinal: Natural
}

RelationsCheckedLossyUseFactBodyV0(f) =
  R {0:Q("zkc.relations.checked-lossy-use.v0"), 1:RB(f)}

RelationsCheckedLossyUseFactValue(f) =
  CanonicalValue<RelationsCheckedLossyUseFactTypeV0(B)>(
    O(M(RelationsCheckedLossyUseFactBodyV0(f))))

CheckedLossyUseExport = {
  use: CheckedBridgeUse,
  binding: LossyUsePremiseBinding,
  checked_use_fact:
    CanonicalValue<RelationsCheckedLossyUseFactTypeV0(B)>,
  exported_fact:
    CanonicalValue<LossExportedFactType(use.bridge_id)>
}

LossyUsePremiseDisagreement =
    GroundingEqualityFalse(BridgeUseCoordinate, equality_ordinal)
  | AnchorMismatch(BridgeUseCoordinate)
  | PremisePredicateFalse(BridgeUseCoordinate)

CheckedLossyUsePremiseSet = {
  selection: LossyUseSelection,
  bindings: ExactMap<BridgeUseCoordinate, LossyUsePremiseBinding>,
  agreements: CanonicalSeq<CheckedLossyUseExport>,
  disagreements: CanonicalSeq<LossyUsePremiseDisagreement>
}

CheckLossyUsePremises(
  exact LossyUseSelection,
  matching fresh affirmative authority for its exact bridge_use_set,
  exact source consumer and purpose RelationsDownstreamCoordinate values
    fixed by the consuming operation,
  exact LossyUsePremiseRequestSet,
  exact LossyGroundingAdmissionSet and matching fresh admission capabilities,
  exact LossyBridgeSemanticAdmissionSet and matching fresh admission
    capabilities,
  every required exact grounding source-authority binding and matching fresh
    source capability,
  exact LossySourceAuthorityBinding for every source anchor, identical to the
    matching grounding source-authority binding,
  exact K1 evaluator support, immutable dependency snapshot, and limits)
  -> Qualified<CheckedLossyUsePremiseSet>

CheckedLossyUseConsumerSource = {
  use_coordinate: BridgeUseCoordinate,
  premise_binding: LossyUsePremiseBinding,
  exact_source_authority_binding: LossySourceAuthorityBinding
}

CheckLossyUseAtConsumerSource(
  exact overall-Affirmative CheckedLossyUsePremiseSet and fresh capability,
  exact lossy BridgeUseCoordinate in that set,
  exact source consumer and purpose RelationsDownstreamCoordinate values
    fixed by this consumer,
  exact consumer-issued LossySourceAuthorityBinding and matching fresh source
    capability)
  -> Qualified<CheckedLossyUseConsumerSource>
~~~

The three arms select the exact Relations source-authority vocabulary from
[Protocol Correspondence, Section 4.3](protocol-correspondence.md#43-exact-relations-source-authority-subjects).
There is no `ExactSourceAuthorityBinding`,
`ExactAdmittedSubjectAuthorityBinding`, or lossy-specific carrier beyond the
one Foundation envelope and the written owner predicate.

The instance arm is portable because an admitted `RelationInstanceId`
content-addresses all of its public, phase, and Oracle-public-binding values;
the payload additionally commits to the one exact typed endpoint. The artifact
arm is portable because an admitted `RelationArtifactObservationId`
content-addresses the complete expectation-free observation, while the
payload commits to the selected artifact endpoint. Both portable bindings are
inert: cold use must reauthenticate the complete subject and obtain a fresh
matching owner capability. The private-witness arm is necessarily owner-local
because `PrivateWitnessAssignment` is an `OwnerLocalOccurrence`; its semantic
payload commits only to the instance and typed witness endpoint, while the Foundation
local coordinate and live capability retain the exact assignment occurrence,
secret-value capability, and process generation. Equal secret values or a
reconstructed envelope cannot change that constraint.

This selection closes the semantic portability and body-shape question for
these three source families. It does not claim executable implementation or
native protocol coverage of the lossy-use lane. The bounded Schnorr witness
did not execute this lane; native IOP/IOR, folding, and concrete lossy-
projection pressure remain required before a broader evidence or freeze claim.

For an admitted lossy bridge `b`, `LossPremiseInputType(b)` and
`LossPremiseAnchorType(b)` are exactly the lifted `premise_input_type` and
`source_anchor_type` of `b.lane.source_premise`; the latter equals
`b.source_type` by bridge admission. `LossExportedFactType(b)` is exactly the
lifted `exported_fact_type` of `b.lane.quantitative_export`. All three functions
require those exact admitted declarations and the bridge-use-set capability's
retained fresh affirmative law-basis authority.

Every selected coordinate must name an exact lossy entry in
`selection.bridge_use_set`; a non-lossy, absent, or duplicate coordinate is
malformed. The request-map key set is every and only
`selection.coordinates`. Each key equals `binding.use_coordinate`; the invocation and
`binding.premise_output` name the same authenticated equation. The selected
output is well formed and has exact type `LossPremiseInputType(b)`. It may be a
separate source or derived step: for example, a preimage-valued premise output
and a digest-valued source anchor need not have the same type or a directed
dataflow edge between them. Their value binding is established by the
contract-owned anchor comparison below.

The grounding-admission key set is every and only distinct equation ID in the
request map. The bridge-semantic-admission key set is every and only distinct
lossy bridge ID in the selection. Each admitted bridge body and its two
admitted declarations must equal the references resolved from that key; every
map is extra-key-free, and each admission result has a separately matching
fresh capability. Neither an ID nor the bridge-use-set result substitutes for
these semantic admission inputs.
The consuming operation, not the source caller, fixes the exact downstream
consumer and purpose coordinates. Every source arm and live capability in the
request set must bind those identical coordinates; a mixed set or caller-
selected substitute is `Refused` before premise evaluation.
The completed result's `bindings` map is copied mechanically from the request
map over that same exact key domain. It therefore retains the equation, output,
and source anchor for Affirmative and Negative alike; disagreement tags cannot
erase which premise was tested. That portable map contains no invocation or
secret occurrence. Evaluation uses the complete owner-local request and source
inputs, but only an overall-Affirmative completion atomically creates and
retains an exact map from every use coordinate to a live `LossySourceBinding`
in its fresh capability. A Negative capability retains the checked
disagreements but no consumer-usable source binding. Neither live map appears
in the portable result, has an `RB` case, or can be recreated from the record.

The anchor must also be the exact static source endpoint of that use. Because
lossy use is forward-only, the source is `use.left_endpoint`. The closed match
is:

| bridge source endpoint | exact equation source at the anchor |
|---|---|
| `RelationPublicValue(r,p)` | `InstancePublic(slot,r,p)` where the slot Interface is `r.owner_id` |
| `RelationPhaseValue(r,p)` | `InstancePhase(slot,r,p)` where the slot Interface is `r.owner_id` |
| `RelationOraclePublicBindingValue(r,p)` | `InstanceOracleBinding(slot,r,p)` where the slot Interface is `r.owner_id` |
| `RelationWitnessValue(r,p)` | `WitnessValue(slot,r,p)` where the slot Interface is `r.owner_id` |
| `ArtifactValue(s)` | `ArtifactFact(slot,s)` where the slot profile is the owner of `s` |

No other pair matches. In particular, equal types, equal values, another
instance slot, another artifact observation, a constant, or an unbound run
source cannot anchor the use.
`LossySourceOccurrence(equations,request)` is the exact
`GroundingOperandSource` selected by that anchor's slot in the request's
`GroundingInvocation`; it is inert and grants no authority. The checker
combines it with the source owner's exact K1 binding satisfying the selected
`RelationsSourceAuthorityBindingMatches` predicate and matching fresh
`RelationsLiveSourceAuthorityMatches` capability to create the live
`LossySourceBinding`, retaining the exact endpoint, owner, occurrence,
capability family, and process generation.
The endpoint selects exactly one `LossySourceAuthorityBinding` arm. Its
`instance_id`, `assignment_occurrence`, or `observation_id` must equal the
corresponding `RelationInstance`, `WitnessOccurrence`, or
`ArtifactObservation` operand returned above; for the witness arm the exact
owner-associated assignment body must also name that `instance_id`. Its
endpoint including the typed selector must equal `use.left_endpoint`. Any
cross-arm, occurrence, instance, or field mismatch is `Refused`, not a value
disagreement.
This is an independently explicit source-occurrence context, so a guarded
target need not have executed merely to form the conservative static-site
check. A later run-grounded consumer may use it only after requiring complete
source-binding equality with the occurrence that consumer actually read.
Selector, ID, or value equality alone is insufficient.

For each request, Relations runs `EvaluateGroundingEquation`. A false grounding
equality records the exact use and equality disagreement. Only an affirmative
evaluation permits `ReadGroundingOutput` of both
`binding.premise_output` and the exact
`GroundingOutputCoordinate(equation_id,
Source(binding.source_anchor_ordinal))` under the same live authority.
Relations evaluates the contract-owned `anchor` algorithm on the premise
value and compares its `LossPremiseAnchorType(b)` output by exact K1 equality
with that source value. Inequality is `AnchorMismatch`; only equality permits
the exact admitted source-premise predicate to run on the complete premise
value. Predicate false is `PremisePredicateFalse`. On true, Relations
constructs the one domain-tagged checked-use value above and evaluates the
exact admitted loss-export algorithm on that value. No module-selected
anchor, checked-use type, or encoder participates.
Fact formation requires `M(RelationsCheckedLossyUseFactBodyV0(f))` to fit the
fixed bounded carrier, strict decoding to consume all bytes, and re-encoding to
reproduce the identical body.
Evaluation unavailability, a missing source, false authority, or limit
exhaustion remains its qualified noncompletion class and produces no partial
checked set.

An overall Affirmative has one agreement and export for every selected key and
no disagreements. A Negative retains completed unaffected agreements and every
exact disagreement, but its capability authorizes no quantitative aggregation.
`SelectedBridgeUseCardinality(selection,b)` is only a candidate derived count:
a value-consuming owner must first establish that the selection is exactly its
complete relevant-use set and obtain a fresh consumer-source join for every
coordinate. At K3-B only the fresh overall-Affirmative run-grounded
checked-result capability retaining those exact joins licenses Analysis to
consume that selected count.
The wider `BridgeUseCardinality` remains a structural inventory number and has
no quantitative authority. Exported canonical values alone are inert.

`CheckLossyUseAtConsumerSource` is the only consumer join. It retrieves the
live `LossySourceBinding` for the exact coordinate from the overall-Affirmative
capability, authenticates the consumer's exact K1 binding under the same
Relations source-authority predicate, and requires complete binding equality plus
equality of the two live associations: owner, selected endpoint/field
coordinate, local occurrence where applicable, process generation, capability
family/ABI, and authority lifetime. A mismatch is `Refused`, a missing or
expired capability is `CannotAnswer`, and neither becomes semantic Negative.
Success creates a fresh owner-local join capability for that one use and
consumer source. The checked record has no semantic ID or `RB` case, and record
equality cannot replace either input capability.

Replay reauthenticates every subject and declaration, recreates the exact
bridge-use set and selection, reacquires fresh occurrence/source capabilities, reruns the
grounding DAG and equalities, reads the selected output and anchored source,
and reruns the contract-owned anchor, exact K1 comparison, premise predicate,
and export algorithm, then reruns the consumer join when one is required.
Equal checked-use or exported bytes do not recreate occurrence authority,
selection authority, consumer-join authority, or a quantitative claim.

### 10.3 Commitment grounding is not a value bridge

~~~text
RelationMaterialSource =
    PublicMaterial(RelationPublicRef, TypedValueSelector)
  | WitnessMaterial(RelationWitnessRef, TypedValueSelector)
  | OracleMaterial(RelationOracleRef, TypedValueSelector)

ProtocolPublicationTarget =
    PublishedValue(OccurrenceRef, output_ordinal,
                   TypedValueSelector)
  | OraclePublicationValue(OracleRef, OccurrenceRef,
                           TypedValueSelector)

CommitmentGrounding = {
  used_modules: CanonicalSortedUniqueSeq<SemanticModuleId>,
  relation_material: NonEmptyCanonicalSeq<{
    construction_input_ordinal: Natural,
    material: RelationMaterialSource,
    equation_source_ordinal: Natural
  }>,
  protocol_publication: {
    target: ProtocolPublicationTarget,
    equation_source_ordinal: Natural
  },
  construction:
    ModuleDeclarationRef<"relations.commitment-construction">,
  equation_id: GroundingEquationId,
  construction_step_ordinal: Natural,
  construction_equality_ordinal: Natural
}

CommitmentGroundingId =
  RelationsId<"relations.commitment-grounding">(
    B, CommitmentGroundingBody)
~~~

The admitted construction contract's material-type sequence equals the
selected material types in `construction_input_ordinal` order and its
commitment type equals the publication target type. Material ordinals are
exactly `0..n-1`. Each material's equation source is unique and is exactly the
corresponding `InstancePublic`, `WitnessValue`, or `OracleMaterialValue`
selector with the identical relation ref and selector. The publication source
is unique and exactly `ProtocolValue(run-slot,publication-coordinate,selector)`
for the identical target.

The referenced equation has exactly those `n+1` sources, no additional source,
one step, and one equality. The named step is that sole step; its inputs are
the material source refs in construction order, its algorithm is exactly the
admitted contract's `construct`, and its output type is the commitment type.
The named equality is the sole equality and compares exactly that step output
with the publication source at that same type, in either written side order.
Its instance/run slot set is therefore exactly the set mechanically required
by those selectors, with no unused slot. These closure rules connect every
field of `CommitmentGrounding` to one exact equation position; none is
decorative.

The checked equation may establish that one exact run publication equals the
declared construction over exact relation material. It does not establish
commitment binding, hiding, extractability, opening knowledge, or the
soundness of a Protocol check. Those require separate Analysis judgments.

Opening messages and checks are deliberately absent from
`CommitmentGrounding`: K3-B has not selected a general opening-security
contract. FRI/IOR opening correspondence remains an explicit post-K3-B K4 P02
gate rather than an unsupported claim carried by unconnected lists.

A commitment is deliberately not modeled as a lossy projection: material and
commitment have different semantic roles, and cryptographic binding is not a
representation inverse law. FRI roots, Nova accumulator commitments, and
module-effect publications use typed K2 publication occurrences rather than a
generic object carrier.

## 11. Structural and run-grounded judgments

### 11.1 Nonduplicated question families

| Question | Exact proposition | Deliberate non-claim |
|---|---|---|
| `MappedStatementCorrespondence` | Requested Statement edges resolve and their types/value relations agree | Whole Statement coverage or runtime equality |
| `WholeRelationPublicCoverage` | Every requested relation public occurrence is covered under the fixed `ExactNonoverlappingCover`/`SelectorPartition` law | Whole Protocol Statement coverage |
| `WholeStatementCoverage` | Requested edge endpoints exactly cover the selected complete Statement surface | External Interface completeness |
| `MappedPlanWitnessCorrespondence` | Requested witness edges resolve to exact PIR surface entries | Secret possession or satisfaction |
| `WholeRelationWitnessCoverage` | Every relation witness occurrence has the requested Plan source coverage | Every private Plan input is a witness |
| `WholePlanWitnessSurfaceCoverage` | Every exported witness-surface entry has the requested relation coverage | Full private Plan coverage |
| `ClaimReductionShape` | Claims, order, contracts, recipes, transform ABI, challenges, and publications match K2 | Reduction theorem or witness evolution |
| `ArtifactInterfaceComparison` | Requested observed fields agree or disagree with requested relation facts | Artifact provenance or relation truth |
| `GroundingEquationHolds` | Exact typed runtime/artifact/relation operands satisfy the equation | Cryptographic faithfulness beyond the equation |
| `CommitmentGroundingHolds` | Exact relation material and exact publication occurrence satisfy the construction equation | Binding, hiding, or extraction |
| `RunGroundedCorrespondence` | One qualified run's selected values and occurrences agree with one exact instance/binding | Universal protocol behavior or satisfaction |
| `RelationSatisfaction` | One confidential occurrence evaluates true or false under one exact model | Protocol acceptance or security |
| `RelationRefinement` | One exact directional relation proposition holds under its basis | Probabilistic protocol reduction |

Admission checks only K1 formation, resolvable typed coordinates, finite
bounds, exact dependencies, and question grammar. It does not precompute the
question's substantive equality, coverage, or refinement predicate. Thus each
completed result family retains a constructible Negative as required by R-08.
A reference to the wrong owner/kind or an ill-typed selector is malformed; a
well-formed edge to an allowed but non-covering occurrence remains available
for a negative coverage result.

### 11.2 Exact run-grounding law

For every Statement edge `e : r -> b` selected by a run-grounding question:

~~~text
relation_value = Select(instance.public_values[r], e.relation.selector)
protocol_value = Select(run_view.binding_value[b], e.protocol.selector)

ApplyValueRelation(e.value_relation, relation_value, protocol_value)
  = true
~~~

The same law applies to phase edges and oracle public-binding edges with their
exact source families. Claim recipes derive exact input/output instance
occurrences from the selected run values before claim agreement is checked.
Commitment groundings evaluate their separate equation DAGs.

When a selected edge uses a lossy bridge, the run-grounded operation derives
the exact full `BridgeUseSet` and the owner-derived selection containing every
and only lossy coordinate selected by its `RelationBoundValue` checks. It
requires an overall-Affirmative `CheckedLossyUsePremiseSet` for that exact
selection and creates each consumer source binding from the exact
`RelationInstance` public/phase/Oracle-binding field and fresh authority used
by this question. It must then consume a fresh Affirmative
`CheckLossyUseAtConsumerSource` result for every coordinate in the selection.
That typed join, not prose value equality, establishes identical owner,
subject, field coordinate, occurrence/generation, capability family, and
authority lifetime. A different instance, generation, capability, or equal
field value is refused; an unavailable fresh binding is `CannotAnswer`. Only
the fresh overall-Affirmative run-grounded checked-result capability retaining
the exact complete selection and all join capabilities licenses its selected
use count. K3-B defines no analogous Plan or artifact consumer join; adding
one requires that operation's exact live source binding and cannot reuse this
result ambiently.

The checked result retains both occurrence coordinates even if values are
equal. A wrong value or wrong well-formed occurrence is Negative. A caller-
constructed value, missing PIR view, wrong source authority, unread artifact
field, unavailable secret premise, or incomplete manifest is respectively
refused or cannot answer, not Negative.

### 11.3 Result direction

`ClaimPresence`, `CheckTrue`, or an accepting terminal may be selected as a
structural Protocol fact. None means relation acceptance. The following are
distinct:

~~~text
structural result reference
relation satisfaction
Protocol acceptance at one run
completeness direction
soundness direction
full equivalence
~~~

Full equivalence requires separately established directions. No subtype rule
derives soundness from completeness, satisfaction from acceptance, or a
behavioral theorem from structural shape.

## 12. Pressure results and object disposition

| Case | Required representation | Consequence |
|---|---|---|
| Schnorr/Sigma | public statement `Y`, local witness `x`, separate nonce randomness, message occurrence `A`, initial claim, terminal | Relation witness cannot mean all private prover input; message occurrence needs no object wrapper |
| R1CS | structured public vector, witness assignment, constraint/artifact facts | Typed K1 values and selectors preserve order and multiplicity without scalar-port explosion |
| randomized AIR | public instance, trace/oracle material, post-commitment verifier challenges | `PhaseInput` is a first-class fourth role |
| FRI/IOR | public statement, logical oracle statement, publication/query/answer occurrences, opening messages/checks | `OracleStatement` and typed K2 Oracle/occurrence coordinates are required; K4 P02 retains full native-path validation |
| Nova/folding | ordered input claim-instance occurrences, cross-term publication, challenge, output accumulator instance, evolved witness | Claim/reduction correspondence is an occurrence graph plus relation transform; K4 P09 retains executable end-to-end validation |
| `sha256-216` | exact 256-to-216 directional uses and grounded source-preimage premise | A separate lossy lane and derived occurrence count are mandatory |

No reviewed case requires generic `ObjectRef` in K2 or Relations. Existing
typed coordinates cover verifier-observable material:

- `BindingRef` and `ValueRef` for public and derived values;
- `OccurrenceRef` plus output ordinal for messages and module effects;
- `OracleRef` plus publish/query/answer occurrences for logical oracles;
- `ChallengeRef`, `ClaimRef`, `ReductionRef`, `CheckRef`, and `TerminalRef` for
  their distinct structural roles; and
- typed relation-side material selectors for private or derived material.

A generic object would create an untyped shadow carrier, duplicate occurrence
identity, and invite commitment, message, oracle, and value semantics to be
conflated. Reopening it requires an executable supported case with verifier-
observable committed material that none of the typed coordinates can name. A
convenience wrapper, carrier label, or backend object is not such evidence.

## 13. Exact Relations body compiler

The identities above do not depend on a printer, host record layout, or an
undefined `Body` function. `RelationsBodyV0<T>` is the following total,
type-directed compiler into K1 `MetaValueV0`. It uses `U`, `MF`, `MT`, `N`,
`I`, `O`, `Q`, `S`, `R`, and `V` exactly as defined by K1.

For every complete algebra block in this file or its companion Relations
specifications, record fields are numbered
`0..n-1` in their written order and variant alternatives are tagged `0..n-1`
in their written order. Field names and type aliases are not encoded. Changing
field order, variant order, or any field type therefore changes the body
schema and rotates `RelationsProfile` plus every downstream profile that
imports it. A module-owned declaration change instead rotates that module and
its exact users. The shared Foundation semantic regime rotates only when a
Foundation-owned mechanism or its interpretation changes.

~~~text
RB(Unit)                    = U
RB(false)                   = MF
RB(true)                    = MT
RB(Natural n)               = N(n)
RB(Int z)                   = I(z)
RB(Bytes x)                 = O(x)
RB(MetaSymbol x)            = Q(x)

RB(SemanticContentId<K> x)  = O(ContentRefV0(x))
RB(PriorMetaId<K> x)        = O(PriorRefV0(x))
RB(DeclarationRef<K> x)     = DeclarationRefBody(x)
RB(DeclarationValueType x)  = DeclarationValueTypeBody(x)
RB(ValueType T)             = CanonicalValueTypeBody(T)
RB(CanonicalValue<T> x)     = R {0:CanonicalValueTypeBody(T),
                                  1:x.datum}

RB(Optional.None)           = V(0,U)
RB(Optional.Some(x))        = V(1,RB(x))
RB(Enum alternative i)      = V(i,U)
RB(Variant alternative i,x) = V(i,RB(x))

RB(Record {f0,...,fn-1})    = R {0:RB(f0),...,n-1:RB(fn-1)}
RB(Tuple (x0,...,xn-1))     = R {0:RB(x0),...,n-1:RB(xn-1)}
RB(Sequence [x0,...,xn-1])  = S[RB(x0),...,RB(xn-1)]

RB(CanonicalSet X) =
  S[RB(x)... sorted by M(RB(x)); duplicate encodings reject]

RB(CanonicalMap M) =
  S[R{0:RB(k),1:RB(v)} ...
    sorted by M(RB(k)); duplicate key encodings reject]
~~~

`CanonicalSeq`, `NonEmptyCanonicalSeq`, sorted-unique sequences, and total or
exact maps use the corresponding sequence/map rule after their independent
cardinality, ordering, key-domain, and totality checks. A
`TypedValueSelector` path is a variant followed by its ordered step sequence;
each step is its written-order variant with natural ordinal payload.
`RelationRef<S,R>` value `x` is
`R{0:O(ContentRefV0(x.owner_id)),1:RB(x.role),
2:N(x.canonical_ordinal)}`.
`WitnessSurfaceKey` uses its owner-defined K1 `MetaSymbol` body.
`PlanWitnessSurfaceId` and every durable K2 typed reference embedded in a
Relations body use the exact canonical body exported by their PIR owner;
Relations does not re-encode their fields. Durable Relations-owned
`ProtocolValueCoordinate`, `ProtocolStructuralSource`, and companion question
selector wrappers use their written-order `RB` variants and contain only those
exact typed references and selector data. At checking time the owner operation
derives the corresponding process-local `RelationRunCoordinate` and reads the
PIR-issued view. The live `RelationRunCoordinate`, read manifest,
`RelationRunView`, histories, and selected entries have no K1 canonical body or
`RB` case and never enter a durable identity preimage.

For a same-regime `PortableAlgorithmRef`, `RB` uses
`O(ContentRefV0(algorithm_id))`. There is no K3-B `RB` arm for a cross-regime
translation: such a request is `Unsupported` before Relations body formation.
Owner-local occurrences, capabilities, source
bindings, evaluator processes, observations without a declared durable ID,
and live extraction/run views have no `RB` case and therefore cannot enter a
durable identity preimage.

Law propositions use one exact owner carrier rather than an undefined encoder:

~~~text
RelationsLawPropositionV0 =
    DefinitionModelLawProposition {
      definition_id: RelationDefinitionId,
      semantic_model_id: RelationSemanticModelId
    }
  | RefinementLawProposition {
      transform_id: RelationTransformId,
      direction: RelationRefinementDirection,
      input_models: TotalMap<input_ordinal,RelationSemanticModelId>,
      output_models: TotalMap<output_ordinal,RelationSemanticModelId>
    }
  | BridgeLawPropositionValue(BridgeLawProposition)

RelationsLawPropositionBodyV0(p) =
  R {0:Q("zkc.relations.law-proposition.v0"), 1:RB(p)}

RelationsPropositionTypeV0(B) =
  RootBytes[0,2^20] in B

RelationsPropositionValue(p) =
  CanonicalValue<RelationsPropositionTypeV0(B)>(
    O(M(RelationsLawPropositionBodyV0(p))))
~~~

The three variant tags and every record field use the written order. Formation
checks that the encoded bytes strictly decode to that one body, consume all
bytes, re-encode identically, and fit the exact proposition type. A law
contract whose lifted proposition type differs is refused. Thus a certificate
verifier receives the complete exact proposition named by the question; no
printer string, digest-only surrogate, or ambient proposition registry is
accepted.

Every recognized module declaration body is encoded by `RB` over exactly its
named complete contract schema from Section 2.4.
`RelationsDeclarationContractCatalogV0` is the following compile-time closed
dispatch; it is an owner grammar, not another durable object or registry:

~~~text
"relations.definition-language"        -> DefinitionLanguageContractV0
"relations.oracle-access-law"           -> OracleAccessLawContractV0
"relations.model-assumption"            -> ModelAssumptionContractV0
"relations.definition-model-law"        -> DefinitionModelLawContractV0
"relations.satisfaction-evaluator"       -> SatisfactionEvaluatorContractV0
"relations.private-transform-contract"  -> PrivateTransformContractV0
"relations.refinement-law"               -> RefinementLawContractV0
"relations.value-bridge-law"             -> ValueBridgeLawContractV0
"relations.loss-source-premise"          -> LossSourcePremiseContractV0
"relations.loss-export"                  -> LossExportContractV0
"relations.artifact-fact"                -> ArtifactFactContractV0
"relations.artifact-format"              -> ArtifactFormatContractV0
"relations.artifact-interpreter"         -> ArtifactInterpreterContractV0
"relations.commitment-construction"      -> CommitmentConstructionContractV0

RelationsDeclarationBodyV0<K>(x) = RB<selected complete schema>(x)

keys(RelationsDeclarationContractCatalogV0) =
  set(RelationsDeclarationContractKindCatalogV0)
~~~

The `version` field is field `0` in every declaration schema and must encode
`N(0)`. Remaining fields follow the exact written order in Section 2.4;
variants use their written alternative order. A kind absent from this dispatch
has no declaration body grammar in K3-B. This encoding is the body stored at
the declaration's module-catalog ordinal and therefore is already committed by
its `SemanticModuleId`; Relations does not create a second declaration ID.

Every durable Relations subject defined below adds one body-profile
discriminator. Companion Relations specifications instantiate the same total
compiler and name their exact body aliases locally:

~~~text
RelationsBodyV0<T>(x) =
  R {0:Q("zkc.relations.body.v0"), 1:RB_T(x)}

RelationDefinitionBody       = RelationsBodyV0(RelationDefinition)
RelationInterfaceBody        = RelationsBodyV0(RelationInterface)
RelationInstanceBody         = RelationsBodyV0(RelationInstance)
RelationSemanticModelBody    = RelationsBodyV0(RelationSemanticModel)
DefinitionModelCorrespondenceQuestionBody =
  RelationsBodyV0(DefinitionModelCorrespondenceQuestion)
RelationTransformBody        = RelationsBodyV0(RelationTransform)
RelationRefinementQuestionBody =
  RelationsBodyV0(RelationRefinementQuestion)
ValueBridgeBody              = RelationsBodyV0(ValueBridge)
ProtocolRelationBindingBody  = RelationsBodyV0(ProtocolRelationBinding)
PlanWitnessBindingBody       = RelationsBodyV0(PlanWitnessBinding)
RelationArtifactProfileBody  = RelationsBodyV0(RelationArtifactProfile)
RelationArtifactObservationBody =
  RelationsBodyV0(RelationArtifactObservation)
ArtifactProfileCountQuestionBody =
  RelationsBodyV0(ArtifactProfileCountQuestion)
ArtifactComparisonQuestionBody =
  RelationsBodyV0(ArtifactComparisonQuestion)
GroundingEquationBody         = RelationsBodyV0(GroundingEquation)
CommitmentGroundingBody       = RelationsBodyV0(CommitmentGrounding)
~~~

`RB_T` means `RB` under the complete statically known schema `T`; it is not
runtime reflection. Formation first resolves every nested owner, kind, regime,
reference, and type, then applies the compiler. Strict decode must consume the
whole body and re-encoding must reproduce identical bytes before identity is
authenticated.

## 14. Rejected alternatives and post-K3-B gates

The selected model rejects:

- copying the pre-K1 `H(...)`, `SemanticRegimeId`, value-domain contract,
  declared-totality, and mixed-dependency placeholders;
- making every private input a relation witness;
- treating an oracle body as an ordinary witness;
- making Plan or external Interface part of the base Protocol binding;
- allowing Plan to reference a relation Interface;
- replacing occurrence graphs with a globally injective map;
- representing relation transforms or commitments as value bridges;
- combining the three bridge lanes under authored flags;
- accepting a caller-built tuple or raw run record as execution grounding;
- treating result-reference shape as behavioral equivalence;
- authoring a lossy-projection use count;
- hardcoding one universal artifact-fact list; and
- storing full relation artifacts or private assignments in Protocol identity.

At its stated boundary, the Relations algebra and its bounded pressure result
are selected, but the domain is not yet eligible for a persistent-profile or
semantic-freeze claim. Its finite pressure cases and static/invariant
instruments exercised the selected seam shapes, identities, types, authority
boundaries, and refusal classes. They did not execute every full native
protocol contract, the new lossy source-authority constructors, or every live
capability path, and they are not evidence of those stronger claims.

The remaining work is exact profile publication, implementation/evidence, and
dependent-owner freeze work:

1. The exact semantic-subject and declaration-kind catalogs, source-authority
   body schemas, and lossy-source portability choices are selected, but the
   complete six-field `SemanticLanguageProfileBody`, exact semantic-law-source
   bytes, and independently reconstructible full typed
   `RelationsProfileId` remain a publication obligation. No persistent-ID or
   semantic-freeze claim is made before that publication.
2. The source-authority selection has not yet acquired executable constructor,
   cold-replay, stale-generation, cross-field, cross-consumer, or
   cross-purpose evidence across all three lossy source arms. Such evidence
   may falsify these laws; it cannot redefine them silently.
3. Native FRI/IOR validation remains required for the exact Oracle
   publication/query/answer target union and commitment-grounding sources;
   native Nova/folding validation remains required for the ordered
   claim-instance and transform occurrence graph.
4. The bounded integrated Schnorr witness exercises only one finite
   relation/Plan grounding path. It does not close live `PlanWitnessSurface`
   extraction and substituted-Plan controls, causal `RelationRunView` issuance
   and grounding, or exemplar derived-exhaustive and certificate-backed
   bridge-law bases without an ambient checker registry. Their named PIR and
   Relations owners retain the semantic contracts; native IOP/IOR and folding
   pressure, owner-carrier implementation correspondence, and independent
   freeze evidence remain obligations.
5. The current Analysis target selects the initial relation-bound and
   Fresh-to-Fiat--Shamir profiles and their exact source/support bindings
   without restating relation facts. Broader refinement, commitment, and
   lossy-projection property profiles remain open; the concrete `sha256-216`
   reduction and quantitative price are also open.

These gates may falsify an implementation or expose a specification defect,
but their pending execution does not make the bounded K3-B selection
incomplete and does not license a fallback to the superseded placeholder
algebra.
