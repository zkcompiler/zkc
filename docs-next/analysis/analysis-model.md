# Analysis semantic model

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative Analysis target
> **Target status:** Bounded minimum kernel; broader Analysis remains deferred
> **Provisional owner:** `analysis`
> **Authority:** This page defines a redesign target for `docs-next/`. The
> current specifications under [`docs/`](../../docs/README.md) remain
> authoritative until explicit consolidation and cutover. This page establishes
> no theorem truth, property, implementation, migration, or reliance claim.

<!-- zkc-profile-source:analysis-kernel-foundation-semantics:start -->

## 1. Scope and fixed separations

The minimum Analysis kernel evaluates exact conditional propositions over
source-owned semantic subjects:

```text
authenticated source manifests
  + one closed strategy/experiment profile
  + one hypothesis-free goal
  + one canonical hypothesis context
  + semantic basis and exact support
  + independent validation basis
  -> one qualified conditional judgment
```

The following categories never alias:

```text
source subject or checked result
source manifest
strategy class
experiment profile
question
goal
conditional proposition
semantic basis
support instantiation
validation basis
checking attempt
qualified judgment record
live result capability
replay material
```

A citation is not theorem authority. A supplied run is not a strategy. A
successful run is not a universal property. A semantic basis is not its
checker. A record, digest, receipt, or replay bundle is not live authority.

## 2. Exact source ingress

### 2.0 Analysis language profiles and exact evaluators

Analysis uses the Foundation semantic-language-profile mechanism rather than an
ambient Analysis catalog inside `B`. Every portable Analysis body is governed
by one direct standalone `SemanticLanguageProfileId`. The selected profile is
an ordinary same-regime semantic subject, not a module declaration and not a
prior-meta axis. Its `supported_subject_kinds` contains the exact Analysis
subject kind being formed, and its populated publication catalogs contain the
exact marked source fragments plus every local Analysis declaration used by
its laws. Foundation's owner-qualified `SemanticProfileLawSourceV1` is the
exact direct-use, subject-language, evaluator, and failure-schema index; it
does not copy the domain law. Each `analysis.semantic-law` declaration instead
selects exact bytes in one authenticated source fragment and denotes one
closed `AnalysisLanguageProfileLawProgramV0`:

```text
AnalysisDeclarationContractV0 = {
  declaration_kind: MetaSymbol,
  local_ordinal: Natural,
  exact_declaration_body: MetaValueV0
}

AnalysisLawDeclarationV0 = {
  local_ordinal: Natural,
  law_name: MetaSymbol,
  exact_closed_law_term: MetaValueV0
}

AnalysisAdequacyEvaluatorSchemaV0 = {
  local_ordinal: Natural,
  evaluator_name: MetaSymbol,
  exact_input_schema: MetaValueV0,
  exact_failure_partition: MetaValueV0
}

AnalysisBodySchemaDeclarationV0 = {
  subject_kind: MetaSymbol,
  body_revision: exactly 0,
  constructor: MetaSymbol,
  ordered_field_schemas: CanonicalSeq<MetaSymbol>
}

AnalysisLanguageProfileLawProgramV0 = {
  version: exactly 0,
  declaration_contracts:
    CanonicalKeySortedSeq<
      (declaration_kind,local_ordinal),AnalysisDeclarationContractV0>,
  law_declarations:
    CanonicalSeq<AnalysisLawDeclarationV0>,
  adequacy_evaluator_schemas:
    CanonicalSeq<AnalysisAdequacyEvaluatorSchemaV0>,
  body_schemas:
    CanonicalKeySortedSeq<subject_kind,AnalysisBodySchemaDeclarationV0>
}

AnalysisProfileDeclarationRef<P,K> =
    ProfileLocalDeclarationRef<K> resolved locally in exact profile P
  | ImportedProfileDeclarationRef<K> naming an exact profile in P's
      authenticated import closure

AnalysisProfileLawRef<P,S> =
  AnalysisProfileDeclarationRef<P,"analysis.semantic-law",S>

AnalysisLawTerm<P,S> = {
  law_ref: AnalysisProfileLawRef<P,S>,
  canonical_arguments: CanonicalMetaValueTuple admitted by S
}

TotalAnalysisLawSignature<P,Inputs,Output> = {
  input_schemas:
    exact nonempty ordered tuple of closed schemas resolved under P equal to
      Inputs,
  output_schema: exact closed schema resolved under P equal to Output,
  totality_law:
    for every admitted input tuple there is exactly one admitted output,
  evaluation_law:
    deterministic, terminating within the declaration's exact static bound,
    and reading no ambient registry, future subject, live capability, caller
    expectation, or undeclared source
}

TotalAnalysisProfileLaw<P,Inputs,Output> =
  AnalysisProfileLawRef<
    P,TotalAnalysisLawSignature<P,Inputs,Output>>

AnalysisAdequacyEvaluatorBody<P,I> = {
  input_schema: AnalysisProfileLawRef<P,ClosedInputSchema<I>>,
  supported_input_profile_ids:
    CanonicalNonEmptySortedUniqueSeq<SemanticLanguageProfileId>,
  output_schema: exactly RootBool,
  portable_algorithm_ref: PortableAlgorithmRef,
  evaluation_contract_id: EvaluationContractId,
  exact_direct_module_roots: DirectModuleRoots(portable_algorithm_ref),
  success_value: exactly true,
  failure_partition:
    AnalysisProfileLawRef<P,AnalysisAttemptFailurePartition>
}

AnalysisAdequacyEvaluatorId<P,I> =
  AnalysisId<"analysis.adequacy-evaluator",P>(
    B,AnalysisAdequacyEvaluatorBody<P,I>)
```

The four declaration records above use only the closed version-`0` constructor
and field-schema symbols selected by that exact profile family. They are not
open names or comments. An unknown symbol, duplicate ordinal, noncontiguous
ordinal, body schema for an unsupported kind, supported kind without exactly
one body schema, or dispatcher entry unequal to the authenticated
`(subject_kind,constructor,ordered_field_schemas)` row refuses profile use.
`declaration_contracts` is keyed first by declaration-kind bytes and then by
the contiguous local ordinal derived from the inline catalogs;
`law_declarations` and `adequacy_evaluator_schemas` have contiguous ordinals in
sequence order, with the latter empty exactly when the profile declares no
evaluator; and `body_schemas` is keyed uniquely by `subject_kind` bytes. A change to
the normative interpretation of a law, constructor, or field-schema symbol is
a profile revision and rotates the profile ID. Host code cannot add, rename, or
reinterpret a row without changing and reauthenticating this law source.

The profile parameter `P` is part of the static type of every Analysis
declaration reference, law ref, law term, and evaluator body. Later displays
omit `P` only inside a constructor whose direct profile has already been fixed;
the omission is notation, not a body-to-profile inference. In particular, a
local ordinal under two unequal profiles never denotes one reusable reference.

The profile body has exactly the Foundation fields `profile_family`, `revision`,
`profile_imports`, `supported_subject_kinds`, `declaration_catalogs`, and
`semantic_law_source`. The publication catalogs and generic v1 law-source
record are strictly decoded from their exact bytes, must consume those bytes
completely, and must re-encode identically. Catalog kinds are sorted and
unique; local declaration ordinals are contiguous.
Local references are interpreted only against the selected profile's catalog;
imported references name an exact profile ID in its authenticated import
closure plus a kind and ordinal. No ID-looking bytes acquire reference meaning.
Every declaration, schema, law, and evaluator reference is resolved and
typechecked before any domain body is interpreted.

A law term is an exact typed syntax value, not prose and not a runtime callback.
An adequacy evaluator is a bounded Foundation portable algorithm whose complete ABI,
evaluation contract, exact supported input-profile IDs, and subject-specific
direct module roots are committed by its ID. Matching a profile family or
revision is insufficient, and an owner subject under an unlisted exact profile
is `Unsupported`. `Success(true)` is the only affirmative adequacy result;
`Success(false)`, domain failure, unsupported interpretation, malformed input,
resource exhaustion, and checker disagreement retain their distinct declared
dispositions.

The bounded Analysis executable is a correspondence surrogate for this target, not
an implementation of the complete typed law calculus. Its authenticated law-
source bytes contain finite declaration rows, symbolic law rows, evaluator-
schema rows, and a kind-to-body-schema table. They pressure byte stability,
profile locality, and finite dispatch, but the symbolic law and field tokens do
not yet implement `AnalysisProfileLawRef`, `AnalysisLawTerm`, closed
signatures, or general signature checking. A passing executable gate therefore
does not establish the typed-law requirement above. Closing that gap requires
an implementation to decode and typecheck the exact closed terms; it does not
permit the target specification to reinterpret the symbolic surrogate as
normative law.

The profile's exact direct imports are derived from the imported declaration
references and owner-profile dependencies admitted by its closed catalogs and
law grammar. Missing imports,
unused padding imports, cycles, and missing or extra supplied profile preimages
are refused. `EffectiveSemanticContext` authenticates only the exact bounded
profile-import DAG. It does not sweep ordinary semantic modules. Modules needed
by a portable algorithm, evaluation contract, or owner subject are authenticated
separately by that subject's exact domain dependency closure.

The earlier bounded Analysis executables construct their selected direct-import
tuples explicitly and check them for exact equality. The independent profile
publication compilers now join both branches and derive imports from exact
declaration dependencies in the published manifests. Those manifests and
source-bound definitions still do not implement the complete typed law-term
interpreter described above. Passing publication therefore establishes exact
preimage reconstruction and import locality, not execution of every typed law.

An unrelated profile or ordinary module therefore does not rotate an Analysis
ID. Adding or changing a declaration or law inside the directly selected
profile intentionally rotates every governed Analysis body; a narrow extension
forms a new importing profile rather than mutating an ambient universe.
Compatibility between unequal profile IDs is never inferred from family or
revision labels. It requires a separately checked, directional, domain-owned
compatibility relation. A profile may contain local declaration references but
never its future ID, a governed subject ID, evidence, a policy decision, or a
live/local capability. This keeps the dependency direction
`prior-meta basis -> profile DAG -> profiled subjects -> subject module DAG`
acyclic.

<!-- zkc-profile-source:analysis-kernel-foundation-semantics:end -->

Analysis selects six independently evolvable profiles rather than one Analysis
universe. Four form the initial cryptographic-property branch and two form the
independent incremental-composition branch:

```text
AnalysisKernelLanguageProfileId =
  identity of the standalone profile whose inline catalogs and law source own
  only the common Analysis body compiler, attempt partition, source-slot and
  manifest grammar, question/goal/proposition calculus, basis/support/
  validation separation, judgment grammar, and exact use/authority envelope

AnalysisCryptographicPropertyLanguageProfileId =
  identity of the standalone profile that imports exactly
    AnalysisKernelLanguageProfileId,
    the exact-used Relations Relations/correspondence profile,
    PIRInteractionProfileId,
    PIRCanonicalFramedFSProfileId,
    PIRPublicSetupProfileId,
  and whose own catalogs contain only the bounded Schnorr/property-family,
  concrete-source, experiment, quantitative, rule, use, and adequacy contracts

AnalysisAFKTransportLanguageProfileId =
  identity of the standalone profile that imports exactly
    AnalysisCryptographicPropertyLanguageProfileId
  and whose own catalogs contain only the AFK asymptotic-family language,
  abstract family-source, F-dependent experiment and quantitative,
  theorem-template, applicability, transport, specialization, and replay
  contracts

AnalysisAFKTheoremSourceValidationLanguageProfileId =
  identity of the standalone profile that imports exactly
    AnalysisAFKTransportLanguageProfileId
  and whose own catalogs contain only the theorem-source-kind declarations,
  theorem-source-validation body schema, source/proof validation laws, and the
  exact support/validation/operation-policy/judgment schemas that consume or
  govern those validation-bearing results,
  together with the two exact result-qualification declarations and contracts
  for AFK family transport and fixed-member specialization

AnalysisIncrementalCompositionLanguageProfileId =
  identity of the standalone profile that imports exactly
    AnalysisKernelLanguageProfileId,
    PIRInteractionProfileId,
    PIRInterfacePlanProfileId,
    the exact-used Relations Relations/correspondence profile,
  and whose own catalogs contain only the closed finite incremental-
  composition family, property, theorem-component, native-rule, carried-
  obligation, report-qualification, evaluator, and failure contracts

AnalysisIncrementalCompositionSourceValidationLanguageProfileId =
  identity of the standalone profile that imports exactly
    AnalysisIncrementalCompositionLanguageProfileId
  and whose own catalogs contain only theorem-source-kind and source-
  validation declarations plus the exact validation-bearing support,
  validation, operation-policy, judgment, result-authority, consumer, and
  purpose contracts for incremental-composition conclusions
```

The names are typed selectors for exact profile IDs, not family/revision
matching. The exact Relations Relations/correspondence profile imports the
Interface/Plan profile, whose own closure reaches PIR profiles. That transitive
path does not discharge Analysis's own direct uses: the property owner opens
Interaction static views, canonical-framed construction views, and
`PublicSetupInvocationView` values. It therefore imports those three exact PIR
profiles directly as well as Relations. These are required direct-use diamonds,
not redundant convenience edges.
These names now denote the six owner-local exact profile IDs published from
strict manifests and exact marked owner source. Two independent compilers
reconstruct every complete six-field body, direct-use edge, typed content
reference, and downstream rotation cone. The older joined-path profile objects
remain bounded correspondence surrogates and do not own these identities.
Publication establishes persistent target language coordinates, not typed-law
interpreter completeness, theorem truth, property establishment, implementation
conformance, or integrated semantic freeze.

The kernel never imports a downstream profile. The cryptographic profile never
imports either AFK child, and the AFK semantic transport profile never imports
its source-validation child. The incremental-composition profile imports none
of the AFK branch and never imports its own source-validation child. Thus
source-validation changes cannot rotate theorem meaning, changes in one branch
cannot rotate the other, and an unrelated property forms a new narrow profile
rather than changing an ambient universe. A mutation of an imported owner
profile intentionally rotates the direct downstream profile and governed
subjects, but cannot flow backward into the owner profile.

The version-`0` supported-kind sets are exact and are derived from the active
dispatch below, not from host classes or call sites:

```text
AnalysisProfileBundle = {
  kernel: AnalysisKernelLanguageProfileId,
  property: AnalysisCryptographicPropertyLanguageProfileId,
  transport: AnalysisAFKTransportLanguageProfileId,
  theorem_source_validation:
    AnalysisAFKTheoremSourceValidationLanguageProfileId,
  incremental_composition:
    AnalysisIncrementalCompositionLanguageProfileId,
  incremental_composition_source_validation:
    AnalysisIncrementalCompositionSourceValidationLanguageProfileId,
  required_import_edges: exactly
    property -> [kernel,exact-used Relations Relations profile,
                 PIR Interaction, PIR canonical-framed FS,
                 PIR public-setup projection],
    transport -> [property],
    theorem_source_validation -> [transport],
    incremental_composition ->
      [kernel,PIR Interaction,PIR Interface/Plan,
       exact-used Relations Relations profile],
    incremental_composition_source_validation ->
      [incremental_composition]
}

ActiveAnalysisBodyKinds =
  the exact canonical key set of the active `AnalysisBodyV0` dispatch in
  Section 4.1

AnalysisKernelSupportedKinds = {
  "analysis.hypothesis-context"
}

AnalysisCryptographicPropertySupportedKinds = {
  "analysis.adequacy-evaluator",
  "analysis.asymptotic-protocol-family",
  "analysis.capability-requirement-payload",
  "analysis.challenge-domain",
  "analysis.checked-result-coordinate",
  "analysis.consumer",
  "analysis.distribution-profile",
  "analysis.experiment-profile",
  "analysis.extractor-profile",
  "analysis.family-read-manifest-schema",
  "analysis.fixed-public-setup",
  "analysis.goal",
  "analysis.hypothesis-context",
  "analysis.judgment-record",
  "analysis.loss-semantic-import",
  "analysis.named-premise",
  "analysis.operation-policy",
  "analysis.owner-policy-closure",
  "analysis.portable-source-authority-binding",
  "analysis.positive-polynomial",
  "analysis.positive-polynomial-profile",
  "analysis.proposition",
  "analysis.quantitative-formula",
  "analysis.question",
  "analysis.semantic-basis",
  "analysis.semantic-read-manifest",
  "analysis.source-authority-contract",
  "analysis.source-profile",
  "analysis.source-support",
  "analysis.strategy-class",
  "analysis.support-instantiation",
  "analysis.use-purpose",
  "analysis.validation-basis"
}

AnalysisAFKTransportSupportedKinds = {
  "analysis.adequacy-evaluator",
  "analysis.asymptotic-protocol-family",
  "analysis.checked-result-coordinate",
  "analysis.consumer",
  "analysis.distribution-profile",
  "analysis.experiment-profile",
  "analysis.extractor-profile",
  "analysis.family-read-manifest-schema",
  "analysis.family-instance-role-map",
  "analysis.goal",
  "analysis.hypothesis-context",
  "analysis.judgment-record",
  "analysis.logical-nat-literal",
  "analysis.loss-semantic-import",
  "analysis.named-premise",
  "analysis.capability-requirement-payload",
  "analysis.operation-policy",
  "analysis.owner-policy-closure",
  "analysis.pointwise-quantitative-normalization",
  "analysis.portable-source-authority-binding",
  "analysis.proposition",
  "analysis.quantitative-formula",
  "analysis.question",
  "analysis.semantic-basis",
  "analysis.source-authority-contract",
  "analysis.source-profile",
  "analysis.strategy-class",
  "analysis.support-instantiation",
  "analysis.theorem-schema",
  "analysis.use-purpose",
  "analysis.validation-basis"
}

AnalysisAFKTheoremSourceValidationSupportedKinds = {
  "analysis.capability-requirement-payload",
  "analysis.checked-result-coordinate",
  "analysis.consumer",
  "analysis.judgment-record",
  "analysis.operation-policy",
  "analysis.owner-policy-closure",
  "analysis.portable-source-authority-binding",
  "analysis.source-authority-contract",
  "analysis.support-instantiation",
  "analysis.theorem-source-validation",
  "analysis.use-purpose",
  "analysis.validation-basis"
}

AnalysisIncrementalCompositionSupportedKinds = {
  "analysis.adequacy-evaluator",
  "analysis.consumer",
  "analysis.goal",
  "analysis.hypothesis-context",
  "analysis.incremental-composition-family",
  "analysis.proposition",
  "analysis.quantitative-formula",
  "analysis.question",
  "analysis.semantic-basis",
  "analysis.semantic-read-manifest",
  "analysis.source-profile",
  "analysis.theorem-schema",
  "analysis.use-purpose"
}

AnalysisIncrementalCompositionSourceValidationSupportedKinds = {
  "analysis.capability-requirement-payload",
  "analysis.checked-result-coordinate",
  "analysis.consumer",
  "analysis.judgment-record",
  "analysis.operation-policy",
  "analysis.owner-policy-closure",
  "analysis.portable-source-authority-binding",
  "analysis.source-authority-contract",
  "analysis.source-support",
  "analysis.support-instantiation",
  "analysis.theorem-source-validation",
  "analysis.use-purpose",
  "analysis.validation-basis"
}
```

For each profile, `supported_subject_kinds` and the key set of `body_schemas`
in its authenticated law source must equal the corresponding set above after
canonical sorting. The union is exactly `ActiveAnalysisBodyKinds`; an extra or
missing key refuses profile use. Overlap is intentional reuse of a closed body
grammar, not permission to choose a profile. Every *concrete body constructor*
has one direct profile: family-owned bodies use the profile containing that
exact family declaration; goals inherit their authenticated question profile;
propositions and semantic bases use their owning family profile; property,
transport, and theorem-validation result constructors are fixed respectively
to the property, transport, and validation profile; and the Analysis authority
carriers inherit the completed result profile. The initial family-neutral
empty hypothesis context is the only body formed directly under the kernel
profile. No generic identity operation accepts a caller-selected profile for a
body whose required profile has not first been derived and checked by these
rules.

The incremental-composition family, its Relations-result adequacy evaluators,
source profiles and concrete manifests, questions, goals, propositions,
theorem schemas, quantitative formulas, and semantic bases select the
incremental-composition profile. Source support, theorem support, validation,
policy, judgment, and authority carriers that consume its live owner results
or theorem-source validation select the narrow source-validation child.
Neither profile imports or reuses the AFK
branch merely because both use the common Analysis calculus.

The selected `analysis.challenge-domain` constructor is the one explicit
cross-layer boundary to the family-owned shorthand above. It forms a
property-owned finite projection from the exact challenge coordinates in one
authenticated concrete subject tuple. Its named constructor case fixes the
property profile and verifies those owner coordinates and the selected
adequacy evaluator. The body carries no transport-owned family ID and therefore
verifies no such predecessor; nor does it import the transport profile backward
into the property profile or authorize caller choice. The cryptographic-
property page owns the exact restriction.

`RequiredAnalysisLanguageProfile` below selects the kernel profile only for a
closed family-neutral kernel constructor. A family-owned question, goal,
proposition, and semantic basis select the exact semantic profile that owns
that family. Support and validation constructors select the narrowest exact
importing profile required by their authenticated predecessors. An operation
policy and the judgment it governs select the exact completed-result profile;
they never fall back to the profile that merely owns the result's property
family. Thus the AFK theorem schema, questions, goals, propositions, semantic
bases, and applicability/transport semantics select the semantic transport
profile, while a theorem-source-validation body and every AFK support,
validation basis, operation policy, or judgment body that actually consumes or
governs one select the narrow child validation profile. A body cannot choose a
profile, and a same-shaped body under another profile is a distinct semantic
subject.

The same rule applies independently to incremental composition: the family
and semantic theorem bodies select its semantic profile; a source-validation
body and every support, validation, policy, judgment, or authority body that
consumes it select its exact child. No constructor searches both branches for
a matching body shape.

<!-- zkc-profile-source:analysis-kernel-domain-semantics:start -->

### 2.1 Source read slots

Analysis imports the Foundation/project source-binding variants; it does not redefine
their fields:

```text
AnalysisExactSourceAuthorityBinding =
    PortableSourceAuthorityBinding
  | OwnerLocalSourceAuthorityBinding
```

One manifest slot has the following Analysis-owned meaning:

```text
AnalysisSemanticReadSlot = {
  owner_domain,
  source_family,
  exact_semantic_coordinate,
  read_purpose: SemanticMeaning | PremiseSupport | OccurrenceEvidence,
  selected_fields: CanonicalNonEmptySeq<OwnerFieldCoordinate>,
  adequacy_evaluator_id: AnalysisAdequacyEvaluatorId<OwnerReadInput>,
  source_binding_schema,
  required_authority_class: None | FreshSourceCapability,
  failure_disposition
}

AnalysisFamilyRoleReadSlotSchema = {
  abstract_role_coordinate: LocalAnalysisSourceFamilyRoleRef,
  read_purpose: SemanticMeaning | PremiseSupport,
  dependent_signature,
  adequacy_evaluator_id: AnalysisAdequacyEvaluatorId<AbstractRoleReadInput>,
  failure_disposition
}

LocalAnalysisSourceFamilyRoleRef = {
  local_role_ordinal: Natural,
  exact_role_tag: AnalysisProfileDeclarationRef<"analysis.family-role-kind">
}

AnalysisFamilyRoleKindDeclarationBody = {
  name: MetaSymbol,
  signature_class:
      ValueCarrier | Predicate | ExperimentProcess | VerifierProcess
    | ResourceMeasure | PositivePolynomialProfile | QuantitativeValue
}

AnalysisSourceReadSlotSchema =
    OwnerSourceReadSlotSchema(AnalysisSemanticReadSlot schema)
  | AbstractFamilyRoleSlotSchema(AnalysisFamilyRoleReadSlotSchema)

AnalysisClosedReadCoordinate =
    ConcreteOwnerField(OwnerFieldCoordinate)
  | AbstractFamilyRoleField(
      LocalAnalysisSourceFamilyRoleRef,exact dependent_signature)

ExactOwnerFieldProjection(owner_body_schema,field_paths) =
  the canonical sorted unique sequence of OwnerFieldCoordinate values obtained
  by resolving every path in field_paths against owner_body_schema; formation
  rejects an absent path, an interior record in place of a leaf, a duplicate,
  or caller order different from ascending encoded OwnerFieldCoordinate order

CompleteOwnerBodyProjection(owner_body_schema) =
  ExactOwnerFieldProjection(
    owner_body_schema,
    the regime-derived sequence of every leaf path in owner_body_schema)

ResolvedOwnerSourceBodySchema(owner_domain,source_family) =
  the one exact closed body schema resolved from the authenticated owner-domain
  catalog for source_family

ResolvedOwnerSourceBindingSchema(owner_domain,source_family) =
  the one exact immutable view, admitted-body, or checked-result binding schema
  that the same owner declaration exposes for source_family

ConcreteOwnerReadSlotSchema(
    owner_domain,source_family,semantic_coordinate_schema,read_purpose,
    selected_fields,adequacy_evaluator_id,source_binding_schema,
    required_authority_class,failure_disposition) =
  OwnerSourceReadSlotSchema(AnalysisSemanticReadSlot schema {
    owner_domain,
    source_family,
    exact_semantic_coordinate: semantic_coordinate_schema,
    read_purpose,
    selected_fields,
    adequacy_evaluator_id,
    source_binding_schema,
    required_authority_class,
    failure_disposition
  })

AbstractFamilyRoleReadSlotSchema(
    abstract_role_coordinate,read_purpose,dependent_signature,
    adequacy_evaluator_id,failure_disposition) =
  AbstractFamilyRoleSlotSchema(AnalysisFamilyRoleReadSlotSchema {
    abstract_role_coordinate,
    read_purpose,
    dependent_signature,
    adequacy_evaluator_id,
    failure_disposition
  })
```

`selected_fields` is a projection, not copied fact values. The source owner
defines every field and the schema of its immutable view or checked-result
binding. Analysis owns only the semantic read selection, purpose, adequacy
requirement, and proposition that uses it. A semantic slot contains no concrete
source binding, origin, qualification, policy closure, capability requirement
value, or live token.

A semantic slot is invalid when the source kind, semantic coordinate, subject,
expected polarity, binding schema, authority class, purpose, or field set
differs. At invocation, a missing support binding or authority is
`CannotAnswer`; a wrong authenticated subject, concrete binding, capability, or
use is `Refused`; noncanonical structure is `Malformed`; an unsupported source
kind or field is `Unsupported`.

An abstract family-role slot has no owner domain, concrete semantic coordinate,
binding schema, or live authority class. It is legal only in a family read
manifest schema, where the resolved family-language contract derives its value
from one abstract member. Its local role ref is resolved only against the
complete source-family declaration selected by the enclosing profile; it cannot
escape that declaration, become a durable role ID, or refer to the source-family
coordinate from inside that coordinate's own body. Family denotation and
projection coherence remain
ordinary hypotheses. Using an abstract slot in a concrete manifest, or an
owner-source slot in an abstract family projection, is malformed.

### 2.2 Finite manifests

The source shape is independent of any experiment that later consumes it. Its
family coordinate is an authenticated declaration, not a caller-authored tag:

```text
AnalysisSourceFamilyCoordinate =
  AnalysisProfileDeclarationRef<"analysis.source-family">

AnalysisSourceFamilyDeclarationBody<P> = {
  allowed_slot_variant: ConcreteOwnerSource | AbstractFamilyRole,
  exact_slot_and_field_schema,
  exact_adequacy_evaluator_schema:
    AnalysisProfileLawRef<SourceFamilyAdequacyEvaluatorSchema>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

AnalysisSourceFamilySemanticsContract<P> = {
  allowed_slot_variant: ConcreteOwnerSource | AbstractFamilyRole,
  exact_slot_and_field_schema,
  exact_adequacy_evaluator_schema:
    AnalysisProfileLawRef<SourceFamilyAdequacyEvaluatorSchema>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

ResolvedAnalysisSourceFamilyContract(P,coordinate) =
  the one declaration contract in the authenticated law source of exact
  `SemanticLanguageProfileId` P whose complete profile-declaration coordinate equals
  coordinate; absent, duplicate, wrong-profile, or body-mismatched resolution
  is rejected

AnalysisSourceProfile = {
  family_tag: AnalysisSourceFamilyCoordinate,
  slot_schemas: CanonicalNonEmptySeq<AnalysisSourceReadSlotSchema>,
  closed_field_read_set: CanonicalSortedUniqueSeq<AnalysisClosedReadCoordinate>,
  adequacy_evaluator_id: AnalysisAdequacyEvaluatorId<SourceProfileInput>
}

AnalysisSourceProfileBody = AnalysisSourceProfile

AnalysisSourceProfileId =
  AnalysisId<"analysis.source-profile">(B, AnalysisSourceProfileBody)
```

A concrete slot schema fixes its owner domain, source family, purpose, field
projection, authority class, and failure disposition. An abstract slot schema
instead fixes one family role and dependent signature. Neither contains a
concrete binding or capability. One source profile is uniformly concrete or
abstract; mixing the variants refuses admission. An experiment may name an
`AnalysisSourceProfileId`; the source profile never names the experiment. This
direction prevents a manifest/profile/experiment identity cycle.

`closed_field_read_set` is a retained canonical summary, not an authored
claim. `DerivedClosedFieldReadSet(slot_schemas)` is the sorted-unique union of
every concrete slot's exact selected owner fields, or of every abstract slot's
role coordinate and complete dependent signature. Formation requires the body
field to equal that result exactly. A missing, extra, duplicated, reordered, or
wrong-variant read coordinate is malformed.

The complete source-family declaration and body must resolve through
`ResolvedAnalysisSourceFamilyContract(P, family_tag)` in the exact profile that
governs the source-profile body, and its selected contract must admit
the profile's slot variant and exact slot/field/adequacy schemas. A display
name, free symbol, or declaration with the right spelling but another body is
`Unsupported`; malformed payload or slot structure is `Malformed`. Adding or
changing a source-family contract rotates its profile ID and every governed or
downstream-importing Analysis ID; it does not rotate the shared semantic regime.

```text
AnalysisSemanticReadManifest = {
  source_profile_id: AnalysisSourceProfileId,
  exact_subjects: CanonicalNonEmptySeq<SemanticContentId>,
  slots: CanonicalSortedUniqueSeq<AnalysisSemanticReadSlot>
}

AnalysisSemanticReadManifestBody = AnalysisSemanticReadManifest

AnalysisSemanticReadManifestId =
  AnalysisId<"analysis.semantic-read-manifest">(
    B, AnalysisSemanticReadManifestBody)
```

The manifest is admitted only when:

1. every slot names an admitted owner source kind and exact semantic
   coordinate;
2. its selected fields are exactly the fields declared by the source profile;
3. no two slots claim one coordinate under conflicting owners or purposes;
4. every required field has exactly one authoritative source;
5. every binding schema and required authority class matches the owner
   declaration.

Missing, extra, duplicated, wrong-purpose, or ambient reads fail. A view cannot
be widened later without changing the manifest and every dependent question.

Concrete authority belongs to support and invocation instead:

```text
AnalysisSourceSupport = {
  semantic_read_manifest_id: AnalysisSemanticReadManifestId,
  bindings: CanonicalSortedUniqueSeq<{
    semantic_read_slot_ref,
    exact_source_authority_binding: AnalysisExactSourceAuthorityBinding
  }>,
  derived_owner_policy_dependency_closure:
    CanonicalSortedUniqueSeq<TypedContentId>
}

AnalysisSourceSupportBody = AnalysisSourceSupport

PortableAnalysisSourceSupportId =
  AnalysisId<"analysis.source-support">(B, AnalysisSourceSupportBody)
```

`AnalysisSourceSupport` is portable only when every owner coordinate permits
it; otherwise it is a collision-free `LocalAnalysisSourceSupportHandle` with
no portable ID. Matching fresh capabilities are
supplied separately at the checking occurrence and enter no portable identity.
Changing a source check, result origin, qualification, or policy binding may
change support without changing the semantic question.

The owner capability requirement is not a second authored support field. The
complete `OwnerCapabilityRequirement` is read from
`exact_source_authority_binding`; the slot's exact adequacy evaluator resolves
its owner-profiled `owner_requirement` body and requires the same owner domain,
capability family, binding schema, consumer, typed use, and semantic read
purpose. For an admitted-subject binding, its owner source coordinate must equal
the slot's semantic coordinate. For a checked-result binding, it must instead be
the exact owner result coordinate whose authenticated payload answers that slot
coordinate and polarity under the slot evaluator; a result coordinate is never
silently equated with its question coordinate. `required_authority_class` says
whether that inert requirement must additionally be met by a matching fresh
invocation capability. A mismatch refuses consumption; a duplicated or
caller-authored requirement field is malformed.

The policy summary is derived, never authored:

```text
DerivedOwnerPolicyDependencyClosure(bindings) =
  CanonicalSortedUniqueUnion, by complete typed policy-ID bytes, of
    1. the exact TypedContentId carried by each binding's
       OwnerOperationPolicyDisposition, and
    2. every exact TypedContentId in the owner-profiled canonical closure body
       authenticated by that binding's owner_policy_closure ID

ExactAnalysisSourceSupportBody(
    manifest_id,manifest_body,supplied_owner_bindings) =
  authenticate `manifest_id` against `manifest_body` and its exact source
  profile; for every manifest slot derive the unique supplied owner binding
  whose owner coordinate, requirement, semantic-read purpose, binding schema,
  authority class, and adequacy result match that slot; reject zero or multiple
  matches and reject any unused supplied binding; sort the resulting slot/
  binding records by the manifest's canonical slot order; return
  AnalysisSourceSupportBody {
    semantic_read_manifest_id: manifest_id,
    bindings: the derived complete slot/binding sequence,
    derived_owner_policy_dependency_closure:
      DerivedOwnerPolicyDependencyClosure(the derived binding sequence)
  }

ExactAnalysisSourceSupportId(
    manifest_id,manifest_body,supplied_owner_bindings) =
  AnalysisId<"analysis.source-support">(B,
    ExactAnalysisSourceSupportBody(
      manifest_id,manifest_body,supplied_owner_bindings))
```

Formation authenticates every binding, resolves the complete owner-binding
payload, requirement, immediate policy disposition, and owner-policy-closure
preimage under the exact owner profile selected by the slot, and requires the
owner adequacy evaluator to validate that closure's derivation. It rejects a
dependency cycle or profile/regime mismatch, derives the union once, and
requires the body field to equal it exactly. Missing, extra, duplicated, or
caller-reordered policy IDs are malformed. The field is retained only as a
canonical authenticated summary; it creates no policy authority. Foundation's
generic envelope does not interpret or establish the owner closure.

`ExactAnalysisSourceSupportId` is defined only when the derived body is fully
portable. If any selected owner binding is local, the same checked derivation
returns a `LocalAnalysisSourceSupportHandle` and the portable-ID constructor is
undefined; no caller may hash the local handle or copied binding body.

### 2.3 Asymptotic family ingress

Foundation authenticates finite semantic descriptions and PIR Protocols use finitely
bounded `ValueType`s. Neither therefore becomes an asymptotic protocol family
by quantifying over the lengths admitted by one fixed type. Analysis uses a
separate, explicit mathematical family subject:

```text
LogicalNat = the unbounded natural-number binder sort of the Analysis logic

AnalysisAsymptoticFamilyLanguageDeclarationBody(name,payload_type,
                                                 contract_revision) =
  MetaRecord {
    0: MetaSymbol(name),
    1: DeclarationValueTypeBody(payload_type),
    2: MetaNatural(contract_revision)
  }

ResolvedAnalysisFamilyLanguageContract(P,language_ref) =
  the one asymptotic-family-language declaration contract resolved from P's
  authenticated `AnalysisLanguageProfileLawProgramV0`; the complete declaration
  body and payload schema must match exactly

AnalysisAsymptoticFamilyLanguageContract = {
  input: (the resolved declaration, one canonical value of its lifted
          payload type, n : LogicalNat),
  denotation_relation:
    DenotesFamilyMember(language_ref,payload,n,abstract_member),
  abstract_member_signature: {
    mathematical Statement and Witness carriers,
    relation and relation-membership predicate,
    public setup and setup-selection schedule,
    commitment, challenge, response, proof, and auxiliary-output carriers,
    Fresh and Fiat--Shamir experiment schemas and verifier relations,
    finite nonempty challenge set and cardinality,
    prover, verifier, extractor, and oracle interface schemas,
    statement-length and resource-measure functions,
    failure, undefinedness, and nontermination laws
  },
  declaration_admission:
    exact declaration grammar, resolution by
    ResolvedAnalysisFamilyLanguageContract(P,language_ref), successful lift of
    payload_type, and an Analysis provider conforming to that profile contract,
  non_claims:
    declaration admission establishes no member existence, uniqueness,
    coherence, algorithm implementation, resource law, or theorem
}

AnalysisAsymptoticProtocolFamilyDefinitionBody(
    language_ref:AnalysisProfileDeclarationRef<
      "analysis.asymptotic-family-language">,
    payload) = {
  family_language: language_ref,
  canonical_family_payload:
    CanonicalValue<resolved and lifted payload type of language_ref>(payload)
}

AnalysisAsymptoticProtocolFamilyDefinitionId(B,language_ref,payload) =
  AnalysisId<"analysis.asymptotic-protocol-family">(
    B,AnalysisAsymptoticProtocolFamilyDefinitionBody(language_ref,payload))

FamilyMember(F,n:LogicalNat) =
  the abstract mathematical member related to `(F,n)` by the one resolved
  language contract; it is not a Foundation `CanonicalValue`, PIR Protocol,
  Relations object, or portable algorithm

AnalysisFamilyReadManifestSchemaBody = {
  family_definition_id: AnalysisAsymptoticProtocolFamilyDefinitionId,
  member_source_profile_id: AnalysisSourceProfileId
}

DerivedFamilyReadProjection(F,source_profile,n) =
  the unique ordered projection of the fixed abstract-member roles named by
  source_profile's closed slot schemas, interpreted through F's resolved
  family-language contract

AnalysisFamilyReadManifestSchemaId =
  AnalysisId<"analysis.family-read-manifest-schema">(
    B, AnalysisFamilyReadManifestSchemaBody)
```

The selected language contract belongs to the exact semantic-language profile
directly committed by the family body, not to `B` and not to a live provider
registry. Each entry is keyed by the complete declaration coordinate and body
and fixes the payload interpretation and mathematical denotation law. Changing
that contract rotates the selected profile and every governed family ID;
changing an unrelated profile does not. Provider code only implements the
already selected law and disagreement is `CheckerFailure`. A declaration not
resolved by the selected profile is `Unsupported`, not provider-defined
meaning.

The initial admitted profile entry is the closed indexed-protocol-signature
language `analysis.indexed-protocol-signature.v0`. Its exact lifted payload
type is:

```text
IndexedProtocolSignatureV0Payload = CanonicalRecord {
  0: statement_role: Symbol[1,128],
  1: witness_role: Symbol[1,128],
  2: relation_role: Symbol[1,128],
  3: public_setup_role: Symbol[1,128],
  4: commitment_role: Symbol[1,128],
  5: challenge_role: Symbol[1,128],
  6: response_role: Symbol[1,128],
  7: proof_role: Symbol[1,128],
  8: auxiliary_output_role: Symbol[1,128],
  9: verifier_output_role: Symbol[1,128],
  10: fresh_experiment_role: Symbol[1,128],
  11: fiat_shamir_experiment_role: Symbol[1,128],
  12: random_oracle_index_role: Symbol[1,128],
  13: statement_length_role: Symbol[1,128],
  14: resource_measure_role: Symbol[1,128]
}
```

All fifteen values must be pairwise distinct. Missing, extra, duplicate, or
empty role symbols are malformed. At `(payload,n)` the regime law
denotes nominal dependent carriers and relations keyed by the complete family
ID, `n`, and those role symbols. It supplies no algebraic equation,
implementation, totality, efficiency, distribution, or theorem; all such laws
are propositions. This exact nominal-signature entry is sufficient for Analysis; a
computational or proof-assistant family language requires a new exact language
profile (or a new revision of the profile deliberately governing that family).

The declaration kind above has exactly the three-field body grammar shown; a
different record, payload type, or revision is malformed or unsupported. The
profile contract fixes the input and result signatures, while the selected
declaration and payload fix the language-specific mathematical relation. That relation is
not a Foundation portable executable and is not evaluated by bounded Foundation iteration.
Foundation authenticates only the finite declaration reference and payload.

The family-read-manifest schema likewise has exactly the two fields shown.
Its member projection and coherence obligation are derived from the closed
source-profile slot sequence and the fixed abstract-member signature; they are
not caller-authored expression fields. A missing role, duplicate role, or
unsupported role interpretation refuses schema admission. The derived
projection's agreement with the denotation remains a proposition below.

The following remain ordinary Analysis propositions unless discharged by
accepted proof authority:

- total family denotation for every `n : LogicalNat`;
- existence and uniqueness of one abstract member at every such `n`;
- coherence of Statement, Witness, relation, Fresh/FS, challenge, setup, and
  ABI projections; and
- uniformity and asymptotic resource laws of the selected algorithm families.

Formation of `F` proves none of those propositions. A family question retains
them in its hypothesis context. `FamilyMember(F,n)` is a dependent logical
subject inside that context. It is never required to be natively admitted at
every `n`; such a requirement would make an unbounded family uninhabitable
under Foundation's finite value and body limits. For one representable concrete `n0`,
an admitted Foundation/PIR/Relations subject `S` is related to the abstract
member only through a separately checked
`FamilyInstanceCorrespondence(F,n0,S)` proposition. `F`
contains neither derived projections nor concrete members, theorem IDs,
proposition IDs, or correspondence results, so the dependency direction is
acyclic and callers cannot author parallel family fields that disagree.

A fixed PIR subject can support finite tests and a specialized pointwise
judgment. It cannot fill an asymptotic family slot, establish uniformity, or
turn a finite length range into `LogicalNat`.

### 2.4 Protocol source family

An active Protocol manifest selects one admitted Protocol and only the exact
subset of these owner views required by its family:

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

The first six are derived from one PIR Core. A Fresh-only property need not and
must not select transcript-construction or FS fields merely because a later
transport may use them. `TranscriptDeclarationView`,
`RequiredInfluenceView`, and `ChallengeTransitionView` are derived from one
exact PIR transcript construction. `FSConstructionView` is derived only from the
exact affirmative `CheckedFSConstruction` and carries the paired Fresh/FS
Protocol IDs, shared Core, maps, and structural conclusion. The manifest checks
the owner-issued `FSResultView(CheckedFSConstructionResultRef,
CanonicalFramedFSResultViewKindRef)` plus the exact transcript-construction/
Fresh/FS/Core
subject coordinates. Its support binds the
`ExactPIRStaticViewAuthorityBinding<FSConstructionView>`, and the Analysis
checking invocation supplies the matching `PIRStaticViewCapability`. The
underlying `ExactCheckedFSConstructionAuthorityBinding` and
`CheckedFSConstructionCapability` were consumed by PIR's
`IssueFSConstructionView` and do not cross that issuance boundary into
Analysis; there is no portable authority implied by either result ref. The
manifest checks that all source coordinates agree. It never contains a second
event schedule, transcript declaration, influence graph, challenge sampler, or
Protocol body.

`ExecutionView` exposes the strategy-step boundary and generated-execution
law. A concrete `RunRecord`, `RelationRunView`, `CausalGenerationCapability`,
or `CheckedReplayMatch` enters only a separately declared occurrence slot.

### 2.5 Relations source family

When a property is relation-bound, its manifest selects exact Relations and
PIR-owned coordinates for:

```text
admitted relation definition and RelationSemanticModel
admitted relation Interface and RelationInstance
admitted ProtocolRelationBinding and PlanWitnessBinding
exact Relations CorrespondenceQuestion IDs and owner refs for Statement,
  claim, and Witness coordinates
exact PIR CheckRef and CheckDecl algorithm/evaluation-contract/input fields
exact PIR TerminalRef and TerminalDecl verdict/required-check/disposition fields
exact Relations GroundingEquationId and EquationGrounding question coordinate
bridge-use scope and selection schema
occurrence-local loss-source and export schemas, when consumed
```

The universal acceptance correspondence is an Analysis proposition formed over
this manifest and a deterministic correspondence experiment. It belongs in the
property hypothesis context and support, never in the source profile or
manifest. This preserves the one-way edge from owner semantic reads to an
Analysis-owned proposition and avoids a manifest/proposition cycle.

The concrete affirmative `CheckedCorrespondence` result bindings are support
inputs for those exact questions, and their live capabilities are invocation
inputs. Concrete bridge-use selections, loss-source/export results, and
consumer-source joins follow the same rule. They do not enter the semantic read
manifest or property identity.

Analysis may consume a live `CheckedRelationSatisfaction` only when a selected
occurrence premise explicitly requires it. The result remains owner-local and
cannot be restated, serialized, or generalized. The initial special-soundness
profile does not use a caller Boolean or remint `RelationSatisfies`.

## 3. Strategy and experiment semantics

### 3.1 Strategy class

```text
StrategyClassProfile = {
  role: AnalysisProfileDeclarationRef<"analysis.strategy-role">,
  dependent_parameter_schema: CanonicalSeq<AnalysisParameterSchemaEntry>,
  strategy_abi: AnalysisProfileLawRef<StrategyABI>,
  private_state_type: ValueType,
  initial_advice_type: ValueType,
  allowed_views: CanonicalSortedUniqueSeq<OwnerFieldCoordinate>,
  allowed_oracles_and_capabilities:
    CanonicalSortedUniqueSeq<AnalysisProfileLawRef<CapabilityABI>>,
  legal_move_relation: AnalysisLawTerm<StrategyLegalMoveRelation>,
  stop_and_noncompletion_law:
    AnalysisProfileLawRef<StrategyStopAndNoncompletionLaw>,
  resource_dimensions: ResourceBasis
}

StrategyClassProfileBody = StrategyClassProfile

AnalysisStrategyClassProfileId =
  AnalysisId<"analysis.strategy-class">(B, StrategyClassProfileBody)
```

For a PIR prover, each interactive step must inhabit the exact PIR boundary:

```text
StrategyStep(ProverView, private_state, private_randomness)
  -> ProverMove | Stop
```

`allowed_views` is the exact `StrategyDecisionView` projection. The strategy
cannot read a future challenge, hidden verifier state, an oracle table behind
its query capability, or an unlisted occurrence. A whole trace, `RunRecord`,
move table containing future-dependent values, replay result, or serialized
strategy observation cannot fill this slot.

### 3.2 Quantifier prefix

Quantifier order is semantic identity:

```text
QuantifierAtOrdinal(i) =
    ForAllStrategy(
      binding_ordinal: exactly i,
      AnalysisStrategyClassProfileId,
      dependent_domain_predicate over EarlierQuantifierRef<j<i>)
  | ExistsStrategy(
      binding_ordinal: exactly i,
      AnalysisStrategyClassProfileId,
      dependent_domain_predicate over EarlierQuantifierRef<j<i>)
  | Sample(
      binding_ordinal: exactly i,
      AnalysisDistributionProfileId)
  | ForAllValue(
      binding_ordinal: exactly i,
      ValueType,
      domain_predicate over EarlierQuantifierRef<j<i>)
  | ForAllFamilyValue(
      binding_ordinal: exactly i,
      AnalysisAsymptoticProtocolFamilyDefinitionId,
      dependent_abstract_sort,
      dependent_domain_predicate over EarlierQuantifierRef<j<i>)
  | ForAllQuantitativeValue(
      binding_ordinal: exactly i,
      AnalysisQuantitativeSort,
      domain_predicate over EarlierQuantifierRef<j<i>)
  | ForAllLogicalNat(
      binding_ordinal: exactly i,
      domain_predicate over EarlierQuantifierRef<j<i>)
  | ExistsPositivePolynomial(
      binding_ordinal: exactly i,
      AnalysisPositivePolynomialProfileId)
  | ExistsExtractor(
      binding_ordinal: exactly i,
      AnalysisExtractorProfileId)
  | ExistsUniformBlackBoxExtractor(
      binding_ordinal: exactly i,
      AnalysisExtractorProfileId)
  | ExistsUniformExtractorFamily(
      binding_ordinal: exactly i,
      AnalysisExtractorProfileId)

QuantifierPrefix =
  NonEmptyOrderedSeq whose entry at sequence position i is QuantifierAtOrdinal(i)

EarlierQuantifierRef<j<i> =
  the canonical natural ordinal j, accepted only when j is in range and
  strictly earlier than the containing QuantifierAtOrdinal(i)

CurrentQuantifiedValue =
  the typed bound value tested by the `domain_predicate` of the containing
  ForAll constructor; it is a profile-owned AST leaf, not an ordinal reference
  and is unavailable outside that constructor's predicate
```

Reordering adaptive statement choice, setup, public coins, advice, strategy,
oracle sampling, or extractor choice creates a different experiment. There is
no normalization that commutes quantifiers merely because two fixtures happen
to produce the same finite runs.

Display binders such as `A`, `Ext`, `pair`, `n`, and `Q` are reader aliases for
the corresponding `binding_ordinal`; they are never encoded. Every dependent
domain, experiment term, and quantified-witness requirement refers to a binder
only by its exact ordinal and checks the constructor and dependent sort at that
ordinal. Alpha-renaming therefore cannot rotate an experiment, while changing
order, constructor, type, profile, or a dependent reference necessarily does.

`ForAllValue` ranges only over one admitted finite Foundation `ValueType`.
`ForAllFamilyValue` ranges over an abstract dependent mathematical carrier
denoted by one family at the already bound `LogicalNat`; its denotation and
domain predicate remain family hypotheses. The two constructors are not
interchangeable, and a finite native value enumeration cannot establish a
`ForAllFamilyValue` conclusion.

The referenced profile kinds are closed Analysis semantic objects:

```text
AnalysisDistributionProfile = {
  output_type: AnalysisProfileLawRef<DependentOutputType>,
  exact_support_predicate: AnalysisLawTerm<DistributionSupportPredicate>,
  exact_probability_mass_or_measure_law:
    AnalysisLawTerm<ProbabilityOrMeasureLaw>,
  parameter_and_security_parameter_coordinates:
    CanonicalSeq<AnalysisParameterSchemaEntry>,
  independence_and_correlation_declarations:
    CanonicalSortedUniqueSeq<AnalysisLawTerm<IndependenceOrCorrelationLaw>>,
  sampling_or_oracle_denotation: AnalysisLawTerm<SamplingOrOracleDenotation>,
  failure_and_nontermination_law:
    AnalysisProfileLawRef<DistributionFailureAndNonterminationLaw>
}

AnalysisDistributionProfileBody = AnalysisDistributionProfile

AnalysisExtractorProfile = {
  input_and_output_types: AnalysisProfileLawRef<ExtractorABI>,
  private_state_and_randomness_types: AnalysisProfileLawRef<ExtractorStateABI>,
  allowed_source_and_oracle_capabilities:
    CanonicalSortedUniqueSeq<AnalysisProfileLawRef<CapabilityABI>>,
  counterfactual_rights:
    CanonicalSortedUniqueSeq<ProgramSibling | Rerun>,
  state_preservation_relation: AnalysisLawTerm<StatePreservationRelation>,
  output_distribution_preservation_relation:
    AnalysisLawTerm<OutputDistributionPreservationRelation>,
  witness_success_relation: AnalysisLawTerm<WitnessSuccessRelation>,
  termination_and_asymptotic_resource_law:
    AnalysisLawTerm<ExtractorTerminationAndResourceLaw>,
  counterfactual_capability_contract_and_property_family_scope:
    AnalysisProfileLawRef<CounterfactualCapabilityScope>
}

AnalysisExtractorProfileBody = AnalysisExtractorProfile

AnalysisPositivePolynomialProfile = {
  input_sort: LogicalNat | StatementLength(statement_type),
  coefficient_domain: Nat,
  value_shape: CanonicalNonEmptySeq<Nat> in low-to-high order,
  canonical_degree_rule: highest coefficient is nonzero unless degree is zero,
  evaluation: AnalysisProfileLawRef<CheckedNaturalHornerEvaluation>,
  positivity_rule: constant coefficient is at least one,
  admitted_coefficient_and_degree_bounds:
    AnalysisProfileLawRef<PolynomialCoefficientAndDegreeBounds>
}

AnalysisPositivePolynomialProfileBody = AnalysisPositivePolynomialProfile

AnalysisPositivePolynomial = {
  profile_id: AnalysisPositivePolynomialProfileId,
  coefficients_low_to_high: CanonicalNonEmptySeq<Nat>
}

AnalysisPositivePolynomialBody = AnalysisPositivePolynomial

AnalysisDistributionProfileId =
  AnalysisId<"analysis.distribution-profile">(B, body)

AnalysisExtractorProfileId =
  AnalysisId<"analysis.extractor-profile">(B, body)

AnalysisPositivePolynomialProfileId =
  AnalysisId<"analysis.positive-polynomial-profile">(B, body)

AnalysisPositivePolynomialId =
  AnalysisId<"analysis.positive-polynomial">(
    B, AnalysisPositivePolynomialBody)
```

`ProgramSibling` and `Rerun` are the complete common counterfactual-right
vocabulary. They are operational authority classes, not informal names for a
proof technique. Every selected right must have one complete denotation in the
profile's final
`counterfactual_capability_contract_and_property_family_scope` field and one
compatible capability ABI in `allowed_source_and_oracle_capabilities`.
`Program`, `Fork`, and `Rewind` are not aliases: programming is only the exact
sibling-programming transition, a fork is a checked relation between completed
siblings rather than execution authority, and root rerun is the only admitted
reset operation. An absent denotation or any other tag refuses profile
formation.

The initial uniform Fresh-coin and classical random-oracle profiles define
their exact finite-output laws with these bodies. The initial AFK extractor
profile alone supplies its exact lazy-random-oracle denotation and grants the
`ProgramSibling` and `Rerun` rights. Naming
an extractor algorithm or a distribution label without these laws does not
form either profile. Extractor profiles are theorem-neutral; a theorem schema
selects one exact profile, never the reverse, so their identities cannot cycle.
The positive-polynomial profile is the bounded Analysis representation over which
the existential ranges; each admitted polynomial value has its own ID. It is
not a caller-supplied numerical bound or an ambient complexity claim. The
selected `q_KS(n) = 1` witness is
`AnalysisPositivePolynomialId(profile, [1])`. Broader polynomial
representations require a new profile.

### 3.3 Experiment profile

```text
AnalysisExperimentProfile = {
  family: AnalysisFamilyCoordinate,
  source_profile_id: AnalysisSourceProfileId,
  quantifier_prefix: QuantifierPrefix,
  role_interfaces: CanonicalSortedUniqueSeq<AnalysisProfileLawRef<RoleABI>>,
  setup_and_input_sampling: AnalysisLawTerm<SetupAndInputSamplingLaw>,
  randomness_ownership_and_independence:
    AnalysisLawTerm<RandomnessOwnershipAndIndependenceLaw>,
  public_coin_or_oracle_model: AnalysisProfileLawRef<CoinOrOracleModel>,
  scheduler: AnalysisProfileLawRef<ExperimentScheduler>,
  generated_execution_relation: AnalysisLawTerm<GeneratedExecutionRelation>,
  observation_and_win_event: AnalysisLawTerm<ObservationAndWinEvent>,
  failure_abort_and_noncompletion_law:
    AnalysisProfileLawRef<ExperimentFailureLaw>,
  termination_law: AnalysisProfileLawRef<ExperimentTerminationLaw>,
  resource_basis: ResourceBasis,
  output_type: AnalysisProfileLawRef<DependentOutputType>
}

AnalysisExperimentProfileBody = AnalysisExperimentProfile

AnalysisExperimentProfileId =
  AnalysisId<"analysis.experiment-profile">(
    B, AnalysisExperimentProfileBody)
```

Semantically, an instantiated experiment maps parameters and legal strategy
modules to a subdistribution over terminated records:

```text
(StructuredOutcome, ResourceVector, AuditTrace, Terminated)
```

Explicit abort and completed failure are structured outcomes. Missing
probability mass denotes genuine nontermination; it is not also returned as an
outcome. A step-indexed experiment may instead return its exact limit outcome,
but that establishes only the bounded experiment. The common kernel imposes no
global strategy-termination rule: each family profile selects its exact total,
almost-sure, partial, or bounded completion law. In particular, the active AFK
prover domain is total-output with no runtime bound, while future profiles may
admit genuine missing mass. Expected-time resources are separate from worst-
case resources.

For an ordinary PIR run, `generated_execution_relation` invokes the PIR
generated-execution semantics. `StrategyStopped`, invalid moves, future reads,
verifier failure, sampling exhaustion, and accepted/rejected terminals retain
their exact source dispositions; a family profile states which contribute to
its win event. It cannot silently drop an outcome that benefits its bound.

### 3.4 Oracle and resource discipline

Oracle access is capability-typed. An adversary receives query operations, not
the hidden table. Lazy sampling is an oracle denotation, not a counterfactual
right. The only common counterfactual rights are `ProgramSibling` and `Rerun`,
and they exist only inside an exact theorem experiment whose capability
contract grants them; neither is a PIR replay capability.

```text
ResourceDimension = {
  operation_role: AnalysisProfileDeclarationRef<"analysis.resource-operation">,
  value_sort,
  owner_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  dependent_parameter_schema: CanonicalSeq<AnalysisParameterSchemaEntry>,
  capability_abi_or_algorithm_schema:
    AnalysisProfileLawRef<CapabilityOrAlgorithmSchema>,
  lifetime_scope: AnalysisProfileLawRef<ResourceLifetimeScope>,
  aggregation: Sum | Maximum | Expected,
  exact_counter_event: AnalysisLawTerm<ResourceCounterEvent>
}

ResourceBasis = CanonicalSortedUniqueSeq<ResourceDimension>
```

Examples include adversary random-oracle queries, verifier calls, extractor
invocations, expected time, memory, and communication. They never collapse to
one ambient `cost` scalar. A count sort contains the complete resource-
dimension body, including its owners, operation role, capability/algorithm
schema, lifetime, aggregation, and counter event. Matching only a display
name, natural-number carrier, or predicate is insufficient. In particular, a
query count owned by a verifier, another oracle ABI, another subject, or
another experiment cannot fill an adversary random-oracle-query parameter.

## 4. Foundation-aligned semantic identities

### 4.1 One identity algebra

Every portable Analysis semantic object uses the exact authenticated Foundation prior-
meta basis `B`, the existing semantic-regime axis, and one directly selected Foundation
semantic-language profile:

```text
AnalysisConstructorProfileRule =
    FixedToSelectedProfile
  | OwnsResolvedFamily(AnalysisFamilyCoordinate)
  | InheritAuthenticatedQuestionProfile
  | InheritAuthenticatedGoalProfile
  | NarrowestExactImportingProfileOfAuthenticatedPredecessors
  | ExactCompletedResultProfile

AnalysisConstructorCaseContract = {
  subject_kind: MetaSymbol,
  exact_body_schema: AnalysisProfileLawRef<ClosedAnalysisBodySchema>,
  predecessor_schema:
    AnalysisProfileLawRef<ClosedConstructorPredecessorSchema>,
  profile_rule: AnalysisConstructorProfileRule,
  exact_formation_law:
    AnalysisProfileLawRef<TotalAnalysisConstructorFormationLaw>
}

AnalysisConstructorCaseRef =
  AnalysisProfileDeclarationRef<"analysis.constructor-case">

RequiredAnalysisLanguageProfile(
    constructor_case_ref,K,body,authenticated_predecessors) =
  authenticate the exact Analysis profile bundle and every predecessor; resolve
  `constructor_case_ref` in exactly one bundle profile; require its
  `subject_kind` to equal K, its body schema to admit exactly body, its
  predecessor schema to admit exactly authenticated_predecessors, and its
  total formation law to return true; apply its profile rule and require the
  result to equal the profile that owns constructor_case_ref; return that one
  profile ID; zero or multiple matching cases is malformed

AnalysisId<K,P>(B, body) =
  profiled_content_id(
    K,
    P,
    AnalysisDomainBodyV0<K>(body),
    B.semantic_regime)

where P must equal
  RequiredAnalysisLanguageProfile(
    ExactConstructorCaseOf(body),K,body,AuthenticatedPredecessors(body))
```

There is no separate `AnalysisSemanticRegimeId`, no free `H(...)`, and no
identity derived from display text, a citation label, or a live capability.
`P` is a static constructor parameter and an identity-bearing field of the Foundation
profiled wrapper; it is not recovered from the unprofiled domain body.
`AnalysisId<K>(B,body)` in later compact displays means the unique well-typed
`AnalysisId<K,P>(B,body)` after the surrounding constructor has fixed `P`.
There is no unqualified runtime overload. `RequiredAnalysisLanguageProfile` is
not a registry lookup or caller choice. In the target it accepts only the six
exact owner-published profile IDs and their authenticated no-extra closure; a
structurally compatible ad-hoc, rotated, family/revision-equal, or broader
profile is refused. Each
selected profile law source contains a canonical constructor-case catalog,
whose key set equals the finite active constructor table. Merely listing a
kind in `supported_subject_kinds` never authorizes minting it.
`ExactConstructorCaseOf(body)` is notation for the case ref statically fixed by
the named owner constructor that produced `body`; it is not inferred from a
host class, searched by kind, or accepted from an untrusted caller. The
formation operation recompiles the body and binds its exact digest, case ref,
predecessor set, and selected profile before calling Foundation `profiled_content_id`.
For a family-owned question it is the profile fixed by the complete family
declaration; a goal inherits the authenticated question profile; a proposition
inherits the authenticated goal profile; bases, support, validation, policy,
and judgments use the unique profile fixed by their closed constructor and
must be profile-compatible with every referenced predecessor. Independent
strategy, experiment, formula, theorem, and source-profile constructors name
their exact owning profile in the owner specification. Zero or multiple
profiles is malformed. Each resulting body is a closed `MetaValueV0` tagged
record with canonical finite sequences and exact typed references.

The bounded Analysis executable does not yet carry the authenticated
`analysis.constructor-case` catalog or execute the total resolver above. It
uses a finite host-side constructor dispatcher to select and cross-check the
profile for the covered body classes. That surrogate pressures the selected
branch results, but it is not evidence that the catalog is complete, that its
predecessor schemas are authenticated, or that
`RequiredAnalysisLanguageProfile` has been implemented. A conforming
implementation must resolve the exact catalog entry and execute its committed
formation law before minting the profiled ID; host dispatch cannot become a
second authority.

The common dependent types used below are not open metavariables. They are
resolved through the exact authenticated semantic-language profile directly
selected by the body:

```text
AnalysisFamilyCoordinate =
  AnalysisProfileDeclarationRef<"analysis.property-family">

AnalysisFamilySemanticsContract<P> = {
  exact_subject_schema: AnalysisProfileLawRef<ClosedFamilySubjectSchema>,
  exact_question_payload_meta_schema:
    AnalysisProfileLawRef<ClosedFamilyQuestionPayloadSchema>,
  exact_hypothesis_free_conclusion_meta_schema:
    AnalysisProfileLawRef<ClosedFamilyConclusionSchema>,
  question_to_conclusion_reconstruction_law:
    AnalysisLawTerm<TotalQuestionToConclusionReconstruction>,
  allowed_question_context_variants:
    CanonicalNonEmptySortedUniqueSeq<AnalysisQuestionContextVariant>,
  exact_quantitative_result_schema:
    AnalysisProfileLawRef<ClosedFamilyQuantitativeResultSchema>,
  affirmative_and_negative_meaning:
    AnalysisProfileLawRef<FamilyPolarityMeaning>,
  finite_cover_discharge_contract:
    None | AnalysisFiniteCoverFamilyContract,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

AnalysisFiniteCoverFamilyContract = {
  exact_cover_schema:
    AnalysisProfileLawRef<ClosedFiniteCoverSchema>,
  exact_candidate_algorithm_schema:
    AnalysisProfileLawRef<ClosedFiniteCandidateAlgorithmSchema>,
  exact_representative_success_schema:
    AnalysisProfileLawRef<ClosedFiniteRepresentativeSuccessSchema>,
  exact_coverage_certificate_schema:
    AnalysisProfileLawRef<ClosedFiniteCoverageCertificateSchema>,
  exact_quotient_factorization_certificate_schema:
    AnalysisProfileLawRef<ClosedFiniteQuotientFactorizationCertificateSchema>,
  exact_success_transfer_certificate_schema:
    AnalysisProfileLawRef<ClosedFiniteSuccessTransferCertificateSchema>,
  finite_cover_target_reconstruction_law:
    AnalysisLawTerm<TotalFiniteCoverTargetReconstruction>,
  operation_checker_binding_admission_law:
    AnalysisLawTerm<TotalFiniteCoverCheckerBindingAdmission>,
  deterministic_stream_progress_law:
    AnalysisLawTerm<DeterministicFiniteStreamProgress>
}
```

The law and schema sorts in that contract have closed signatures:

```text
TotalFiniteCoverTargetReconstruction =
  total law from one authenticated proposition, its question, its singleton
  finite-value experiment, and its resolved family contract to exactly one
  AnalysisFiniteCoverTarget; it accepts no validation basis, checker, receipt,
  certificate occurrence, support binding, or future judgment coordinate

ClosedFiniteCoverSchema =
  exact schema over the target's raw and representative types, both domain
  predicates and ABIs, normalization, representative embedding, canonical
  representative-stream algorithm and ABI, and output-congruence law and ABI

ClosedFiniteCandidateAlgorithmSchema =
  exact schema over the candidate extractor profile, portable algorithm, and
  candidate ABI in one AnalysisFiniteCoverTarget

ClosedFiniteRepresentativeSuccessSchema =
  exact schema over the representative-success and raw-member-success
  predicates and their ABIs in one AnalysisFiniteCoverTarget

ClosedFiniteCoverageCertificateSchema,
ClosedFiniteQuotientFactorizationCertificateSchema,
ClosedFiniteSuccessTransferCertificateSchema =
  three pairwise-distinct exact goal-body schemas for, respectively, only the
  quotient coverage, universal quotient-factorization, and success-transfer
  obligations stated below
```

These are semantic schemas. They do not name an implementation of a checker.
Their law-source bytes are fixed by the selected family profile, and
`ExactFiniteCoverTargetOf` executes or applies every one of them. None is a
display label or an unconstrained extension point.

```text
ResolvedAnalysisFamilyContract(P,family) =
  the one property-family contract in P's authenticated
  `AnalysisLanguageProfileLawProgramV0` whose complete declaration coordinate
  and body equal family; absence, duplication, or a wrong-profile body rejects

ExactFamilyQuestionPayload<f> =
  the canonical MetaValueV0 accepted by f's resolved question-payload schema

ExactFamilyConclusion<f> =
  the canonical MetaValueV0 accepted by f's resolved conclusion schema

TypedSemanticSubjectRef<K> =
  the exact ContentRefV0 of an authenticated SemanticContentId<K>, where K is
  admitted by the consuming family contract and source profile

TypedSemanticSubjectRef =
  the closed kind-indexed union of TypedSemanticSubjectRef<K> admitted by the
  exact selected Analysis family and source-profile contracts

AnalysisQuantitativeSort =
    Nat
  | Probability
  | SignedProbabilityLowerBound
  | ComputationalAdvantage(exact game subject)
  | LogicalNat
  | StatementLength(exact statement-type coordinate)
  | ChallengeCardinality(exact challenge-domain subject)
  | FamilyChallengeCardinality(
      exact asymptotic-family subject, LogicalNat parameter ordinal)
  | FamilyConstantChallengeCardinality(
      exact asymptotic-family subject)
  | QueryCount(
      complete ResourceDimension body,
      exact binding for every dependent parameter)
  | ExpectedCount(
      complete ResourceDimension body,
      exact binding for every dependent parameter)

AnalysisParameterSchemaEntry = {
  local_ordinal: Natural,
  sort: AnalysisQuantitativeSort
}

In concrete displays, `n : S`, `Q : S`, and similar binder notation is an
expository abbreviation for the entry at that sequence position
`{local_ordinal: position, sort: S}`. The displayed binder spelling is not a
body field. Formation requires ordinals `0..len-1` in sequence order; every
dependent reference uses the ordinal and exact earlier sort.

LocalParameterRef<S> =
  an earlier in-range local ordinal whose declared sort is exactly S

BasisNeutralQuantitativeExpr<S> =
  a canonical typed MetaValueV0 expression admitted by the authenticated
  quantitative-expression grammar of the selected Analysis language profile
```

An `AnalysisFiniteCoverFamilyContract` is a fixed profile contract, not a
table of future subjects or a declaration that one raw carrier is feasible to
enumerate. Its reconstruction law receives and authenticates a candidate
proposition, question, and experiment at application time and derives the raw
target, representative cover, predicates, and candidate algorithm from those
bodies. The law-source bytes contain only the closed reconstruction and
checker-binding admission laws plus the schemas above; they contain no
governed proposition, experiment, extractor, algorithm, checker, certificate
occurrence, semantic-basis, validation-basis, or judgment ID. `None` is a
structural prohibition: a family without this exact contract cannot acquire
finite-cover discharge merely because one of its fixtures or experiment
profiles happens to have a finite carrier.

#### Exact Analysis body compiler

`AnalysisBodyV0<T>` is total on every admitted active Analysis body and undefined
on every other host value. It uses Foundation `U`, `MF`, `MT`, `N`, `I`, `O`, `Q`, `S`,
`R`, and `V`; it does not serialize a printer, field name, host class, or prose
clause. Record fields and variant alternatives are numbered `0..n-1` in their
written order in the closed body schema selected by the direct language
profile.

```text
AB(Unit)                    = U
AB(false)                   = MF
AB(true)                    = MT
AB(Natural n)               = N(n)
AB(Int z)                   = I(z)
AB(Bytes x)                 = O(x)
AB(MetaSymbol x)            = Q(x)

AB(SemanticContentId<K> x)  = O(ContentRefV0(x))
AB(PriorMetaId<K> x)        = O(PriorRefV0(x))
AB(ModuleDeclarationRef<K> x) = DeclarationRefBody(x)
AB(ProfileDeclarationRef<K> x) = profile_declaration_ref_datum(x)
AB(SemanticLanguageProfileId x) = O(ContentRefV0(x))
AB(DeclarationValueType x)  = DeclarationValueTypeBody(x)
AB(ValueType T)             = CanonicalValueTypeBody(T)
AB(CanonicalValue<T> x)     = R {0:CanonicalValueTypeBody(T),1:x.datum}

AB(Optional.None)           = V(0,U)
AB(Optional.Some(x))        = V(1,AB(x))
AB(Enum alternative i)      = V(i,U)
AB(Variant alternative i,x) = V(i,AB(x))
AB(Record {f0,...,fn-1})    = R {0:AB(f0),...,n-1:AB(fn-1)}
AB(Tuple (x0,...,xn-1))     = R {0:AB(x0),...,n-1:AB(xn-1)}
AB(Sequence [x0,...,xn-1])  = S[AB(x0),...,AB(xn-1)]

AB(CanonicalSet X) =
  S[AB(x)... sorted by M(AB(x)); duplicate encodings reject]

AB(CanonicalMap M0) =
  S[R{0:AB(k),1:AB(v)} ... sorted by M(AB(k));
    duplicate key encodings reject]

AnalysisDomainBodyV0<T>(x) = AB_T(x)

AnalysisBodyV0<T>(P,x) =
  profiled_semantic_body(P,AnalysisDomainBodyV0<T>(x))
```

`CanonicalSeq`, nonempty sequences, sorted-unique sequences, exact maps, local
ordinals, and dependent maps first satisfy their independent length, order,
key-domain, totality, and earlier-reference laws and then use the sequence or
map arm above. `AnalysisProfileLawRef`, `AnalysisLawTerm`, typed quantitative
ASTs, theorem-template ASTs, source slots, field coordinates, and every closed
property payload use their selected profile's complete statically known schema;
there is no runtime reflection. A phrase such as “exact correspondence law” in
expository prose is never a body value: the corresponding closed schema field
contains an `AnalysisProfileLawRef`, an `AnalysisLawTerm`, or an
`AnalysisAdequacyEvaluatorId` of the displayed signature.

The active dispatch is exactly:

```text
"analysis.adequacy-evaluator"       -> AnalysisAdequacyEvaluatorBody
"analysis.source-profile"           -> AnalysisSourceProfileBody
"analysis.semantic-read-manifest"   -> AnalysisSemanticReadManifestBody
"analysis.source-support"           -> AnalysisSourceSupportBody
"analysis.checked-result-coordinate" -> AnalysisCheckedResultCoordinateBody
"analysis.capability-requirement-payload" ->
  AnalysisCapabilityRequirementPayloadBody
"analysis.source-authority-contract" -> AnalysisSourceAuthorityContractBody
"analysis.owner-policy-closure"     -> AnalysisOwnerPolicyClosureBody
"analysis.portable-source-authority-binding" ->
  PortableAnalysisSourceAuthorityBindingBody
"analysis.strategy-class"           -> StrategyClassProfileBody
"analysis.distribution-profile"     -> AnalysisDistributionProfileBody
"analysis.extractor-profile"        -> AnalysisExtractorProfileBody
"analysis.positive-polynomial-profile" -> AnalysisPositivePolynomialProfileBody
"analysis.positive-polynomial"      -> AnalysisPositivePolynomialBody
"analysis.experiment-profile"       -> AnalysisExperimentProfileBody
"analysis.asymptotic-protocol-family" ->
  AnalysisAsymptoticProtocolFamilyDefinitionBody
"analysis.incremental-composition-family" ->
  IncrementalCompositionFamilyBody
"analysis.family-read-manifest-schema" -> AnalysisFamilyReadManifestSchemaBody
"analysis.challenge-domain"         -> AnalysisChallengeDomainBody
"analysis.fixed-public-setup"       -> AFKFixedPublicSetupBody
"analysis.quantitative-formula"     -> AnalysisQuantitativeFormulaBody
"analysis.logical-nat-literal"      -> AnalysisLogicalNatLiteralBody
"analysis.family-instance-role-map" -> FamilyInstanceRoleMapProposalBody
"analysis.pointwise-quantitative-normalization" ->
  AFKPointwiseQuantitativeNormalizationContractBody
"analysis.consumer"                 -> AnalysisConsumerIntakeBody
"analysis.use-purpose"              -> AnalysisUsePurposeIntakeBody
"analysis.question"                 -> AnalysisQuestionBody
"analysis.goal"                     -> AnalysisGoalBody
"analysis.hypothesis-context"       -> AnalysisHypothesisContextBody
"analysis.proposition"              -> AnalysisPropositionBody
"analysis.named-premise"            -> AnalysisNamedPremiseBody
"analysis.theorem-schema"           -> AnalysisTheoremSchemaBody
"analysis.theorem-source-validation" -> AnalysisTheoremSourceValidationBody
"analysis.loss-semantic-import"     -> AnalysisLossSemanticImportBody
"analysis.semantic-basis"           -> AnalysisSemanticBasisBody
"analysis.support-instantiation"    -> AnalysisSupportInstantiationBody
"analysis.validation-basis"         -> AnalysisValidationBasisBody
"analysis.operation-policy"         -> AnalysisOperationPolicyBody
"analysis.judgment-record"          -> AnalysisJudgmentRecordBody
```

The exact owner page defines each right-hand schema. A selected profile's
`body_schemas` must contain that identical schema and no second schema for the
same subject kind. A kind absent from this dispatch is `Unsupported`; an
untyped field, unknown variant, schema mismatch, or host carrier without an
`AB` arm is `Malformed`. Owner-local handles, capabilities, evaluator
processes, observations without a declared portable ID, and live source views
have no `AB` arm and cannot enter a portable preimage.

This table is also a semantic-compression boundary. A helper record, theorem-
local binder, experiment-local process description, resource occurrence,
family-role entry, or quantitative subterm is encoded inside its nearest
stable owner body unless another owner specification independently gives it a
portable semantic identity. An owner-produced object retains that owner's
kind and exact reference; Analysis does not mint an `analysis.*` alias for it.
Finite falsifier and fixture values that intentionally have no durable meaning
use a disjoint `probe.analysis.*` namespace and are forbidden from every Analysis
ID, proposition, judgment, authority binding, support assertion, or claimed
parity witness. Adding a host class, helper function, or printable label never
extends this dispatch. A genuinely new durable subject requires an explicit
body schema, direct-profile assignment, compiler arm, formation law, and
locality tests together.

```text
DirectAnalysisContentDependencies(P,T,x) =
  every exact typed ContentRefV0 emitted while compiling AB_T(x)

DirectAnalysisModuleRoots(P,T,x) =
  CanonicalSortedUniqueUnion(
    modules named by every ModuleDeclarationRef emitted by AB_T(x),
    exact_direct_module_roots of every referenced adequacy evaluator)

ExactAnalysisDependencyClosure(P,T,x) =
  {
    semantic_context:
      the exact EffectiveSemanticContext selected by P,
    content_dependencies:
      the exact authenticated transitive content/body closure reached from
      DirectAnalysisContentDependencies,
    ordinary_module_dependencies:
      the separately authenticated exact no-extra SemanticModule closure
      reached from DirectAnalysisModuleRoots
  }
```

Formation proceeds in this order: authenticate `B`; authenticate `P` and the
exact no-extra profile-import closure; strictly decode and validate its inline
declaration catalogs and law source;
preflight all aggregate counts; authenticate every direct content dependency;
resolve every declaration, law ref, schema, and evaluator; check the complete
owner schema and all dependent formation laws; compile `AnalysisBodyV0`;
strictly decode the result, consume all bytes, and require byte-identical
re-encoding; derive `ExactAnalysisDependencyClosure`; reject any missing or
extra supplied dependency; and only then authenticate or form the typed ID.
All Foundation `MetaValueV0`, depth, node, edge, axis, sequence, module, schema, term,
and canonical-byte limits apply. Aggregate lengths are checked before member
inspection, so admitted compilation is total and bounded; exhaustion before a
semantic body exists is `DeterministicLimitExceeded`, not a partial ID.

This compiler and the direct profile wrapper intentionally rotate every
pre-repair Analysis ID. The rotation is semantic: previous bodies omitted the
governing language profile and did not define one total canonical preimage.
Validation-basis, policy, or provider changes outside an ID's selected profile
and exact dependency closure do not rotate that ID.

The active expression constructors and their formation rules are closed in
[`cryptographic-properties.md`](cryptographic-properties.md#6-typed-quantitative-language).
Display names such as `n`, `Q`, and `epsilon` are expository aliases for local
ordinals and do not enter an identity body. An unknown family declaration,
payload schema, conclusion schema, subject kind, quantitative sort, or
expression constructor is `Unsupported`; a malformed or ill-typed instance is
`Malformed`. Provider code cannot add meaning to these profile contracts at runtime.

The active Analysis property-family declaration set is exactly:

```text
KOutOfNSpecialSoundness
FixedExtractorUniversalCorrectness
AdaptiveKnowledgeExtractionAtFixedLengthQltN
AsymptoticKOutOfNSpecialSoundness
AdaptiveKnowledgeSoundnessQltN
TheoremTruth
TheoremApplicability
FamilyInstanceCorrespondence
ChallengeDomainCorrespondence
AcceptanceRelationCorrespondence
AlgebraAndCanonicalEncodingLaws
PolynomialTimeRelationMembership
PolynomialTimeSourceVerifier
PolynomialTimeExtractor
TotalSingleValuedFamilyDenotation
FamilyProjectionCoherence
UniformPrimeOrderSchnorrFamily
UniformPolynomialTimeRelationMembership
UniformPolynomialTimeVerifier
FreshUniformIndependentPublicCoin
ExactClassicalRandomOracleProcess
FixedPublicSetupIndependence
TotalUniformChallengeSamplerAdequacy
FixedFamilyChallengeCardinality
FiniteBoundedRandomOracleIndexAndEfficientOperations
AFKExperimentObservationCorrespondence
FamilyDenotationAtIndex
FamilyProjectionAtIndex
FamilyInstanceRoleMapAdequacy
FamilyInstanceQuantitativeNormalizationAdequacy
FamilyInstanceProcessCorrespondence
ClosedIncrementalCompositionFamily
FamilyMemberSelectionCorrespondence
FamilyDescriptionAdviceCorrespondence
StepRecurrenceCorrespondence
BindingCoverageCorrespondence
UpdateVerifierCorrectness
FinalDeciderCorrectness
ArbitraryContinuationCompleteness
IncrementalCompositionCompleteness
IncrementalCompositionKnowledgeSoundness
IncrementalCompositionEfficiency
```

Each spelling above denotes one exact module declaration, not a string tag.
The family owner page fixes its dependent payload and conclusion schemas. A
new family or a changed schema requires a new declaration and a semantic-
selected-profile contract.

Each active declaration above belongs to one exact Analysis semantic-language
profile. A family-owned question directly selects the profile that contains
its family contract; theorem, source, and quantitative profiles import only
the exact upstream profiles whose declarations they use. Within one selected
profile, declaration catalogs and contracts are canonical key-sorted and
admission rejects a missing used key, an unused imported profile, an extra
supplied profile preimage, duplicate coordinates, or two contracts for the
same complete declaration. There is no corpus-wide Analysis catalog in `B`,
no runtime registry, and no search order across profiles.

The active kinds and bodies are:

```text
analysis.strategy-class = {
  strategy ABI, state/advice types, exact access capabilities,
  legal-move relation, stop law, resource dimensions
}

analysis.experiment-profile = {
  family, source-profile ID, quantifier prefix, role interfaces,
  sampling/randomness/oracle/scheduler laws, generated execution,
  outcomes, failures, termination, resources
}

analysis.distribution-profile = {
  output type, support and probability law, parameters, independence,
  sampling/oracle denotation, failure and nontermination
}

analysis.extractor-profile = {
  exact ABI and state, allowed capabilities, counterfactual state laws,
  distribution preservation, witness success, termination/resources,
  counterfactual capability contract and property-family scope
}

analysis.positive-polynomial-profile = {
  input and coefficient sorts, canonical representation, exact evaluation,
  positivity, coefficient and degree bounds
}

analysis.positive-polynomial = {
  positive-polynomial-profile ID, exact canonical coefficient sequence
}

analysis.quantitative-formula = {
  result sort, exact parameter schema, closed basis-neutral typed formula AST
}

analysis.challenge-domain = {
  exact owner nominal challenge-declaration coordinates, Analysis-owned finite
  value model, canonical cardinality derivation and adequacy law
}

analysis.fixed-public-setup = {
  exact public setup constituent coordinates/values and pre-experiment
  independence schedule
}

analysis.asymptotic-protocol-family = {
  exact admitted family-language ref and one canonical value of its resolved
  payload type
}

analysis.incremental-composition-family = {
  exact finite member and selector maps over authenticated Protocol, Plan, and
  Relations subjects; exact recurrence and binding-coverage coordinates;
  typed update-verifier, final-decider, carried-obligation, and acyclic
  family-description-advice contracts
}

analysis.family-read-manifest-schema = {
  family-definition ID and member source-profile ID; the abstract role
  projection and its coherence obligation are derived
}

analysis.logical-nat-literal = {
  one finite MetaNatural syntax value used to select a representable family
  index; it is not the unbounded LogicalNat quantifier domain
}

analysis.family-instance-role-map = {
  family and logical-index IDs, concrete subject refs and native length,
  closed role coordinate, abstract/concrete coordinates, exact map-clause
  variant, and information-loss classification
}

analysis.semantic-read-manifest = {
  source-profile ID, exact subjects, canonical semantic read slots
}

analysis.source-profile = {
  family tag, canonical slot schemas, closed field read set,
  exact adequacy-evaluator ID
}

analysis.source-support = {
  semantic-read-manifest ID, exact portable source bindings and requirements,
  derived source-policy dependency closure
}

analysis.consumer = {
  the exact Analysis named-consumer declaration ref nominalized for a foreign
  owner API that requires a same-regime TypedContentId
}

analysis.use-purpose = {
  the exact Analysis typed-purpose declaration ref nominalized for a foreign
  owner API that requires a same-regime TypedContentId
}

analysis.question = {
  family, exact subjects, source-free or semantic-experiment context,
  family-owned question payload
}

analysis.goal = {
  question ID only; family and hypothesis-free conclusion are derived
}

analysis.hypothesis-context = {
  canonical proposition DAG and exact root set
}

analysis.proposition = {
  goal ID, hypothesis-context ID
}

analysis.semantic-basis = {
  rule or theorem schema, exact premise schemas, source read purposes,
  conclusion schema, typed transform program
}

analysis.theorem-schema = {
  exact restricted semantic statement: local bindings, source/target property
  and experiment schemas, maps, side conditions, resources, typed transform,
  conclusion reconstruction law
}

analysis.theorem-source-validation = {
  exact theorem-schema ID, bibliographic source and artifact digest,
  source locators, imported-paper or checked-proof status, truth-discharge
  metadata; never theorem semantics
}

analysis.loss-semantic-import = {
  exact Relations bridge and occurrence schema, direction, source premise and
  quantitative export, Analysis sort and interpretation rule, substitution,
  per-occurrence expression
}

analysis.support-instantiation = {
  semantic-basis ID, proposition ID, exact non-hypothesis premise bindings,
  exact established and assumed hypothesis-node bindings,
  exact manifest-to-source-support bindings
}

analysis.validation-basis = {
  admitted checker algorithms and ABIs, translations, finite controls,
  exact theorem-source validation IDs actually consumed, residual-trust roots
}

analysis.operation-policy = {
  supported family and model coordinates, named consumer/purpose permissions,
  capability lifetime, disclosure, unknown-question disposition,
  persistence and cold-replay rules
}

analysis.judgment-record = {
  proposition ID, polarity, exact conclusion, inherited hypotheses,
  quantitative result, semantic-basis ID, support ID,
  validation-basis ID, qualification and derived policy closure
}
```

The list above is a compact index of the domain-semantic carriers used most
often by Analysis; it is not a second exhaustive kind table and is not permission
to invent a different preimage. The exhaustive set is the `AnalysisBodyV0`
dispatch in Section 4.1. In particular, that dispatch additionally owns the
adequacy-evaluator, checked-result-coordinate, capability-requirement-payload,
source-authority-contract, owner-policy-closure, portable-source-authority-
binding, and pointwise-quantitative-normalization carriers whose exact schemas
are defined on their owner pages. The exact closed body types and nominal
constructors that were not already formed in Sections 2 and 3 are:

```text
AnalysisQuestionContext =
    SourceFree(AnalysisProfileLawRef<SourceFreeFamilyReason>)
  | SemanticExperimentContext {
      semantic_read_manifest_ids:
        CanonicalNonEmptySeq<AnalysisSemanticReadManifestId>,
      experiment_profile_ids:
        CanonicalNonEmptySeq<AnalysisExperimentProfileId>
    }
  | FamilySemanticExperimentContext {
      family_definition_id:
        AnalysisAsymptoticProtocolFamilyDefinitionId,
      family_read_manifest_schema_ids:
        CanonicalNonEmptySeq<AnalysisFamilyReadManifestSchemaId>,
      family_experiment_profile_ids:
        CanonicalNonEmptySeq<AnalysisExperimentProfileId>
    }
  | FamilyInstanceContext {
      family_definition_id:
        AnalysisAsymptoticProtocolFamilyDefinitionId,
      family_read_manifest_schema_ids:
        CanonicalNonEmptySeq<AnalysisFamilyReadManifestSchemaId>,
      concrete_semantic_read_manifest_ids:
        CanonicalNonEmptySeq<AnalysisSemanticReadManifestId>,
      family_experiment_profile_ids:
        CanonicalNonEmptySeq<AnalysisExperimentProfileId>,
      concrete_experiment_profile_ids:
        CanonicalNonEmptySeq<AnalysisExperimentProfileId>
    }

AnalysisNamedPremiseKind =
    FreshPublicCoinDistribution
  | FiatShamirSamplerAdequacy
  | FiatShamirOracleProcess
  | ProviderOutcomeCarrierMap
  | RelationPredicate
  | WitnessType
  | ProverPrivateState
  | HonestCommit
  | HonestRespond

AnalysisPremiseCoordinate =
    PIRPublicCoinLawCoordinate(
      ProtocolDeclarationRef<"pir.public-coin-law">)
  | AnalysisFamilyPremiseCoordinate(
      AnalysisAsymptoticProtocolFamilyDefinitionId,
      SamplerAdequacy | OracleProcess)
  | PIRProtocolOutcomePartitionCoordinate(ProtocolId)
  | RelationsModelEvaluatorCoordinate(RelationSemanticModelId)
  | RelationsWitnessPlanJoinCoordinate(
      RelationInterfaceId, private_witness_ordinal: Natural,
      PlanWitnessBindingId, witness_edge_ordinal: Natural)
  | PIRPlanStateCoordinate(ProverPlanId, persistent_state_ordinal: Natural)
  | PIRPlanRecipeCoordinate(
      ProverPlanId, decision_ordinal: Natural, recipe_node_ordinal: Natural)

AnalysisProviderDeclaration = AnalysisProfileLawRef<ProviderDeclaration>

AnalysisProviderOutcomeCarrierMapBody = {
  provider: AnalysisProviderDeclaration,
  protocol_outcome_partition: PIRProtocolOutcomePartitionCoordinate,
  provider_carrier: AnalysisProfileLawRef<ClosedProviderCarrier>,
  total_lane_map:
    CanonicalMap<ProtocolOutcomeLane, CanonicalValue<provider_carrier>>
}

AnalysisNamedPremiseBoundValue<K> =
    BoundModel(TypedSemanticSubjectRef,
               AnalysisLawTerm<ExactModelBindingLaw<K>>)
  | BoundHypothesis(AnalysisLawTerm<ExactNamedHypothesis<K>>)
  | BoundProviderOutcomeCarrierMap(AnalysisProviderOutcomeCarrierMapBody)

AnalysisNamedPremiseSource =
    OwnerSemanticCoordinate(TypedSemanticSubjectRef)
  | CandidateOwnerCoordinate(TypedSemanticSubjectRef)
  | FamilyHypothesisSource(AnalysisFamilyCoordinate)
  | ProviderDeclarationSource(AnalysisProviderDeclaration)

AnalysisPremiseEvidenceDepth =
    SourceGroundedMapping
  | TypedConstructiveBinding
  | FrozenExecutableFalsification

AnalysisPremiseModelScope =
    FreshChallengeOnly
  | OracleModelOnly(AnalysisDistributionProfileId)
  | ExactSubjectsOnly(
      CanonicalNonEmptySortedUniqueSeq<TypedSemanticSubjectRef>)
  | RebindRequired

AnalysisNamedPremiseBody<K> = {
  kind: exactly K,
  coordinate: AnalysisPremiseCoordinate admitted for K,
  bound_model_or_hypothesis: AnalysisNamedPremiseBoundValue<K>,
  source: AnalysisNamedPremiseSource admitted for K,
  evidence_depth: AnalysisPremiseEvidenceDepth,
  model_scope: AnalysisPremiseModelScope
}

AnalysisNamedPremiseRequirement = {
  slot: ExactAsciiSymbol,
  kind: AnalysisNamedPremiseKind,
  coordinate: AnalysisPremiseCoordinate admitted for kind
}

AnalysisQuestionBody = {
  family: AnalysisFamilyCoordinate,
  exact_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  context: AnalysisQuestionContext,
  family_payload: ExactFamilyQuestionPayload<family>,
  named_premise_requirements:
    CanonicalSortedUniqueSeq<AnalysisNamedPremiseRequirement>
}

AnalysisGoalBody = {
  question_id: AnalysisQuestionId,
  named_premise_bindings:
    CanonicalMap<AnalysisNamedPremiseRequirement, AnalysisNamedPremiseId>
}

GoalFamily(goal_body) =
  Authenticate(goal_body.question_id).family

HypothesisFreeConclusion(goal_body) =
  ResolvedAnalysisFamilyContract(
    ProfileOf(goal_body.question_id),GoalFamily(goal_body))
  .question_to_conclusion_reconstruction_law(
    Authenticate(goal_body.question_id))

PremiseIdsOfGoal(goal_id) =
  the canonical sorted-unique sequence of the values of
  Authenticate(goal_id).named_premise_bindings

AnalysisHypothesisNode = {
  local_ordinal,
  goal_id: AnalysisGoalId,
  dependency_ordinals: CanonicalSortedUniqueSeq<EarlierLocalOrdinal>,
  exact_named_premise_ids: exactly PremiseIdsOfGoal(goal_id)
}

AnalysisHypothesisContextBody = {
  nodes: CanonicalSeq<AnalysisHypothesisNode>,
  roots: CanonicalSortedUniqueSeq<LocalOrdinal>,
  exact_named_premise_ids:
    the canonical sorted-unique union of node.exact_named_premise_ids over
    every node reachable from roots
}

PremiseIdsOfProposition(proposition_id) =
  the canonical sorted-unique union of
  PremiseIdsOfGoal(Authenticate(proposition_id).goal_id) and
  Authenticate(Authenticate(proposition_id).hypothesis_context_id)
    .exact_named_premise_ids

AnalysisPropositionBody = {
  goal_id: AnalysisGoalId,
  hypothesis_context_id: AnalysisHypothesisContextId
}

AnalysisQuantitativeFormulaBody<S> = {
  result_sort: S,
  parameter_schema: CanonicalSeq<AnalysisParameterSchemaEntry>,
  declared_parameter_independence:
    CanonicalSortedUniqueSeq<LocalParameterOrdinal>,
  expression: BasisNeutralQuantitativeExpr<S>
}

AnalysisNativeRuleCoordinate =
  AnalysisProfileDeclarationRef<"analysis.native-rule">

AnalysisNativeRuleSemanticsContract<P> = {
  exact_payload_meta_schema: AnalysisProfileLawRef<ClosedPayloadSchema>,
  allowed_conclusion_families:
    CanonicalNonEmptySeq<AnalysisFamilyCoordinate>,
  exact_premise_requirement_schema:
    AnalysisProfileLawRef<PremiseRequirementSchema>,
  exact_typed_transform_program_schema:
    AnalysisProfileLawRef<TypedBasisTransformSchema>,
  conclusion_reconstruction_law:
    AnalysisProfileLawRef<ConclusionReconstructionLaw>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

ResolvedAnalysisNativeRuleContract(P,rule_coordinate) =
  the one exact native-rule contract resolved from P's authenticated law source
  for the complete declaration coordinate and body

NativeRuleSchema = {
  rule_coordinate: AnalysisNativeRuleCoordinate,
  canonical_rule_payload:
    CanonicalValue<resolved and lifted payload type of rule_coordinate>
}

AnalysisRuleSource =
    NativeRuleSource(NativeRuleSchema)
  | ImportedTheoremRuleSource(AnalysisTheoremSchemaId)

AnalysisQualificationRequirementCoordinate =
  AnalysisProfileDeclarationRef<"analysis.qualification-requirement">

AnalysisPolarity = Affirmative | FamilyDefinedNegative

AnalysisQualificationCoordinate =
  AnalysisProfileDeclarationRef<"analysis.qualification">

AnalysisNamedConsumerCoordinate =
  AnalysisProfileDeclarationRef<"analysis.named-consumer">

AnalysisTypedPurposeCoordinate =
  AnalysisProfileDeclarationRef<"analysis.typed-purpose">

AnalysisConsumerIntakeBody = {
  consumer: AnalysisNamedConsumerCoordinate
}

AnalysisUsePurposeIntakeBody = {
  purpose: AnalysisTypedPurposeCoordinate
}

AnalysisConsumerIntakeId(c) =
  AnalysisId<"analysis.consumer",ProfileOf(c)>(
    B,AnalysisConsumerIntakeBody {consumer: c})

AnalysisUsePurposeIntakeId(p) =
  AnalysisId<"analysis.use-purpose",ProfileOf(p)>(
    B,AnalysisUsePurposeIntakeBody {purpose: p})

AnalysisQualificationSemanticsContract<P> = {
  subject_parametric_acceptance_law:
    AnalysisProfileLawRef<SubjectParametricQualificationAcceptanceLaw>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

AnalysisQualificationRequirementSemanticsContract<P> = {
  requirement_to_law_resolver:
    AnalysisProfileLawRef<QualificationRequirementToAcceptanceLawResolver>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

AnalysisUseSemanticsContract<P> = {
  accepted_subject_and_result_kinds:
    CanonicalNonEmptySortedUniqueSeq<MetaSymbol>,
  required_qualification: AnalysisQualificationRequirementCoordinate,
  capability_attenuation_law:
    AnalysisProfileLawRef<CapabilityAttenuationLaw>,
  operation_policy_compatibility_law:
    AnalysisProfileLawRef<OperationPolicyCompatibilityLaw>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

ResolvedAnalysisUseContract(P,use_coordinate) =
  the one exact use contract resolved from P's authenticated law source for a
  complete named-consumer or typed-purpose declaration coordinate and body

ResolvedAnalysisQualificationContract(P,qualification_coordinate) =
  the one exact AnalysisQualificationSemanticsContract resolved from P's
  authenticated law source for the complete qualification declaration
  coordinate and body

ResolvedAnalysisQualificationRequirementContract(P,requirement_coordinate) =
  the one exact AnalysisQualificationRequirementSemanticsContract resolved
  from P's authenticated law source for the complete qualification-
  requirement declaration coordinate and body

ResolvedQualificationRequirementAcceptanceLaw(P,requirement_coordinate) =
  resolve ResolvedAnalysisQualificationRequirementContract(
    P,requirement_coordinate); execute its fixed
  requirement_to_law_resolver on that complete declaration coordinate and
  body; require exactly one resulting
  AnalysisProfileLawRef<SubjectParametricQualificationAcceptanceLaw> in P's
  authenticated law-source/import closure; and return that law ref

AnalysisExtractorWitnessQuantifierKind =
    ExistsExtractor
  | ExistsUniformBlackBoxExtractor
  | ExistsUniformExtractorFamily

AnalysisQuantifiedWitnessRole = {
  experiment_profile_id: AnalysisExperimentProfileId,
  quantifier_ordinal: Natural,
  expected_quantifier_kind: AnalysisExtractorWitnessQuantifierKind
}

AnalysisPremiseRequirement =
    NamedPremiseRequirement(AnalysisNamedPremiseRequirement)
  | HypothesisNodeRequirement {
      hypothesis_context_id, node_ordinal, exact_goal_id
    }
  | AffirmativeJudgmentCapabilityRequirement {
      proposition_id: AnalysisPropositionId,
      conclusion_family: AnalysisFamilyCoordinate,
      required_qualification: AnalysisQualificationRequirementCoordinate,
      named_consumer: AnalysisNamedConsumerCoordinate,
      typed_purpose: AnalysisTypedPurposeCoordinate
    }
  | ExactQuantifiedWitnessRequirement {
      witness_coordinate: TypedSemanticSubjectRef,
      exact_profile_id: AnalysisExtractorProfileId,
      quantified_role: AnalysisQuantifiedWitnessRole
    }

AnalysisReadPurposeRequirement =
    ConcreteReadPurpose {
      semantic_read_manifest_id: AnalysisSemanticReadManifestId,
      semantic_read_slot_ordinal: Natural,
      exact_purpose: SemanticMeaning | PremiseSupport | OccurrenceEvidence
    }
  | FamilyReadPurpose {
      family_read_manifest_schema_id: AnalysisFamilyReadManifestSchemaId,
      family_read_slot_ordinal: Natural,
      exact_purpose: SemanticMeaning | PremiseSupport
    }

NormalizedAnalysisReadPurpose =
    ConcreteReadPurposeAtom {
      requirement: ConcreteReadPurpose,
      semantic_read_manifest_id: AnalysisSemanticReadManifestId,
      semantic_read_slot_ordinal: Natural,
      exact_manifest_slot: AnalysisSemanticReadSlot,
      exact_profile_slot_schema: AnalysisSourceReadSlotSchema,
      exact_purpose: SemanticMeaning | PremiseSupport | OccurrenceEvidence
    }
  | FamilyReadPurposeAtom {
      requirement: FamilyReadPurpose,
      family_read_manifest_schema_id: AnalysisFamilyReadManifestSchemaId,
      family_read_slot_ordinal: Natural,
      exact_slot_schema: AnalysisFamilyRoleReadSlotSchema,
      exact_purpose: SemanticMeaning | PremiseSupport
    }

CanonicalConcreteReadPurposeExpansion(r: ConcreteReadPurpose) =
  authenticate r.semantic_read_manifest_id and its exact concrete source
  profile; select the one manifest slot and the one profile slot schema at
  r.semantic_read_slot_ordinal; require the profile slot's read_purpose to
  equal r.exact_purpose; and return ConcreteReadPurposeAtom {
    requirement: r,
    semantic_read_manifest_id: r.semantic_read_manifest_id,
    semantic_read_slot_ordinal: r.semantic_read_slot_ordinal,
    exact_manifest_slot: that manifest slot,
    exact_profile_slot_schema: that profile slot schema,
    exact_purpose: r.exact_purpose
  }

CanonicalFamilyReadPurposeExpansion(r: FamilyReadPurpose) =
  authenticate r.family_read_manifest_schema_id, its family definition, and
  its uniformly abstract member source profile; select the one abstract slot
  schema at r.family_read_slot_ordinal in the source profile's canonical slot
  sequence; require that slot's read_purpose to equal r.exact_purpose; and
  return FamilyReadPurposeAtom {
    requirement: r,
    family_read_manifest_schema_id: r.family_read_manifest_schema_id,
    family_read_slot_ordinal: r.family_read_slot_ordinal,
    exact_slot_schema: that slot schema,
    exact_purpose: r.exact_purpose
  }

CanonicalReadPurposeExpansion(r: AnalysisReadPurposeRequirement) =
  case r of
    ConcreteReadPurpose -> CanonicalConcreteReadPurposeExpansion(r)
    FamilyReadPurpose   -> CanonicalFamilyReadPurposeExpansion(r)

NormalizeReadPurposeRequirements(requirements) =
  expand every entry with CanonicalReadPurposeExpansion; reject an invalid,
  out-of-range, wrong-purpose, wrong-variant, duplicate, or conflicting
  expanded atom; order the expanded atoms by exact Foundation
  `M(AB(requirement))` bytes over the variant tag and complete fields, never
  by a host tuple or identifier order; and
  return the CanonicalSortedUniqueSeq<AnalysisReadPurposeRequirement> obtained
  by projecting each atom's exact original requirement in that order

CompleteReadPurposeRequirements(concrete_manifest_ids,
                                family_manifest_schema_ids) =
  authenticate every named manifest or schema; derive one concrete atom for
  every slot in each concrete manifest/profile join and one family atom for
  every slot in each abstract member source profile; normalize their union by
  NormalizeReadPurposeRequirements; and reject an omitted, duplicated,
  reordered, or extra atom at rule formation

ExactPremiseBinding =
    ExactNamedPremiseBinding(AnalysisNamedPremiseId)
  | PortableAffirmativeJudgmentBinding(PortableAnalysisJudgmentRecordId)
  | OwnerLocalAffirmativeJudgmentBinding(
      LocalAnalysisHandle<"analysis.judgment-record",owner,generation>)
  | ExactQuantifiedWitnessBinding(TypedSemanticSubjectRef)

ExactAffirmativeJudgmentCapabilityBinding = {
  judgment_coordinate: AnalysisJudgmentRecordCoordinate,
  required_qualification: AnalysisQualificationRequirementCoordinate,
  named_consumer: AnalysisNamedConsumerCoordinate,
  typed_purpose: AnalysisTypedPurposeCoordinate
}

AssumedGoalValidation =
    NoExternalSourceValidation
  | ImportedTheoremSourceValidation(
      AnalysisTheoremSourceValidationId)

ExactlyAssumedGoal = {
  exact_goal_id: AnalysisGoalId,
  treatment: exactly Assumed,
  assumed_goal_validation: AssumedGoalValidation
}

AnalysisCheckerContractRef = {
  portable_algorithm_ref: PortableAlgorithmRef,
  evaluation_contract_id: EvaluationContractId,
  exact_input_schema: AnalysisProfileLawRef<CheckerInputSchema>,
  exact_output_schema: AnalysisProfileLawRef<CheckerOutputSchema>,
  exact_direct_module_roots: DirectModuleRoots(portable_algorithm_ref)
}

AnalysisTranslationContractRef = {
  source_schema: AnalysisProfileLawRef<TranslationSourceSchema>,
  target_schema: AnalysisProfileLawRef<TranslationTargetSchema>,
  translation_law: AnalysisLawTerm<TotalAnalysisTranslation>
}

AnalysisFiniteControlContractRef = {
  control_kind: AnalysisProfileLawRef<FiniteControlKind>,
  exact_bound: Natural,
  exhaustion_disposition: exactly DeterministicLimitExceeded
}

FiniteCoverPredicateABI<Input> = {
  input: Input,
  output: MetaBooleanFalse | MetaBooleanTrue,
  totality: AnalysisProfileLawRef<TotalFinitePredicateEvaluation>
}

FiniteCoverOutputCongruenceABI<RawOutput,RepresentativeOutput> = {
  inputs: [RawOutput,RepresentativeOutput],
  output: MetaBooleanFalse | MetaBooleanTrue,
  totality: AnalysisProfileLawRef<TotalFiniteCongruenceEvaluation>
}

FiniteCoverRepresentativeStreamABI<Representative> = {
  state_type: ValueType,
  initial_state: CanonicalValue<state_type>,
  input: CanonicalValue<state_type>,
  output:
      Yield {representative: Representative,
             successor_state: CanonicalValue<state_type>}
    | Terminal(CanonicalValue<FiniteCoverStreamTerminal>),
  determinism_and_progress:
    AnalysisProfileLawRef<DeterministicFiniteStreamProgress>
}

FiniteCoverStreamTerminal = {
  exact_representative_count: Natural,
  ordered_representative_stream_digest: Bytes
}

FiniteControlKind = RepresentativeStreamSteps | RepresentativeEvaluations

FiniteUniversalDomainPredicate<Raw>,
FiniteRepresentativeDomainPredicate<Representative>,
FiniteRepresentativeSuccessPredicate<Representative,CandidateOutput>, and
FiniteUniversalMemberSuccessPredicate<Raw,CandidateOutput>
  = four pairwise-distinct total typed predicate-law signatures with
    `MetaBooleanFalse | MetaBooleanTrue` output

FiniteCoverOutputCongruence<RawOutput,RepresentativeOutput> =
  one total typed `MetaBooleanFalse | MetaBooleanTrue` relation-law signature

FiniteCoverNormalizationABI<Raw,Representative> =
  one total deterministic portable-algorithm ABI from Raw to Representative

FiniteCoverRepresentativeEmbeddingABI<Representative,Raw> =
  one total deterministic portable-algorithm ABI from Representative to Raw

FiniteCoverCandidateAlgorithmABI<Raw,CandidateOutput> =
  one total deterministic portable-algorithm ABI from Raw to CandidateOutput

TotalFinitePredicateEvaluation =
  total law that evaluates one exact typed predicate ABI and returns only
  MetaBooleanFalse or MetaBooleanTrue

TotalFiniteCongruenceEvaluation =
  total law that evaluates one exact output-congruence ABI on its ordered pair
  and returns only MetaBooleanFalse or MetaBooleanTrue

DeterministicFiniteStreamProgress =
  law requiring one exact initial state, one deterministic successor per
  nonterminal state, no successor after Terminal, and no repeated state before
  the exact finite control bound

TotalFiniteCoverCheckerBindingAdmission =
  total family-profile law on one exact AnalysisFiniteCoverSemanticOperation,
  one AnalysisCheckerContractRef, and exact input/output translation contracts;
  it accepts exactly when the translations connect the checker's schemas to
  that operation's ABI and the checker implements that semantic operation

AnalysisFiniteCoverSemanticOperation =
    RepresentativeStreamOperation {
      algorithm_ref: PortableAlgorithmRef,
      exact_abi: AnalysisProfileLawRef<
        FiniteCoverRepresentativeStreamABI>
    }
  | RawDomainOperation {
      predicate: AnalysisLawTerm<FiniteUniversalDomainPredicate>,
      exact_abi: AnalysisProfileLawRef<FiniteCoverPredicateABI>
    }
  | RepresentativeDomainOperation {
      predicate: AnalysisLawTerm<FiniteRepresentativeDomainPredicate>,
      exact_abi: AnalysisProfileLawRef<FiniteCoverPredicateABI>
    }
  | NormalizationOperation {
      algorithm_ref: PortableAlgorithmRef,
      exact_abi: AnalysisProfileLawRef<FiniteCoverNormalizationABI>
    }
  | RepresentativeEmbeddingOperation {
      algorithm_ref: PortableAlgorithmRef,
      exact_abi: AnalysisProfileLawRef<FiniteCoverRepresentativeEmbeddingABI>
    }
  | CandidateOperation {
      algorithm_ref: PortableAlgorithmRef,
      exact_abi: AnalysisProfileLawRef<FiniteCoverCandidateAlgorithmABI>
    }
  | QuotientFactorizationOperation {
      raw_predicate: AnalysisLawTerm<FiniteUniversalDomainPredicate>,
      normalization_algorithm_ref: PortableAlgorithmRef,
      representative_embedding_algorithm_ref: PortableAlgorithmRef,
      candidate_algorithm_ref: PortableAlgorithmRef,
      output_congruence:
        AnalysisLawTerm<FiniteCoverOutputCongruence>,
      exact_certificate_schema:
        AnalysisProfileLawRef<
          ClosedFiniteQuotientFactorizationCertificateSchema>
    }
  | RepresentativeSuccessOperation {
      predicate: AnalysisLawTerm<FiniteRepresentativeSuccessPredicate>,
      exact_abi: AnalysisProfileLawRef<FiniteCoverPredicateABI>
    }
  | SuccessTransferOperation {
      representative_success_predicate:
        AnalysisLawTerm<FiniteRepresentativeSuccessPredicate>,
      output_congruence:
        AnalysisLawTerm<FiniteCoverOutputCongruence>,
      raw_member_success_predicate:
        AnalysisLawTerm<FiniteUniversalMemberSuccessPredicate>,
      exact_certificate_schema:
        AnalysisProfileLawRef<ClosedFiniteSuccessTransferCertificateSchema>
    }

AnalysisFiniteCoverCheckerBinding = {
  exact_semantic_operation: AnalysisFiniteCoverSemanticOperation,
  checker_contract: AnalysisCheckerContractRef,
  exact_input_translation: AnalysisTranslationContractRef,
  exact_output_translation: AnalysisTranslationContractRef
}

AnalysisFiniteCoverTarget = {
  proposition_id: AnalysisPropositionId,
  experiment_profile_id: AnalysisExperimentProfileId,
  raw_value_type: ValueType,
  exact_raw_domain_predicate:
    AnalysisLawTerm<FiniteUniversalDomainPredicate>,
  exact_raw_domain_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  representative_value_type: ValueType,
  exact_representative_domain_predicate:
    AnalysisLawTerm<FiniteRepresentativeDomainPredicate>,
  exact_representative_domain_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  exact_normalization_algorithm_ref: PortableAlgorithmRef,
  exact_normalization_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverNormalizationABI>,
  exact_representative_embedding_algorithm_ref: PortableAlgorithmRef,
  exact_representative_embedding_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverRepresentativeEmbeddingABI>,
  exact_representative_stream_algorithm_ref: PortableAlgorithmRef,
  exact_representative_stream_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverRepresentativeStreamABI>,
  exact_candidate_extractor_profile_id: AnalysisExtractorProfileId,
  exact_candidate_algorithm_ref: PortableAlgorithmRef,
  exact_candidate_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverCandidateAlgorithmABI>,
  exact_output_congruence:
    AnalysisLawTerm<FiniteCoverOutputCongruence>,
  exact_output_congruence_abi:
    AnalysisProfileLawRef<FiniteCoverOutputCongruenceABI>,
  exact_representative_success_predicate:
    AnalysisLawTerm<FiniteRepresentativeSuccessPredicate>,
  exact_representative_success_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  exact_raw_member_success_predicate:
    AnalysisLawTerm<FiniteUniversalMemberSuccessPredicate>,
  exact_raw_member_success_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  coverage_goal_id: AnalysisGoalId,
  quotient_factorization_goal_id: AnalysisGoalId,
  success_transfer_goal_id: AnalysisGoalId
}

ExactFiniteCoverTargetOf(P,proposition_id) =
  authenticate proposition_id, its goal, question, exact family contract, and
  question context under P; require the family contract's
  finite_cover_discharge_contract to be present; require the question context
  to be exactly one concrete `SemanticExperimentContext` with exactly one
  experiment profile, never a family, family-instance, or source-free context;
  authenticate that profile and require its complete quantifier prefix to be
  exactly one `ForAllValue` over `raw_value_type` and
  `exact_raw_domain_predicate`; execute the family's fixed
  `finite_cover_target_reconstruction_law`; require every returned algorithm,
  ABI, predicate, schema, and certificate goal to resolve under P's
  authenticated law-source/import closure; require the normalization ABI to be
  total from raw values to representatives and the embedding ABI to be total
  from representatives to raw values; validate the returned cover fields,
  candidate fields, and success fields against, respectively, the family
  contract's exact_cover_schema, exact_candidate_algorithm_schema, and
  exact_representative_success_schema; validate coverage_goal_id against
  exact_coverage_certificate_schema, quotient_factorization_goal_id against
  exact_quotient_factorization_certificate_schema, and success_transfer_goal_id against
  exact_success_transfer_certificate_schema; require the three goals to state
  exactly the coverage, quotient-factorization, and success-transfer obligations below;
  and return the one resulting `AnalysisFiniteCoverTarget`

The three target-derived certificate goals have disjoint meanings:

1. `coverage_goal_id` states that the canonical quotient carrier contains every
   accepted residue representative, every admitted representative has the exact
   canonical embedded raw member selected by that quotient, and the selected
   `exact_representative_stream_algorithm_ref` reaches every representative
   exactly once before its terminal marker under
   `exact_representative_stream_algorithm_abi`;
2. `quotient_factorization_goal_id` states universally over the complete raw
   domain that every value satisfying the raw predicate normalizes to the
   corresponding representative domain, that normalization and representative
   embedding preserve every candidate-observable distinction used by the exact
   candidate ABI on those raw members, and that raw and representative
   candidate outputs satisfy the target's exact output congruence. It does not
   require a nonmember to remain a nonmember after narrowing normalization.
   Finite examples or a bounded set of noncanonical lifts cannot discharge
   this goal; and
3. `success_transfer_goal_id` states that representative success, together
   with that output congruence, entails the raw member-success predicate for
   every raw-domain member covered by that representative.

An affirmative result for one goal cannot fill either of the other two. A
certificate is an exact affirmative Analysis judgment capability for its
derived goal, not an unchecked proof byte string, checker assertion, or stream
digest.

ExactFiniteCoverSemanticRulePayload = {
  proposition_id: AnalysisPropositionId,
  experiment_profile_id: AnalysisExperimentProfileId,
  raw_value_type: ValueType,
  exact_raw_domain_predicate:
    AnalysisLawTerm<FiniteUniversalDomainPredicate>,
  exact_raw_domain_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  representative_value_type: ValueType,
  exact_representative_domain_predicate:
    AnalysisLawTerm<FiniteRepresentativeDomainPredicate>,
  exact_representative_domain_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  exact_normalization_algorithm_ref: PortableAlgorithmRef,
  exact_normalization_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverNormalizationABI>,
  exact_representative_embedding_algorithm_ref: PortableAlgorithmRef,
  exact_representative_embedding_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverRepresentativeEmbeddingABI>,
  exact_representative_stream_algorithm_ref: PortableAlgorithmRef,
  exact_representative_stream_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverRepresentativeStreamABI>,
  exact_candidate_extractor_profile_id: AnalysisExtractorProfileId,
  exact_candidate_algorithm_ref: PortableAlgorithmRef,
  exact_candidate_algorithm_abi:
    AnalysisProfileLawRef<FiniteCoverCandidateAlgorithmABI>,
  exact_output_congruence:
    AnalysisLawTerm<FiniteCoverOutputCongruence>,
  exact_output_congruence_abi:
    AnalysisProfileLawRef<FiniteCoverOutputCongruenceABI>,
  exact_representative_success_predicate:
    AnalysisLawTerm<FiniteRepresentativeSuccessPredicate>,
  exact_representative_success_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  exact_raw_member_success_predicate:
    AnalysisLawTerm<FiniteUniversalMemberSuccessPredicate>,
  exact_raw_member_success_predicate_abi:
    AnalysisProfileLawRef<FiniteCoverPredicateABI>,
  coverage_goal_id: AnalysisGoalId,
  quotient_factorization_goal_id: AnalysisGoalId,
  success_transfer_goal_id: AnalysisGoalId
}

ExactFiniteCoverSemanticRulePayload(target: AnalysisFiniteCoverTarget) =
  the field-for-field canonical projection of target into the record above

AnalysisFiniteCoverValidationSelection = {
  operation_checker_bindings:
    CanonicalMap<AnalysisFiniteCoverSemanticOperation,
                 AnalysisFiniteCoverCheckerBinding>,
  representative_stream_bound: AnalysisFiniteControlContractRef,
  representative_evaluation_bound: AnalysisFiniteControlContractRef
}

AnalysisFiniteCoverStreamReceipt = {
  target: AnalysisFiniteCoverTarget,
  validation_basis_id: AnalysisValidationBasisId,
  enumerator_contract_id: EvaluationContractId,
  exact_representative_count: Natural,
  ordered_representative_stream_digest: Bytes,
  ordered_evaluation_stream_digest: Bytes,
  exact_terminal_marker: CanonicalValue<FiniteCoverStreamTerminal>,
  consumed_enumerator_steps: Natural,
  consumed_member_evaluations: Natural
}

CheckedFiniteCoverUniversalDischargeContract(
    P,proposition_id,semantic_basis_id,support_coordinate,
    validation_basis_id,validation_selection,stream_receipt) =
  1. let target = ExactFiniteCoverTargetOf(P,proposition_id);
  2. authenticate semantic_basis_id and require its native rule contract to be
     the profile-owned checked-finite-cover rule, its canonical payload to equal
     `ExactFiniteCoverSemanticRulePayload(target)`, its conclusion to be exactly
     proposition_id's goal, and its complete premise requirements to include
     exactly target.coverage_goal_id, target.quotient_factorization_goal_id, and
     target.success_transfer_goal_id in addition to the source obligations
     derived by the family contract; the semantic basis contains no checker,
     stream output, run result, or resource limit;
  3. authenticate support_coordinate and require exact affirmative capability
     bindings for all three certificate goals plus every other derived premise;
     no opaque certificate body or self-asserted checker result may substitute;
  4. authenticate validation_basis_id and require validation_selection to be
     its exact no-extra checker/control projection; require exactly one checked
     operation binding for each of the target's nine semantic operations:
     representative stream, raw-domain predicate, representative-domain
     predicate, normalization, representative embedding, candidate,
     quotient-factorization, representative success, and success transfer;
     require every binding's semantic operation to equal the corresponding
     target field or exact composite law tuple, require its input/output
     translations to connect the checker's exact schemas to that operation's
     exact ABI; require exactly one canonical assignment of the validation
     basis's no-extra checker and translation entries to those nine bindings;
     execute the resolved finite-cover family contract's fixed
     operation_checker_binding_admission_law on every binding; require the two
     controls to cover the declared representative stream and member-evaluation
     counts;
  5. rerun the canonical representative stream enumerator from its unique
     initial state; for each yielded representative, require strict canonical
     successor order, successful representative-domain admission, successful
     embedding, successful execution of the exact portable candidate, and a
     true representative-success result; update the two ordered digests and
     counters incrementally without materializing either the raw carrier or a
     carrier-sized outcome map;
  6. require the enumerator to produce its exact terminal marker within the
     declared bound and require the recomputed contract ID, counts, digests,
     terminal marker, and consumed resources to equal stream_receipt exactly;
  7. reauthenticate the three certificate capabilities against this same
     target, including its semantic stream algorithm, normalization, embedding,
     output congruence, candidate ABI, and success predicates; only their
     conjunction transfers the successful representative run to the complete
     raw universal; and
  8. return permission to form the ordinary affirmative Analysis judgment for
     exactly proposition_id; return no affirmative permission after a missing
     certificate, incomplete stream, duplicate or reordered representative,
     false outcome, unsupported operation, MissingDependency, KindMismatch,
     malformed value, semantic DomainFailure, refusal, CannotAnswer, checker
     disagreement, nontermination, or deterministic limit exhaustion

AnalysisResidualTrustRootRef =
  AnalysisProfileDeclarationRef<"analysis.residual-trust-root">

AnalysisSemanticBasisBody = {
  family: AnalysisFamilyCoordinate,
  exact_question_id: AnalysisQuestionId,
  rule_source: AnalysisRuleSource,
  exact_premise_schemas:
    CanonicalSortedUniqueSeq<AnalysisPremiseRequirement>,
  source_read_purposes:
    CanonicalSortedUniqueSeq<AnalysisReadPurposeRequirement>,
  conclusion_schema: AnalysisProfileLawRef<FamilyConclusionSchema>,
  typed_transform_program: AnalysisLawTerm<TypedBasisTransform>
}

AnalysisSupportInstantiationBody = {
  semantic_basis_id: AnalysisSemanticBasisId,
  proposition_id: AnalysisPropositionId,
  exact_named_premise_ids: exactly PremiseIdsOfProposition(proposition_id),
  non_hypothesis_premise_bindings:
    CanonicalMap<AnalysisPremiseRequirement,ExactPremiseBinding>,
  established_hypothesis_node_bindings:
    CanonicalMap<LocalOrdinal,ExactAffirmativeJudgmentCapabilityBinding>,
  assumed_hypothesis_node_bindings:
    CanonicalMap<LocalOrdinal,ExactlyAssumedGoal>,
  source_support_bindings: CanonicalSortedUniqueSeq<
      ExactManifestSupportBinding {
        semantic_read_manifest_id: AnalysisSemanticReadManifestId,
        source_support_coordinate: AnalysisSourceSupportCoordinate
      }
    | FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AnalysisFamilyReadManifestSchemaId,
        dependent_support_schema:
          AnalysisProfileLawRef<DependentFamilySupportSchema>,
        exact_retained_family_support_hypotheses:
          CanonicalSortedUniqueSeq<AnalysisGoalId>
      }>
}

AnalysisValidationBasisBody = {
  admitted_checker_contract_ids_and_abis:
    CanonicalNonEmptySortedUniqueSeq<AnalysisCheckerContractRef>,
  exact_translation_contracts:
    CanonicalSortedUniqueSeq<AnalysisTranslationContractRef>,
  finite_control_contracts:
    CanonicalSortedUniqueSeq<AnalysisFiniteControlContractRef>,
  theorem_source_validation_ids:
    CanonicalSortedUniqueSeq<AnalysisTheoremSourceValidationId>,
  residual_trust_roots:
    CanonicalSortedUniqueSeq<AnalysisResidualTrustRootRef>
}

AnalysisJudgmentRecordBody = {
  proposition_id: AnalysisPropositionId,
  polarity: AnalysisPolarity,
  exact_family_conclusion: ExactFamilyConclusion<GoalFamily>,
  inherited_hypothesis_context_id: AnalysisHypothesisContextId,
  exact_named_premise_ids: exactly PremiseIdsOfProposition(proposition_id),
  typed_quantitative_result: ExactFamilyQuantitativeResult<GoalFamily>,
  semantic_basis_id: AnalysisSemanticBasisId,
  support_coordinate: AnalysisSupportInstantiationCoordinate,
  validation_basis_id: AnalysisValidationBasisId,
  qualification: AnalysisQualificationCoordinate,
  operation_policy_id: AnalysisOperationPolicyId,
  derived_source_policy_dependency_closure:
    CanonicalSortedUniqueSeq<TypedContentId>
}

AnalysisJudgmentCandidate = {
  exact_direct_profile_id: SemanticLanguageProfileId,
  proposed_body: AnalysisJudgmentRecordBody
}

QualificationSubjectContext = {
  candidate_proposition_id: AnalysisPropositionId,
  candidate_goal_id: AnalysisGoalId,
  candidate_question_id: AnalysisQuestionId,
  family: AnalysisFamilyCoordinate,
  exact_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  question_context: AnalysisQuestionContext,
  polarity: AnalysisPolarity,
  exact_family_conclusion: ExactFamilyConclusion<family>,
  inherited_hypothesis_context_id: AnalysisHypothesisContextId,
  exact_quantified_witness_coordinates:
    CanonicalSortedUniqueSeq<TypedSemanticSubjectRef>,
  candidate_qualification: AnalysisQualificationCoordinate
}

QualificationAcceptance = Accepts | Rejects

// The following two total-law signatures resolve under the exact selected
// Analysis profile P.

SubjectParametricQualificationAcceptanceLaw =
  TotalAnalysisProfileLaw<
    P,
    inputs: [
      AnalysisJudgmentRecordBody,
      exact authenticated AnalysisPropositionBody named by that record,
      QualificationSubjectContext derived from that same record
    ],
    output: QualificationAcceptance>

QualificationRequirementToAcceptanceLawResolver =
  TotalAnalysisProfileLaw<
    P,
    inputs: [
      AnalysisQualificationRequirementCoordinate,
      exact authenticated declaration body of that coordinate
    ],
    output:
      Resolved(
        AnalysisProfileLawRef<
          SubjectParametricQualificationAcceptanceLaw>)
      | NoMatch>
```

An acceptance law must reject unless all three inputs describe the same
candidate and authenticated proposition. A resolver has no default: `NoMatch`
is refusal of that requirement, while two matching rows are malformed profile
law source. Neither law can read a future judgment ID, live capability, caller-
supplied expected identity, or ambient registry.

```text

DeriveQualificationSubjectContext(P,candidate) =
  require candidate.exact_direct_profile_id to equal P; validate every field
  of candidate.proposed_body except qualification acceptance; authenticate its
  proposition, goal, question, family contract, and hypothesis context under
  the uniquely required profiles; derive every field of
  QualificationSubjectContext from those authenticated bodies and the
  candidate polarity, conclusion, and qualification; require the derived
  conclusion and inherited context to equal the candidate fields; derive
  exact_quantified_witness_coordinates from every authenticated
  ExactQuantifiedWitnessRequirement in the candidate semantic basis and its
  uniquely matching support binding; and return that one context

QualificationRequirementAccepts(P,requirement_coordinate,candidate) =
  let context = DeriveQualificationSubjectContext(P,candidate); resolve the
  candidate qualification through ResolvedAnalysisQualificationContract;
  let requirement_law =
    ResolvedQualificationRequirementAcceptanceLaw(P,requirement_coordinate);
  require both the qualification contract's subject-parametric acceptance law
  and requirement_law to accept exactly (candidate.proposed_body,
  Authenticate(context.candidate_proposition_id),context); return true only
  when both complete evaluations succeed

AnalysisUsePairAccepts(
    P,requirement_coordinate,named_consumer,typed_purpose,candidate) =
  resolve the consumer and purpose through ResolvedAnalysisUseContract;
  require both contracts.required_qualification to equal
  requirement_coordinate; require the candidate's exact result kind to be
  admitted by both accepted-kind contracts;
  require QualificationRequirementAccepts(
    P,requirement_coordinate,candidate); then apply the two fixed attenuation
  and policy-compatibility laws to that same candidate and return true only
  when the pair agrees without strengthening the result

AnalysisQuestionId =
  AnalysisId<"analysis.question">(B, AnalysisQuestionBody)

AnalysisGoalId =
  AnalysisId<"analysis.goal">(B, AnalysisGoalBody)

AnalysisHypothesisContextId =
  AnalysisId<"analysis.hypothesis-context">(
    B, AnalysisHypothesisContextBody)

AnalysisPropositionId =
  AnalysisId<"analysis.proposition">(B, AnalysisPropositionBody)

AnalysisNamedPremiseId =
  AnalysisId<"analysis.named-premise">(B, AnalysisNamedPremiseBody)

AnalysisQuantitativeFormulaId<S> =
  AnalysisId<"analysis.quantitative-formula">(
    B, AnalysisQuantitativeFormulaBody<S>)

AnalysisSemanticBasisId =
  AnalysisId<"analysis.semantic-basis">(B, AnalysisSemanticBasisBody)

PortableAnalysisSupportInstantiationId =
  AnalysisId<"analysis.support-instantiation">(
    B, AnalysisSupportInstantiationBody)

AnalysisValidationBasisId =
  AnalysisId<"analysis.validation-basis">(B, AnalysisValidationBasisBody)

PortableAnalysisJudgmentRecordId =
  AnalysisId<"analysis.judgment-record">(B, AnalysisJudgmentRecordBody)

IntakeAnalysisNamedPremises(
    exact question,
    supplied: CanonicalMap<AnalysisNamedPremiseRequirement,
                           AnalysisNamedPremiseId>) =
  1. authenticate the question and every supplied premise under the
     question's exact direct Analysis profile;
  2. derive the required key set from question.named_premise_requirements;
  3. return CannotAnswer for a missing key or an absent premise source;
  4. return Refused when a supplied premise is well formed but its kind or
     coordinate differs from the requirement at that slot;
  5. return Malformed for an extra, duplicate, noncanonical, or
     caller-ordered key;
  6. require every premise's model_scope to admit the question: a
     FreshChallengeOnly premise only for a question over a Fresh Protocol, an
     OracleModelOnly premise only for a question whose experiment uses
     exactly that distribution profile, an ExactSubjectsOnly premise only for
     a question over exactly those subjects; RebindRequired admits no
     question;
  7. form exactly one AnalysisGoalBody whose binding map has the required
     key set and no other key; and
  8. expose PremiseIdsOfGoal to every hypothesis node, hypothesis context,
     support instantiation, and judgment that uses that goal.
```

A named premise is the identity-bearing body of one assumption a question
consumes: what it binds, the coordinate it binds to, where it came from, what
evidence accompanies it, and where it may be used. The kind-to-coordinate,
kind-to-bound-value, and kind-to-source relations are closed profile laws; an
unknown case is `Unsupported` and a disallowed pairing is `Malformed`. The
evidence depth records only what evidence accompanies the premise identity:
a source-grounded mapping, a complete typed constructive binding, or a frozen
executable falsification. It never turns an assumption into an established
proposition. A question with an unmet requirement is `CannotAnswer`, never a
question with a default premise; two questions over the same subjects with
different premise bindings have distinct goal, proposition, support, and
judgment identities, because every one of those bodies carries the exact
premise identities it uses. The concrete premise bodies are owned by the
profile whose authenticated import closure can name their coordinates: the
[cryptographic-property profile](cryptographic-properties.md#32-named-premises-of-the-relation-bound-fresh-question)
owns Fresh public-coin distributions, provider outcome-carrier maps, and the
relation and Plan premises, and the
[semantic-transport profile](cryptographic-properties.md#73-family-premises)
owns the Fiat--Shamir family premises. The kernel owns the grammar and the
intake and no concrete premise.

The concrete manifest intentionally carries no purpose field. Its source
profile is the sole authority for slot schema and purpose, while the manifest
is the sole authority for the exact owner occurrence coordinate/value. The
ordinal is their checked join key. Active bounded rule constructors derive
their entire read-purpose sequence with `CompleteReadPurposeRequirements`; no
rule may author a preferred subset such as slot zero.

`CheckedFiniteCoverUniversalDischargeContract` is defined only for the exact
singleton `ForAllValue` shape above. The target experiment cannot contain
`ForAllFamilyValue`, `ForAllLogicalNat`, `ForAllStrategy`, `ExistsStrategy`,
`Sample`, an extractor existential, a quantitative universal, or any other
quantifier beside that one finite-value universal. Consequently this contract
cannot discharge a protocol-family, asymptotic, uniform-strategy,
distributional, probabilistic, expected-value, total-polynomial-time, or other
resource proposition. A finite set of tested indices or sampled executions
cannot be re-encoded as its target. Termination of one bounded representative
stream is not evidence that the candidate algorithm is polynomial time.

The four inputs to this contract have disjoint authority. The semantic basis
identifies the exact logical rule, raw target, checked cover obligations,
candidate algorithm, and success predicates. The support binds independently
established coverage, universal quotient-factorization, and success-transfer
judgments. The
validation basis identifies the independently admitted streaming enumerator,
evaluators, ABIs, finite controls, and residual trust used to carry out that
rule. The stream receipt is occurrence-local replay evidence; it has no
`AnalysisBodyV0` arm, semantic ID, qualification, or authority and cannot fill
the semantic, support, or validation basis. Conversely, representative
enumeration without all three exact certificate capabilities establishes
nothing about the raw universal. Successful application permits the ordinary
affirmative `AnalysisJudgmentRecord` for the target proposition; no special
proof token or premise-binding variant is created.

`AnalysisReadPurposeRequirement` is a closed two-variant algebra. A concrete
requirement selects one slot of one exact admitted concrete manifest. A family
requirement selects one abstract role-slot schema of one exact admitted family
manifest schema. Formation of a semantic basis runs
`NormalizeReadPurposeRequirements` and requires its authored sequence to have
exactly the same canonical order and members as the normalized result. A bare
manifest ID or family-schema ID is not a read-purpose requirement.

Variant tags are semantic. A family atom never expands over `LogicalNat`, and
it never aliases a concrete atom even when a separately checked family-member
correspondence maps their roles to equal-looking fields. Two concrete atoms
under different manifests, or two family atoms under different schemas, also
remain distinct. Equality requires the same variant, complete manifest or
schema ID, in-range slot ordinal, exact resolved slot, and purpose. Duplicate
requirements are rejected rather than silently collapsed. A specialization
from a family atom to a concrete atom is a separate checked transform with its
own correspondence premise; it is not read-purpose normalization.

The normalized sequence must equal the complete read-purpose requirement
sequence derived by the resolved native or theorem rule for the authenticated
`exact_question_id` and its exact question context. The basis family must equal
that question's resolved family, and a later proposition may use the basis only
when its goal names that same question. Every concrete requirement must name a manifest present on the
concrete side of that context; every family requirement must name a family
schema present on its abstract side; and `SourceFree` requires the empty
sequence. A missing required slot, an extra ambient slot, a concrete/family
substitution, or a purpose that differs from the resolved slot refuses basis
formation. Source support later binds the manifests and schemas selected here;
it does not reinterpret their purposes.

Every native rule coordinate and body must resolve through
`ResolvedAnalysisNativeRuleContract(P,rule_coordinate)`. Admission checks its canonical payload,
allowed conclusion family, complete premise-requirement sequence, and typed
transform program against that one contract. A native rule schema contains no
future semantic-basis ID, proposition ID, support binding, checker, or live
capability. An imported theorem uses the disjoint
`ImportedTheoremRuleSource` variant; a theorem ID cannot be re-encoded as a
native rule payload. Unknown rule declarations are `Unsupported`, malformed
payloads are `Malformed`, and provider disagreement is `CheckerFailure`.

Every `AnalysisQuestionBody` first resolves its complete `family` declaration
through `ResolvedAnalysisFamilyContract(P,family)`. The family contract admits every and only
the exact subject kinds, context variant, context members, and family payload
that it specifies. Every referenced manifest and experiment profile must resolve,
must have the subject domain required by that contract, and must be listed in the
question context exactly once in canonical order. A family context's
`family_definition_id` must equal the family definition used by every dependent
manifest and experiment profile in that context. A family-instance context must
add the exact concrete side selected by the family contract; it cannot use an
abstract family carrier as a portable subject reference.

An `AnalysisGoalBody` contains only `question_id`. Admission resolves that exact
question body and derives both `GoalFamily` and `HypothesisFreeConclusion`
through the selected profile's unique reconstruction law. Neither value is a
caller-authored goal field. Thus a caller cannot pair one family's question
with another family's conclusion, choose a second conclusion admitted by the
same carrier schema, or change an encoded duplicate while retaining the same
question.

Every actual-result qualification resolves through
`ResolvedAnalysisQualificationContract`; every qualification requirement
resolves through `ResolvedAnalysisQualificationRequirementContract`; and every
named consumer and typed purpose resolves through
`ResolvedAnalysisUseContract`. A use contract names one qualification-
requirement coordinate, and that requirement selects its one fixed
subject-parametric acceptance law through
`ResolvedQualificationRequirementAcceptanceLaw`. Display text,
caller-selected strings, and byte equality between a requirement tag and an
actual qualification do not define acceptance.

The requirement-to-law resolver is total only on the exact closed requirement
declarations admitted by its profile. It receives only the complete
requirement coordinate and body, not the candidate, and returns one typed law
ref already present in the authenticated law-source/import closure. It cannot
consult a runtime registry, choose a law from candidate data, or synthesize a
new law term. Zero results, multiple results, a wrong signature, or a law from
outside the closure refuses resolution before qualification evaluation.

Qualification admission is well-founded in this order: authenticate the fixed
profile and law source; authenticate the already formed proposition, goal,
question, and hypothesis context; validate every nonqualification field of one
`AnalysisJudgmentCandidate`; derive its `QualificationSubjectContext`; resolve
the candidate's actual qualification and the required acceptance law; and only
then admit the complete judgment body. A fixed profile law receives the
candidate body, authenticated proposition, and derived context as invocation
arguments. Its law-source bytes contain no candidate proposition, goal,
question, hypothesis-context, semantic-basis, support, validation-basis, or
future judgment ID. The law may branch only on closed declaration coordinates
and fields derived from the authenticated candidate. It cannot predict a
future governed ID, accept an authored context literal, or select a second
profile at evaluation time. This order applies equally when an existing
judgment is checked for a later use: authentication recovers the candidate
body, and acceptance is recomputed rather than inherited from its display
qualification.

An `ExactAffirmativeJudgmentCapabilityBinding` is accepted only through
`AnalysisUsePairAccepts` using its one requirement, consumer, purpose, and the
authenticated bound judgment as candidate. The consumer and purpose must name
that same requirement; two individually valid declarations that resolve to
different requirements cannot be paired. The actual-result qualification law,
requirement law, kind filters, attenuation laws, and policy-compatibility laws
therefore all evaluate the same derived subject context. No literal
qualification tag or context ID can bypass the resolver.

For an
`ExactQuantifiedWitnessRequirement`, admission resolves
`quantified_role.experiment_profile_id`, selects the in-range quantifier at
`quantifier_ordinal`, and requires its constructor and bound extractor profile
to equal `expected_quantifier_kind` and `exact_profile_id`. The supplied witness
must inhabit that exact quantified carrier. A display binder name, another
existential in the same prefix, or a profile-equivalent algorithm cannot fill
the requirement.

Analysis-internal bodies retain the exact declaration coordinates above.
When a foreign owner API, including PIR static-view issuance, requires a
same-regime `TypedContentId` for its consumer or purpose intake, Analysis passes
the corresponding `AnalysisConsumerIntakeId` or `AnalysisUsePurposeIntakeId`.
Each wrapper has exactly one declaration-ref field and selects that
ref's exact resolving profile `P` (the profile parameter of
`AnalysisProfileDeclarationRef<P,K>`). For an imported declaration this is the
importing resolution context, not the target profile named by the imported
arm. The wrapper adds no use semantics and cannot replace the
declaration ref inside an Analysis basis, support, policy, or capability
requirement. A wrapper under another profile, for another declaration, or with
an added label is a different or malformed intake coordinate.

Hypothesis nodes refer to goals and earlier local ordinals, never recursively
to the proposition being formed. `roots` is the exact outward hypothesis
frontier. Every dependency reachable from that frontier is also a required
hypothesis; dependency edges order obligations but never establish them.
For a nonempty context, `roots` is uniquely derived as the canonical sorted
sequence of every node that is not reachable by a nonempty dependency path from
another node. Equivalently, it is the unique set of all reachability-maximal
nodes of the authenticated DAG; that set is an antichain at the outward edge. A
root reachable from another root is redundant and malformed. Every node must be
reachable from this derived frontier.
Unreachable nodes, a caller-authored nonmaximal frontier, forward edges,
duplicate goals, or noncanonical root order are malformed. The empty context
has empty `nodes` and `roots`.

The domains of `established_hypothesis_node_bindings` and
`assumed_hypothesis_node_bindings` are disjoint and partition exactly every
node in the reachable closure of `roots`, not merely the roots themselves.
An established entry supplies the exact affirmative judgment capability
required by its node; an assumed entry retains that exact goal as a logical
hypothesis. `NoExternalSourceValidation` is required for every ordinary
assumption. An assumed `TheoremTruth` goal instead requires
`ImportedTheoremSourceValidation(V)`, where V resolves to the exact
`AnalysisTheoremSourceValidationBody` naming the theorem schema in that goal
and selecting `ImportedPaperOnly` plus
`RetainedTheoremTruthAssumption`. Neither variant is accepted for the other
kind. A dependency edge, proof-plan ordering, duplicated goal, bare citation,
or source record for another theorem cannot fill either binding.

The reusable partition elaborator is total and canonical:

```text
AnalysisHypothesisNodeTreatment =
    Established(ExactAffirmativeJudgmentCapabilityBinding)
  | Assumed(ExactlyAssumedGoal)

ExactHypothesisTreatmentPartition(
    GammaId,GammaBody,supplied_treatments) =
  authenticate GammaId against GammaBody; derive the canonical ascending
  sequence of every reachable local ordinal; require supplied_treatments to be
  a CanonicalMap<LocalOrdinal,AnalysisHypothesisNodeTreatment> whose key domain
  is exactly that sequence; for an Established entry authenticate the exact
  affirmative capability required by that node; for an Assumed entry require
  the exact goal and source-validation variant required by that node; reject a
  missing, extra, duplicate, wrong-goal, wrong-qualification, wrong-profile,
  noncanonical, or live-capability-free Established entry; return that exact
  canonical map

EstablishedPartitionOf(partition) =
  require partition to be an output of ExactHypothesisTreatmentPartition;
  return the CanonicalMap<LocalOrdinal,
    ExactAffirmativeJudgmentCapabilityBinding> containing exactly its
  Established entries with tags removed, in inherited key order

AssumedPartitionOf(partition) =
  require partition to be an output of ExactHypothesisTreatmentPartition;
  return the CanonicalMap<LocalOrdinal,ExactlyAssumedGoal> containing exactly
  its Assumed entries with tags removed, in inherited key order
```

The two projections are disjoint, their key union is exactly the partition
domain, and neither accepts an authored replacement map. Concrete inherited-
support combinators must return an `ExactHypothesisTreatmentPartition` for
their named target context before either projection is defined.

`non_hypothesis_premise_bindings` binds every and only the semantic basis's
`NamedPremiseRequirement`, `AffirmativeJudgmentCapabilityRequirement`, and
`ExactQuantifiedWitnessRequirement` entries. It is disjoint from hypothesis-
node treatment. Theorem truth is an ordinary exact goal node in the target
context, so its established-versus-assumed treatment also belongs only in the
two hypothesis-node maps. Its source/proof validation is not a semantic premise:
the assumed path carries the exact source-validation ID in
`ExactlyAssumedGoal`; the established path reaches the exact checked-proof
validation ID through the authenticated theorem-truth judgment's validation
basis. Missing, extra, duplicated, wrong-purpose, wrong-theorem, or wrong-
qualification bindings are malformed or refused according to the common
outcome rules.

An `AnalysisSemanticBasisBody` is admitted only for its authenticated
`exact_question_id`: its `family` equals the question's resolved family, its
`conclusion_schema` reconstructs exactly that question's hypothesis-free goal
body, its complete read-purpose sequence is derived from that question
context, and its rule source's resolved contract admits the family, complete
premise-requirement sequence, and typed transform. When the basis is applied to
one proposition, each hypothesis-node requirement must name that proposition's
exact hypothesis context and authenticated node; every non-hypothesis premise
is disjoint from that node domain. A basis is reusable only across proposition
applications of that exact question for which the same resolved rule
requirements hold, so it contains no support coordinate, live capability,
established/assumed choice, or future judgment ID.

An `AnalysisSupportInstantiationBody` resolves both its proposition and semantic
basis and requires the exact proposition/family/goal triple admitted by that
basis, including equality between the proposition goal's question and the
basis's `exact_question_id`. Its non-hypothesis bindings fill every and only the corresponding premise
requirements; its two hypothesis maps partition every reachable node; and its
source-support domain equals the resolved question context as specified below.
No binding for another proposition, family member, manifest, purpose, or local
owner can be accepted by structural similarity.

An `AnalysisJudgmentRecordBody` resolves the proposition, basis, support, and
validation basis before formation. Its inherited hypothesis context equals the
proposition's context, its `exact_family_conclusion` equals
`HypothesisFreeConclusion` of the resolved goal, its semantic basis and support coordinates equal the
ones just resolved, and its typed quantitative result is admitted by that
family's exact result schema and by the basis transform. Polarity,
qualification, operation policy, and policy closure do not relax any of these
equalities. A mismatch is `Malformed` when the body is noncanonical or
ill-typed, and otherwise `Refused`; it never creates a second interpretation.

The validation basis contains every and only the theorem-source-validation ID
directly used by the checking attempt or by an established theorem-truth
treatment. An assumed theorem-truth treatment instead commits that ID in the
support map, because it explains why that logical premise was retained rather
than discharged. Changing source bytes, locators, bibliographic revision,
proof artifact, or truth-discharge metadata therefore rotates validation or
support identities without rotating the theorem schema, question, goal, or
proposition. Changing the theorem's semantic statement rotates its theorem ID
and necessarily every validation/support body that references it.

Its policy summary is also derived rather than authored:

```text
DerivedJudgmentPolicyDependencyClosure(
    operation_policy_id,support_instantiation) =
  CanonicalSortedUniqueUnion(
    [operation_policy_id],
    every DerivedOwnerPolicyDependencyClosure reached through the support's
      exact source-support bindings,
    every operation-policy ID and derived policy closure reached through an
      established non-hypothesis or hypothesis judgment binding)

ExactAffirmativeAnalysisJudgmentBody(
    proposition_id,typed_quantitative_result,semantic_basis_id,
    support_coordinate,validation_basis_id,qualification,
    operation_policy_id) =
  authenticate the proposition, its goal and question, the semantic basis,
  support, validation basis, qualification contract, and operation policy;
  require the basis and support to select that exact proposition and each
  other and the quantitative result to inhabit the family's exact result
  schema; derive body = AnalysisJudgmentRecordBody {
    proposition_id: proposition_id,
    polarity: Affirmative,
    exact_family_conclusion:
      HypothesisFreeConclusion(Authenticate(
        Authenticate(proposition_id).goal_id)),
    inherited_hypothesis_context_id:
      Authenticate(proposition_id).hypothesis_context_id,
    typed_quantitative_result: typed_quantitative_result,
    semantic_basis_id: semantic_basis_id,
    support_coordinate: support_coordinate,
    validation_basis_id: validation_basis_id,
    qualification: qualification,
    operation_policy_id: operation_policy_id,
    derived_source_policy_dependency_closure:
      DerivedJudgmentPolicyDependencyClosure(
        operation_policy_id,Authenticate(support_coordinate))
  }; derive candidate = AnalysisJudgmentCandidate {
    exact_direct_profile_id:
      RequiredAnalysisLanguageProfile(
        ExactConstructorCaseOf(body),"analysis.judgment-record",body,
        AuthenticatedPredecessors(body)),
    proposed_body: body
  }; derive its QualificationSubjectContext and require the resolved
  qualification contract's subject_parametric_acceptance_law to accept
  exactly (body,Authenticate(proposition_id),that context); then return body
```

The support and hypothesis graphs are authenticated and acyclic before this
union is traversed. Formation requires
`derived_source_policy_dependency_closure` to equal the result exactly; a
missing dependency, extra policy, cycle, duplicate, or caller order is
malformed. This summary changes judgment identity only when an actually used
policy dependency changes and grants no authority by itself.

For compact domain specifications, the following is one derived canonical
constructor rather than prose shorthand:

```text
AllReachableHypothesisNodeRequirements(GammaId,GammaBody) =
  CanonicalSeq, in GammaBody local-ordinal order, containing exactly
  HypothesisNodeRequirement {
    hypothesis_context_id: GammaId,
    node_ordinal: node.local_ordinal,
    exact_goal_id: node.goal_id
  }
  for every node reachable from GammaBody.roots

ReachableHypothesisGoalIds(GammaId,GammaBody) =
  after the same authentication and reachability checks, the canonical
  sorted-unique sequence of exactly `node.goal_id` for every node reachable
  from GammaBody.roots

ExactNonHypothesisPremiseBindingMap(
    semantic_basis_id,semantic_basis_body,supplied_bindings) =
  1. authenticate `semantic_basis_id` against `semantic_basis_body`;
  2. derive the canonical key set consisting of every and only
     `NamedPremiseRequirement`, `AffirmativeJudgmentCapabilityRequirement`,
     and `ExactQuantifiedWitnessRequirement` entry in
     `semantic_basis_body.exact_premise_schemas`;
  3. authenticate every supplied binding, derive the unique requirement it
     satisfies from its exact slot, kind, and coordinate for a named premise,
     or from its exact proposition/quantified role, qualification, consumer,
     purpose, and profile otherwise, and reject zero or multiple matches; and
  4. return the canonical map from that exact key set to the matched bindings,
     rejecting a missing, extra, duplicate, or caller-authored key.

The empty derived key set and empty supplied sequence produce the unique empty
canonical map. A display list of bindings in a concrete constructor is always
an argument to this elaborator; a bare sequence never inhabits
`non_hypothesis_premise_bindings`.

UniqueOrdinalOfGoal(GammaBody,goal_id) =
  the one local ordinal whose authenticated node has exactly goal_id; missing
  or non-unique lookup is malformed

OutwardFrontier(nodes) =
  CanonicalSortedUniqueSeq of exactly those node ordinals that do not occur in
  the nonempty transitive dependency closure of any other node

CanonicalGoalDagUnion(
    contexts: CanonicalNonEmptySeq<AnalysisHypothesisContextBody>) =
  1. authenticate every input context, replace each local dependency ordinal by
     its exact goal ID, and group nodes by complete goal ID;
  2. for each goal ID, take the canonical set union of every grouped dependency
     goal-ID set, preserving every input dependency;
  3. reject a missing dependency, self-edge, or cycle;
  4. assign fresh local ordinals by the unique canonical topological order that
     repeatedly selects the least complete goal ID among nodes whose dependency
     goal IDs have already been assigned;
  5. rewrite dependency goal IDs to those fresh earlier ordinals; and
  6. set roots to OutwardFrontier(the rewritten nodes).
```

`AllReachableHypothesisNodeRequirements`, `ReachableHypothesisGoalIds`, and
`UniqueOrdinalOfGoal` first
authenticate `GammaId` against `GammaBody` and refuse an unreachable node,
duplicate ordinal or goal, forward edge, or cycle. Neither constructor
establishes nor assumes any node; the support partition records that treatment.
`CanonicalGoalDagUnion` never unions caller-supplied root lists. It derives the
one maximal outward frontier after goal merging and dependency union. Equal goals
with different dependency sets therefore acquire the exact canonical union of
those dependencies; a cycle introduced by that merge is malformed. Input order,
display names, and redundant roots cannot change the result.
The domain of `source_support_bindings` is exactly the manifest sequence in an
exact question context, with no missing or extra entry. For a family context it
is a dependent support schema checked at each referenced family member. A
concrete member binding enters only a `FamilyInstanceContext`, which requires
both the family support schema and every concrete manifest support with no
ambient bridge between them. The domain is empty for `SourceFree` questions and
may contain both source and target supports for theorem applicability.

A quantitative formula is part of a family conclusion only through its
basis-neutral formula ID. Its body may refer to family parameters, exact
positive-polynomial values, and the closed native arithmetic constructors
selected by the owning family, but never to a theorem schema, proof, semantic
basis, loss-result occurrence, checker, or live capability. A theorem or native
rule may establish a transform *to* an already formed formula in
`AnalysisSemanticBasisBody.typed_transform_program`; it cannot make theorem
provenance part of the formula or ordinary property-question identity.
Admission derives the expression's exact free-parameter set and requires
`declared_parameter_independence` to equal the ordered complement within
`parameter_schema`; callers cannot hide a used parameter or pad the list.

Potentially local values use one disjoint coordinate type:

```text
AnalysisCoordinate<T> =
    Portable(T)
  | OwnerLocal(LocalAnalysisHandle<kind(T), owner, owner_generation>)

AnalysisSourceSupportCoordinate =
  AnalysisCoordinate<PortableAnalysisSourceSupportId>

AnalysisSupportInstantiationCoordinate =
  AnalysisCoordinate<PortableAnalysisSupportInstantiationId>

AnalysisJudgmentRecordCoordinate =
  AnalysisCoordinate<PortableAnalysisJudgmentRecordId>
```

Portable formation is legal only when the exact body and every transitive
reference are portable and every governing policy permits portable addressing.
A value that semantically depends on an owner-local occurrence, satisfaction,
loss result, source support, or hypothesis receives only a collision-free local
handle. Such a handle has no digest, serialization, equality by copied
structure, or exact cold replay. A canonical collection containing local
coordinates may compare them only within the same owner and generation.

`SourceFree` is admitted only for a family whose meaning requires no source
read or experiment, initially exact theorem truth. It cannot be used to omit a
required manifest or model from a property or applicability question.

The active universal Schnorr question remains portable when its exact public-
setup invocation view is portable. An AFK question is portable only when its
PIR-owned `CheckedFSConstructionResultRef` and every other selected source
coordinate are portable; otherwise owner-local taint propagates through its
manifest, question, goal, and proposition. Concrete run views, checked
correspondence or loss results, consumer joins, and live capabilities occur in
support or invocation. A future family whose
proposition itself names a concrete local occurrence propagates the local
coordinate through its hypothesis, proposition, support, judgment, and every
dependent value.

The hypothesis-free `AnalysisGoalId` is the sole target of correspondence
questions. Concrete correspondence proposition IDs belong in the hypothesis
context or support instantiation, never inside the goal. This breaks the
applicability/correspondence identity cycle.

### 4.2 Identity sensitivity

Changing any semantic subject, read manifest, quantifier order, strategy
class, model, outcome law, theorem schema, property conclusion, parameter map,
or typed transform changes the appropriate ID. Changing a checker
implementation, proof search tactic, timeout, cache, request priority, or
observation receipt does not change proposition meaning; it may change the
validation basis or operational attempt.

Owner-local source coordinates and every Analysis value whose own body names
them use process-local handles rather than portable IDs. Taint flows forward
through actual dependency, not backward into an otherwise portable question.
No value depending on an owner-local satisfaction or lossy-use capability has
a portable digest or exact cold replay.

## 5. Hypotheses, basis, support, and validation

### 5.1 Hypothesis context

The canonical hypothesis DAG retains:

- unproved mathematical or cryptographic assumptions;
- imported theorem truth when no accepted proof authority is supplied;
- model and algorithm correspondences that are propositions rather than
  definitional coordinates;
- group, field, sampler, termination, and resource side conditions; and
- occurrence-local loss premises.

An assumption is represented once, in the canonical hypothesis context. A
support ledger records how that proposition was treated; it does not duplicate
the proposition in judgment identity.

Model coordinates are not removable hypotheses. Checker correctness,
canonical decoding correctness, provider conformance, and runtime integrity are
residual trust, not logical premises.

### 5.2 Four independent roles

```text
SemanticBasis
  defines the inference rule and exact conclusion transformation

SupportInstantiation
  binds every established premise occurrence and every retained assumption

ValidationBasis
  defines how this check was carried out and translated

AnalysisJudgmentRecord
  states the exact qualified semantic result
```

An admitted theorem schema says what an implication means. A paper citation or
schema admission does not establish theorem truth. If theorem truth is assumed,
its exact proposition remains in the result hypotheses. A future checked proof
may discharge that same proposition without changing the question or theorem
schema.

Every inherited hypothesis is canonically unioned exactly once. A transform
may discharge a hypothesis only through an exact affirmative premise binding
authorized by its semantic basis.

### 5.3 Operation policy

```text
AnalysisOperationPolicy = {
  supported_families_and_models:
    CanonicalSortedUniqueSeq<TypedSemanticSubjectRef>,
  named_consumer_and_typed_purpose_permissions:
    CanonicalMap<AnalysisNamedConsumerCoordinate,
                 CanonicalSortedUniqueSeq<AnalysisTypedPurposeCoordinate>>,
  capability_freshness_and_lifetime:
    AnalysisProfileLawRef<CapabilityFreshnessAndLifetimeLaw>,
  disclosure_policy: AnalysisProfileLawRef<DisclosureLaw>,
  unknown_question_disposition:
    AnalysisProfileLawRef<UnknownQuestionDisposition>,
  persistence_policy: AnalysisProfileLawRef<PersistenceLaw>,
  cold_replay_policy: AnalysisProfileLawRef<ColdReplayLaw>
}

AnalysisOperationPolicyBody = AnalysisOperationPolicy

AnalysisOperationPolicyId =
  AnalysisId<"analysis.operation-policy">(B, AnalysisOperationPolicyBody)
```

Policy never changes proposition meaning. It governs whether an otherwise
well-formed result may be minted, disclosed, persisted, replayed, or consumed
for one named purpose.

Concrete Analysis result constructors use the following total elaborators. They
remove no fields from the bodies above and accept no prose placeholders:

```text
AnalysisOperationPolicyLawBundle = {
  capability_freshness_and_lifetime:
    AnalysisProfileLawRef<CapabilityFreshnessAndLifetimeLaw>,
  disclosure_policy: AnalysisProfileLawRef<DisclosureLaw>,
  unknown_question_disposition:
    AnalysisProfileLawRef<UnknownQuestionDisposition>,
  persistence_policy: AnalysisProfileLawRef<PersistenceLaw>,
  cold_replay_policy: AnalysisProfileLawRef<ColdReplayLaw>
}

PolicySubjectClosure(proposition_id) =
  authenticate the proposition, goal, and question; return the canonical
  sorted-unique sequence of exactly the question's `exact_subjects` plus every
  exact typed family/model subject referenced by its context; declaration refs,
  display labels, support coordinates, and capabilities are excluded

ExactAnalysisOperationPolicyBody(
    proposition_id,permission_map,law_bundle) = AnalysisOperationPolicyBody {
  supported_families_and_models: PolicySubjectClosure(proposition_id),
  named_consumer_and_typed_purpose_permissions:
    permission_map : CanonicalMap<
      AnalysisNamedConsumerCoordinate,
      CanonicalSortedUniqueSeq<AnalysisTypedPurposeCoordinate>>,
  capability_freshness_and_lifetime:
    law_bundle.capability_freshness_and_lifetime,
  disclosure_policy: law_bundle.disclosure_policy,
  unknown_question_disposition:
    law_bundle.unknown_question_disposition,
  persistence_policy: law_bundle.persistence_policy,
  cold_replay_policy: law_bundle.cold_replay_policy
}

ExactAnalysisValidationBasisBody(
    checker_contracts,translations,finite_controls,
    directly_consumed_theorem_source_validation_ids,residual_trust_roots) =
  AnalysisValidationBasisBody {
    admitted_checker_contract_ids_and_abis:
      CanonicalNonEmptySortedUniqueSeq(checker_contracts),
    exact_translation_contracts: CanonicalSortedUniqueSeq(translations),
    finite_control_contracts: CanonicalSortedUniqueSeq(finite_controls),
    theorem_source_validation_ids:
      CanonicalSortedUniqueSeq(
        directly_consumed_theorem_source_validation_ids),
    residual_trust_roots: CanonicalSortedUniqueSeq(residual_trust_roots)
  }
```

Each input is an exact typed value authenticated under the selected direct
profile; the sequence notation above is canonical construction, not a cast.
The theorem-source sequence is exact-used: an assumed theorem-truth treatment
places its source-validation ID only in support, an established theorem-truth
treatment places it here only when the checking attempt actually consumes it,
and neither path may duplicate it in both locations.

### 5.4 Live authority

A completed affirmative or family-defined negative may mint a fresh,
process-local capability bound to:

```text
exact judgment record
semantic basis
support instantiation
validation basis
source authority bindings and policy closure
Analysis operation-policy ID
polarity and qualification
named consumer and typed purpose
```

The capability is nonserializable and nonreconstructible. An inert record may
be authenticated and replayed, but cannot satisfy a live premise slot. Failed,
unsupported, unanswered, refused, malformed, over-limit, or checker-failed
attempts mint no partial capability.

Analysis does not define a second common authority envelope. For a completed
Analysis result it owns only the payloads needed to instantiate Foundation's envelope:

```text
AnalysisCheckedResultCoordinateBody(result) = {
  result_id: TypedSemanticSubjectRef,
  proposition_id: AnalysisPropositionId,
  semantic_basis_id: AnalysisSemanticBasisId,
  support_id: PortableAnalysisSupportInstantiationId,
  validation_basis_id: AnalysisValidationBasisId,
  qualification: AnalysisQualificationCoordinate,
  outcome_kind: Affirmative | FamilyDefinedNegative
}

AnalysisCapabilityRequirementPayloadBody = {
  proposition_id: AnalysisPropositionId,
  qualification_requirement: AnalysisQualificationRequirementCoordinate,
  named_consumer: AnalysisNamedConsumerCoordinate,
  typed_purpose: AnalysisTypedPurposeCoordinate
}

AnalysisSourceAuthorityContractBody = {
  owner_coordinate: TypedSemanticSubjectRef,
  checked_result_coordinate_id: AnalysisCheckedResultCoordinateId,
  capability_requirement_payload_id:
    AnalysisCapabilityRequirementPayloadId,
  immediate_policy_ids:
    CanonicalSingleton<AnalysisOperationPolicyId>,
  transitive_policy_ids:
    CanonicalSortedUniqueSeq<TypedContentId>
}

AnalysisOwnerPolicyClosureBody(contract) = {
  owner_coordinate: contract.owner_coordinate,
  policy_ids: CanonicalSortedUniqueUnion(
    contract.immediate_policy_ids,contract.transitive_policy_ids),
  derivation_law:
    AnalysisProfileLawRef<DerivedUsedPolicyClosureLaw>
}

AnalysisCheckedResultCoordinateId =
  AnalysisId<"analysis.checked-result-coordinate">(
    B,AnalysisCheckedResultCoordinateBody)

AnalysisCapabilityRequirementPayloadId =
  AnalysisId<"analysis.capability-requirement-payload">(
    B,AnalysisCapabilityRequirementPayloadBody)

AnalysisSourceAuthorityContractId =
  AnalysisId<"analysis.source-authority-contract">(
    B,AnalysisSourceAuthorityContractBody)

AnalysisOwnerPolicyClosureId =
  AnalysisId<"analysis.owner-policy-closure">(
    B,AnalysisOwnerPolicyClosureBody)
```

Formation derives the checked-result coordinate from the authenticated
completed result and its judgment when one exists. It requires
`immediate_policy_ids` to be exactly the owner result's one selected operation
policy and `transitive_policy_ids` to be exactly the remaining IDs in that
result's derived used-policy closure. For an Analysis judgment that closure is
`DerivedJudgmentPolicyDependencyClosure`; an explicit external-proof treatment
uses the exact separately authenticated external-owner closure admitted by its
Analysis rule. Thus neither sequence is an independent policy assertion.

The unique portable embedding is then:

```text
PortableAnalysisSourceAuthorityEnvelope(c) = PortableSourceAuthorityBinding {
  owner_domain: "analysis",
  capability_family: "checked-result-use",
  owner_source_coordinate: c.checked_result_coordinate_id,
  owner_binding_payload: AnalysisSourceAuthorityContractId(c),
  operation_policy: BoundTo(the singleton c.immediate_policy_ids[0]),
  owner_policy_closure: AnalysisOwnerPolicyClosureId(c),
  capability_requirement: OwnerCapabilityRequirement {
    owner_domain: "analysis",
    capability_family: "checked-result-use",
    owner_requirement: c.capability_requirement_payload_id
  }
}

PortableAnalysisSourceAuthorityBindingBody(c) =
  Foundation PortableSourceAuthorityBindingBody(
    PortableAnalysisSourceAuthorityEnvelope(c))

PortableAnalysisSourceAuthorityBindingId(c) =
  AnalysisId<"analysis.portable-source-authority-binding">(
    B,PortableAnalysisSourceAuthorityBindingBody(c))
```

The Analysis checked-result coordinate, contract, requirement-payload, derived
closure, and portable-binding IDs all select the exact direct profile of the
completed owner result. Their declaration references must resolve through that
profile's authenticated import cone. They are therefore property-profiled for
a property result, transport-profiled for a semantic-transport result, and
source-validation-profiled for a result whose support or validation basis
consumes theorem-source validation. A parent profile cannot carry a child-
profiled dependency, and a caller cannot choose a broader profile. The outer
record is exactly Foundation's canonical inert `PortableSourceAuthorityBindingBody`.
Formation re-derives that record and requires body equality. No Analysis-
defined `OwnerCapabilityRequirement` or second `PortableSourceAuthorityBinding`
exists. The separately fresh Analysis capability binds this exact envelope,
consumer, purpose, evaluator, and invocation; none of those live values enters
the portable body.

Cross-profile consumption never lifts or remints that owner envelope. When a
property-profiled result is consumed by a transport-profile-only consumer, or
a transport-profiled result is consumed by the source-validation child, the
owner requirement names an exact export consumer and export purpose declared
in the result's own profile. The importing profile may then perform this live,
nonportable attenuation:

```text
AttenuateAnalysisAuthorityForImport(
    exact_parent_envelope,
    matching_parent_live_capability,
    child_consumer: AnalysisNamedConsumerCoordinate,
    child_purpose: AnalysisTypedPurposeCoordinate,
    attenuation_law:
      AnalysisProfileLawRef<ImportedAnalysisAuthorityAttenuationLaw>) =
  authenticate the parent envelope under the completed result's exact direct
  profile; authenticate the child declarations and attenuation law under the
  one exact importing child profile; require the law to map that exact parent
  export consumer/purpose to the child pair without strengthening polarity,
  qualification, proposition, lifetime, disclosure, or policy; and return one
  fresh child-invocation capability
```

This operation has no `AnalysisBodyV0` arm, portable ID, or cold-replay form.
Its result is bound to the parent envelope ID, child profile ID, complete
consumer and purpose coordinates, invocation, and evaluator. A missing live
parent capability, an unrelated child, a broader policy, a reverse import, or
an ad-hoc profile refuses. Same-profile use bypasses this adapter and must match
the owner requirement directly. Thus the portable carrier always retains the
completed result profile while a later importing profile can express a
narrower authorized use without a semantic back-edge.

## 6. Qualified outcomes and negative meaning

```text
AnalysisAttemptOutcome<F> =
    Affirmative(EstablishedAnalysisJudgment<F>)
  | Negative(EstablishedAnalysisNegative<F>)
  | Unsupported(exact coordinate)
  | MissingDependency(absent exact authenticated dependency)
  | CannotAnswer(missing exact source, premise, or authority)
  | KindMismatch(wrong exact owner, profile, regime, or semantic kind)
  | Refused(exact prohibited or failed applicability condition)
  | Malformed(exact structural or canonical defect)
  | DeterministicLimitExceeded(exact bounded operation)
  | CheckerFailure(exact evaluator/provider disagreement)

AnalysisAttemptFailurePartition =
    Unsupported(exact unsupported family, model, or coordinate)
  | MissingDependency(absent exact authenticated dependency)
  | CannotAnswer(exact missing source, premise, authority, or support)
  | KindMismatch(wrong exact owner, profile, regime, or semantic kind)
  | Refused(exact prohibited use or failed applicability condition)
  | Malformed(exact structural or canonical defect)
  | DeterministicLimitExceeded(exact bounded operation)
  | CheckerFailure(exact evaluator/provider disagreement)

CommonAnalysisAttemptFailurePartitionRef<P> =
  the unique AnalysisProfileLawRef<P,AnalysisAttemptFailurePartition> whose
  resolved body is exactly AnalysisAttemptFailurePartition above
```

Only a family with a complete decision or refutation semantics may emit
`Negative`. Failure to derive an affirmative result is not a negative.
Theorem inapplicability is not a negative target property. A wrong model or
map normally refuses the application; an unsupported family or oracle model
is `Unsupported`. The common failure partition excludes `Affirmative` and
`Negative`; it classifies only qualified noncompletion after exact outcome
formation. Every family, rule, qualification, use profile, source-ingress
contract, and transport profile that claims the common partition must carry
`CommonAnalysisAttemptFailurePartitionRef<P>` for its exact selected profile.
A prose phrase, imported ref to another body, or caller-selected substitute is
not the common partition.

## 7. Requests, replay, and lifecycle

An operational request names the exact question or proposition, acceptable
bases, resource limits, checker policy, named consumer, and typed purpose. It
does not enter proposition identity. A checking invocation additionally
contains every fresh source/checker capability and immutable dependency
snapshot required for that occurrence.

Analysis cold replay reauthenticates the exact semantic bodies, reconstructs
the source manifests, reruns the admitted basis/checker operations, and
compares the inert result. It cannot recreate owner-local authority, PIR causal
generation, strategy membership, random-oracle behavior, or cryptographic
forking.

## 8. Closure boundary

This page closes the reusable Analysis ingress and common calculus only for the
active profiles named by the domain index. It does not select a universal
proof language, theorem database, persistence format, cache, solver, or
general composition algebra. New families must define their own exact source
manifest, experiment, property, negative meaning, quantitative sort and
operations, semantic basis, and validation boundary before admission.

<!-- zkc-profile-source:analysis-kernel-domain-semantics:end -->
