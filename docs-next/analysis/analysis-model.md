# Analysis semantic model

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-C target
> **Target status:** Bounded minimum kernel; broader Analysis remains deferred
> **Provisional owner:** `analysis`
> **Authority:** This page defines a redesign target for `docs-next/`. The
> current specifications under [`docs/`](../../docs/README.md) remain
> authoritative until explicit consolidation and cutover. This page establishes
> no theorem truth, property, implementation, migration, or reliance claim.

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

### 2.1 Source read slots

Analysis imports the project-owned `ExactSourceAuthorityBinding`; it does not
redefine that record. One manifest slot has the following Analysis-owned
meaning:

```text
AnalysisSemanticReadSlot = {
  owner_domain,
  source_family,
  exact_semantic_coordinate,
  read_purpose: SemanticMeaning | PremiseSupport | OccurrenceEvidence,
  selected_fields: CanonicalNonEmptySeq<OwnerFieldCoordinate>,
  adequacy_requirement,
  source_binding_schema,
  required_authority_class: None | FreshSourceCapability,
  failure_disposition
}

AnalysisFamilyRoleReadSlotSchema = {
  abstract_role_coordinate: LocalAnalysisSourceFamilyRoleRef,
  read_purpose: SemanticMeaning | PremiseSupport,
  dependent_signature,
  adequacy_requirement,
  failure_disposition
}

LocalAnalysisSourceFamilyRoleRef = {
  local_role_ordinal: Natural,
  exact_role_tag: ModuleDeclarationRef<"analysis.family-role-kind">
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
    selected_fields,adequacy_requirement,source_binding_schema,
    required_authority_class,failure_disposition) =
  OwnerSourceReadSlotSchema(AnalysisSemanticReadSlot schema {
    owner_domain,
    source_family,
    exact_semantic_coordinate: semantic_coordinate_schema,
    read_purpose,
    selected_fields,
    adequacy_requirement,
    source_binding_schema,
    required_authority_class,
    failure_disposition
  })

AbstractFamilyRoleReadSlotSchema(
    abstract_role_coordinate,read_purpose,dependent_signature,
    adequacy_requirement,failure_disposition) =
  AbstractFamilyRoleSlotSchema(AnalysisFamilyRoleReadSlotSchema {
    abstract_role_coordinate,
    read_purpose,
    dependent_signature,
    adequacy_requirement,
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
  ModuleDeclarationRef<"analysis.source-family">

AnalysisSourceFamilyDeclarationBody = {
  allowed_slot_variant: ConcreteOwnerSource | AbstractFamilyRole,
  exact_slot_and_field_schema,
  exact_adequacy_schema,
  failure_classification
}

AnalysisSourceFamilySemanticsContract = {
  allowed_slot_variant: ConcreteOwnerSource | AbstractFamilyRole,
  exact_slot_and_field_schema,
  exact_adequacy_schema,
  failure_classification
}

AnalysisSourceFamilySemanticsCatalog(B) =
  the authenticated semantic-regime mapping from each complete resolved
  AnalysisSourceFamilyCoordinate and declaration body to exactly one immutable
  AnalysisSourceFamilySemanticsContract

AnalysisSourceProfile = {
  family_tag: AnalysisSourceFamilyCoordinate,
  slot_schemas: CanonicalNonEmptySeq<AnalysisSourceReadSlotSchema>,
  closed_field_read_set,
  adequacy_predicate
}

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

The complete source-family declaration and body must resolve in
`AnalysisSourceFamilySemanticsCatalog(B)`, and its selected contract must admit
the profile's slot variant and exact slot/field/adequacy schemas. A display
name, free symbol, or declaration with the right spelling but another body is
`Unsupported`; malformed payload or slot structure is `Malformed`. Adding or
changing a source-family contract rotates the semantic regime.

```text
AnalysisSemanticReadManifest = {
  source_profile_id: AnalysisSourceProfileId,
  exact_subjects: CanonicalNonEmptySeq<SemanticContentId>,
  slots: CanonicalSortedUniqueSeq<AnalysisSemanticReadSlot>
}

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
    exact_source_authority_binding,
    owner_capability_requirement
  }>,
  owner_policy_dependency_closure
}

PortableAnalysisSourceSupportId =
  AnalysisId<"analysis.source-support">(B, AnalysisSourceSupportBody)
```

`AnalysisSourceSupport` is portable only when every owner coordinate permits
it; otherwise it is a collision-free `LocalAnalysisSourceSupportHandle` with
no portable ID. Matching fresh capabilities are
supplied separately at the checking occurrence and enter no portable identity.
Changing a source check, result origin, qualification, or policy binding may
change support without changing the semantic question.

### 2.3 Asymptotic family ingress

K1 authenticates finite semantic descriptions and K2 Protocols use finitely
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

AnalysisFamilyLanguageSemanticsCatalog(B) =
  the authenticated semantic-regime mapping from the complete resolved
  ModuleDeclarationRef and exact declaration body to one immutable
  AnalysisAsymptoticFamilyLanguageContract

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
    exact declaration grammar, a matching entry in
    AnalysisFamilyLanguageSemanticsCatalog(B), successful lift of
    payload_type, and an Analysis provider conforming to that catalog entry,
  non_claims:
    declaration admission establishes no member existence, uniqueness,
    coherence, algorithm implementation, resource law, or theorem
}

AnalysisAsymptoticProtocolFamilyDefinitionBody(
    language_ref:ModuleDeclarationRef<"analysis.asymptotic-family-language">,
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
  language contract; it is not a K1 `CanonicalValue`, K2 Protocol, K3
  relation object, or portable algorithm

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

The catalog is part of the exact semantic-regime descriptor in `B`, not a live
provider registry. Each entry is keyed by the complete declaration coordinate
and body and fixes the payload interpretation and mathematical denotation law.
Changing an entry therefore rotates the semantic regime; provider code only
implements the already selected law and disagreement is `CheckerFailure`.
An unlisted declaration is `Unsupported`, not provider-defined meaning.

The initial admitted catalog entry is the closed indexed-protocol-signature
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
are propositions. This exact nominal-signature entry is sufficient for K3-C; a
computational or proof-assistant family language requires a new catalog entry
and regime.

The declaration kind above has exactly the three-field body grammar shown; a
different record, payload type, or revision is malformed or unsupported. The
catalog contract fixes the input and result signatures, while the selected
declaration and payload fix the language-specific mathematical relation. That relation is
not a K1 portable executable and is not evaluated by bounded K1 iteration.
K1 authenticates only the finite declaration reference and payload.

The family-read-manifest schema likewise has exactly the two fields shown.
Its member projection and coherence obligation are derived from the closed
source-profile slot catalog and the fixed abstract-member signature; they are
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
under K1's finite value and body limits. For one representable concrete `n0`,
an admitted K1/K2/K3 subject `S` is related to the abstract member only through
a separately checked `FamilyInstanceCorrespondence(F,n0,S)` proposition. `F`
contains neither derived projections nor concrete members, theorem IDs,
proposition IDs, or correspondence results, so the dependency direction is
acyclic and callers cannot author parallel family fields that disagree.

A fixed K2 subject can support finite tests and a specialized pointwise
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

The first six are derived from one K2 Core. A Fresh-only property need not and
must not select transcript-construction or FS fields merely because a later
transport may use them. `TranscriptDeclarationView`,
`RequiredInfluenceView`, and `ChallengeTransitionView` are derived from one
exact K2 transcript construction. `FSConstructionView` is derived only from the
exact affirmative `CheckedFSConstruction` and carries the paired Fresh/FS
Protocol IDs, shared Core, maps, and structural conclusion. The manifest checks
the owner result schema plus the exact transcript-construction/Fresh/FS/Core
subject coordinates. Its support binds the concrete qualified result record,
and the checking invocation supplies the matching fresh capability; there is no
`CheckedFSConstructionId`. The manifest checks that all source coordinates
agree. It never contains a second event schedule, transcript declaration,
influence graph, challenge sampler, or Protocol body.

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
exact K3-B CorrespondenceQuestion IDs and owner refs for Statement,
  claim, and Witness coordinates
exact K2 CheckRef and CheckDecl algorithm/evaluation-contract/input fields
exact K2 TerminalRef and TerminalDecl verdict/required-check/disposition fields
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
  role,
  dependent_parameter_schema,
  strategy_abi,
  private_state_type,
  initial_advice_type,
  allowed_views,
  allowed_oracles_and_capabilities,
  legal_move_relation,
  stop_and_noncompletion_law,
  resource_dimensions
}

AnalysisStrategyClassProfileId =
  AnalysisId<"analysis.strategy-class">(B, StrategyClassProfileBody)
```

For a K2 prover, each interactive step must inhabit the exact K2 boundary:

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
Quantifier =
    ForAllStrategy(
      AnalysisStrategyClassProfileId, dependent_domain_predicate,
      bound_variable)
  | ExistsStrategy(
      AnalysisStrategyClassProfileId, dependent_domain_predicate,
      bound_variable)
  | Sample(AnalysisDistributionProfileId, bound_variable)
  | ForAllValue(ValueType, domain_predicate, bound_variable)
  | ForAllFamilyValue(
      AnalysisAsymptoticProtocolFamilyDefinitionId,
      dependent_abstract_sort,
      dependent_domain_predicate,
      bound_variable)
  | ForAllQuantitativeValue(
      AnalysisQuantitativeSort, domain_predicate, bound_variable)
  | ForAllLogicalNat(domain_predicate, bound_variable)
  | ExistsPositivePolynomial(
      AnalysisPositivePolynomialProfileId, bound_variable)
  | ExistsExtractor(AnalysisExtractorProfileId, bound_variable)
  | ExistsUniformBlackBoxExtractor(
      AnalysisExtractorProfileId, bound_variable)
  | ExistsUniformExtractorFamily(
      AnalysisExtractorProfileId, bound_variable)

QuantifierPrefix = NonEmptyOrderedSeq<Quantifier>
```

Reordering adaptive statement choice, setup, public coins, advice, strategy,
oracle sampling, or extractor choice creates a different experiment. There is
no normalization that commutes quantifiers merely because two fixtures happen
to produce the same finite runs.

`ForAllValue` ranges only over one admitted finite K1 `ValueType`.
`ForAllFamilyValue` ranges over an abstract dependent mathematical carrier
denoted by one family at the already bound `LogicalNat`; its denotation and
domain predicate remain family hypotheses. The two constructors are not
interchangeable, and a finite native value enumeration cannot establish a
`ForAllFamilyValue` conclusion.

The referenced profile kinds are closed Analysis semantic objects:

```text
AnalysisDistributionProfile = {
  output_type,
  exact support predicate,
  exact probability mass or measure law,
  parameter and security-parameter coordinates,
  independence/correlation declarations,
  sampling or oracle denotation,
  failure and nontermination law
}

AnalysisExtractorProfile = {
  input and output types,
  private state and randomness types,
  allowed source/oracle capabilities,
  rerun, fork, rewind, and programming rights,
  state-preservation relation,
  output-distribution preservation relation,
  witness-success relation,
  termination and asymptotic resource law,
  counterfactual capability contract and property-family scope
}

AnalysisPositivePolynomialProfile = {
  input_sort: LogicalNat | StatementLength(statement_type),
  coefficient_domain: Nat,
  value_shape: CanonicalNonEmptySeq<Nat> in low-to-high order,
  canonical_degree_rule: highest coefficient is nonzero unless degree is zero,
  evaluation: exact checked-natural Horner evaluation,
  positivity_rule: constant coefficient is at least one,
  admitted coefficient and degree bounds
}

AnalysisPositivePolynomial = {
  profile_id: AnalysisPositivePolynomialProfileId,
  coefficients_low_to_high: CanonicalNonEmptySeq<Nat>
}

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

The initial uniform Fresh-coin and classical random-oracle profiles define
their exact finite-output laws with these bodies. The initial AFK extractor
profile alone grants its lazy-sampling, rerun, and programming rights. Naming
an extractor algorithm or a distribution label without these laws does not
form either profile. Extractor profiles are theorem-neutral; a theorem schema
selects one exact profile, never the reverse, so their identities cannot cycle.
The positive-polynomial profile is the bounded K3-C representation over which
the existential ranges; each admitted polynomial value has its own ID. It is
not a caller-supplied numerical bound or an ambient complexity claim. The
selected `q_KS(n) = 1` witness is
`AnalysisPositivePolynomialId(profile, [1])`. Broader polynomial
representations require a new profile.

### 3.3 Experiment profile

```text
AnalysisExperimentProfile = {
  family,
  source_profile_id: AnalysisSourceProfileId,
  quantifier_prefix,
  role_interfaces,
  setup_and_input_sampling,
  randomness_ownership_and_independence,
  public_coin_or_oracle_model,
  scheduler,
  generated_execution_relation,
  observation_and_win_event,
  failure_abort_and_noncompletion_law,
  termination_law,
  resource_basis,
  output_type
}

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

For an ordinary K2 run, `generated_execution_relation` invokes the K2
generated-execution semantics. `StrategyStopped`, invalid moves, future reads,
verifier failure, sampling exhaustion, and accepted/rejected terminals retain
their exact source dispositions; a family profile states which contribute to
its win event. It cannot silently drop an outcome that benefits its bound.

### 3.4 Oracle and resource discipline

Oracle access is capability-typed. An adversary receives query operations, not
the hidden table. Lazy sampling, programming, rewind, or fork rights exist only
inside an exact theorem experiment that grants them; they are not K2 replay
capabilities.

```text
ResourceDimension = {
  operation_role: ModuleDeclarationRef<"analysis.resource-operation">,
  value_sort,
  owner_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  dependent_parameter_schema: CanonicalSeq<AnalysisParameterSchemaEntry>,
  capability_abi_or_algorithm_schema,
  lifetime_scope,
  aggregation: Sum | Maximum | Expected,
  exact_counter_event
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

## 4. K1-aligned semantic identities

### 4.1 One identity algebra

Every portable Analysis semantic object uses the exact authenticated K1 prior-
meta basis `B` and the existing semantic-regime axis:

```text
AnalysisId<K>(B, body) = SemanticContentId<K>(B, body)
```

There is no separate `AnalysisSemanticRegimeId`, no free `H(...)`, and no
identity derived from display text, a citation label, or a live capability.
Each body is a closed `MetaValueV0` tagged record with canonical finite
sequences and exact typed references.

The common dependent types used below are not open metavariables. They are
resolved through authenticated, regime-fixed catalogs:

```text
AnalysisFamilyCoordinate =
  ModuleDeclarationRef<"analysis.property-family">

AnalysisFamilySemanticsContract = {
  exact_subject_schema,
  exact_question_payload_meta_schema,
  exact_hypothesis_free_conclusion_meta_schema,
  question_to_conclusion_reconstruction_law,
  allowed_question_context_variants,
  exact_quantitative_result_schema,
  affirmative_and_negative_meaning,
  failure_classification
}

AnalysisFamilySemanticsCatalog(B) =
  the authenticated semantic-regime mapping from each complete resolved
  AnalysisFamilyCoordinate and declaration body to exactly one immutable
  AnalysisFamilySemanticsContract

ExactFamilyQuestionPayload<f> =
  the canonical MetaValueV0 accepted by f's resolved question-payload schema

ExactFamilyConclusion<f> =
  the canonical MetaValueV0 accepted by f's resolved conclusion schema

TypedSemanticSubjectRef<K> =
  the exact ContentRefV0 of an authenticated SemanticContentId<K>, where K is
  admitted by the consuming family contract and source profile

TypedSemanticSubjectRef =
  the closed kind-indexed union of TypedSemanticSubjectRef<K> admitted by the
  active Analysis family and source catalogs

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

LocalParameterRef<S> =
  an earlier in-range local ordinal whose declared sort is exactly S

BasisNeutralQuantitativeExpr<S> =
  a canonical typed MetaValueV0 expression admitted by the authenticated
  Analysis quantitative-expression catalog for result sort S
```

The active expression constructors and their formation rules are closed in
[`cryptographic-properties.md`](cryptographic-properties.md#6-typed-quantitative-language).
Display names such as `n`, `Q`, and `epsilon` are expository aliases for local
ordinals and do not enter an identity body. An unknown family declaration,
payload schema, conclusion schema, subject kind, quantitative sort, or
expression constructor is `Unsupported`; a malformed or ill-typed instance is
`Malformed`. Provider code cannot add meaning to these catalogs at runtime.

The active K3-C property-family declaration set is exactly:

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
```

Each spelling above denotes one exact module declaration, not a string tag.
The family owner page fixes its dependent payload and conclusion schemas. A
new family or a changed schema requires a new declaration and a semantic-
regime-supported catalog entry.

The active `AnalysisFamilySemanticsCatalog(B)` is the canonical key-sorted union
of the exact owner entry sets in this page's durable Analysis documents.
Admission rejects a missing active key, an extra entry, duplicate coordinates
across owner sets, or two contracts for the same complete declaration. Owner
entry sets are specification partitions only: the resulting catalog is one
authenticated semantic-regime value, not a runtime registry or search order.

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
  adequacy predicate
}

analysis.source-support = {
  semantic-read-manifest ID, exact portable source bindings and requirements,
  source-policy dependency closure
}

analysis.question = {
  family, exact subjects, source-free or semantic-experiment context,
  family-owned question payload
}

analysis.goal = {
  question ID, exact hypothesis-free family conclusion
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
  exact authority/revision and statement digest, source/target property and
  experiment schemas, maps, side conditions, resources, typed transform,
  conclusion reconstruction law
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
  residual-trust roots
}

analysis.operation-policy = {
  supported family and model coordinates, named consumer/purpose permissions,
  capability lifetime, disclosure, unknown-question disposition,
  persistence and cold-replay rules
}

analysis.judgment-record = {
  proposition ID, polarity, exact conclusion, inherited hypotheses,
  quantitative result, semantic-basis ID, support ID,
  validation-basis ID, qualification and policy closure
}
```

The list above is exhaustive for the active K3-C kernel. It is a compact field
catalog, not permission to invent a different preimage. The exact closed body
types and nominal constructors that were not already formed in Sections 2 and
3 are:

```text
AnalysisQuestionContext =
    SourceFree(exact_source_free_family_reason)
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

AnalysisQuestionBody = {
  family: AnalysisFamilyCoordinate,
  exact_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
  context: AnalysisQuestionContext,
  family_payload: ExactFamilyQuestionPayload<family>
}

AnalysisGoalBody = {
  question_id: AnalysisQuestionId,
  conclusion_family: AnalysisFamilyCoordinate,
  hypothesis_free_conclusion: ExactFamilyConclusion<conclusion_family>
}

AnalysisHypothesisNode = {
  local_ordinal,
  goal_id: AnalysisGoalId,
  dependency_ordinals: CanonicalSortedUniqueSeq<EarlierLocalOrdinal>
}

AnalysisHypothesisContextBody = {
  nodes: CanonicalSeq<AnalysisHypothesisNode>,
  roots: CanonicalSortedUniqueSeq<LocalOrdinal>
}

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
  ModuleDeclarationRef<"analysis.native-rule">

AnalysisNativeRuleSemanticsContract = {
  exact_payload_meta_schema,
  allowed_conclusion_families:
    CanonicalNonEmptySeq<AnalysisFamilyCoordinate>,
  exact_premise_requirement_schema,
  exact_typed_transform_program_schema,
  conclusion_reconstruction_law,
  failure_classification
}

AnalysisNativeRuleSemanticsCatalog(B) =
  the authenticated semantic-regime mapping from each complete resolved
  AnalysisNativeRuleCoordinate and declaration body to exactly one immutable
  AnalysisNativeRuleSemanticsContract

NativeRuleSchema = {
  rule_coordinate: AnalysisNativeRuleCoordinate,
  canonical_rule_payload:
    CanonicalValue<resolved and lifted payload type of rule_coordinate>
}

AnalysisRuleSource =
    NativeRuleSource(NativeRuleSchema)
  | ImportedTheoremRuleSource(AnalysisTheoremSchemaId)

AnalysisQualificationRequirementCoordinate =
  ModuleDeclarationRef<"analysis.qualification-requirement">

AnalysisNamedConsumerCoordinate =
  ModuleDeclarationRef<"analysis.named-consumer">

AnalysisTypedPurposeCoordinate =
  ModuleDeclarationRef<"analysis.typed-purpose">

AnalysisUseSemanticsContract = {
  accepted_subject_and_result_kinds,
  qualification_predicate_or_exact_match,
  capability_attenuation_law,
  operation_policy_compatibility_law,
  failure_classification
}

AnalysisUseSemanticsCatalog(B) =
  the authenticated semantic-regime mapping from each complete resolved
  qualification-requirement, named-consumer, and typed-purpose coordinate and
  declaration body to exactly one immutable AnalysisUseSemanticsContract

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
    HypothesisNodeRequirement {
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

AnalysisSemanticBasisBody = {
  family: AnalysisFamilyCoordinate,
  rule_source: AnalysisRuleSource,
  exact_premise_schemas:
    CanonicalSortedUniqueSeq<AnalysisPremiseRequirement>,
  source_read_purposes,
  conclusion_schema,
  typed_transform_program
}

AnalysisSupportInstantiationBody = {
  semantic_basis_id: AnalysisSemanticBasisId,
  proposition_id: AnalysisPropositionId,
  non_hypothesis_premise_bindings,
  established_hypothesis_node_bindings,
  assumed_hypothesis_node_bindings,
  source_support_bindings: CanonicalSortedUniqueSeq<
      ExactManifestSupportBinding {
        semantic_read_manifest_id: AnalysisSemanticReadManifestId,
        source_support_coordinate: AnalysisSourceSupportCoordinate
      }
    | FamilyManifestSupportSchemaBinding {
        family_read_manifest_schema_id: AnalysisFamilyReadManifestSchemaId,
        dependent_support_schema,
        exact retained family-support hypotheses
      }>
}

AnalysisValidationBasisBody = {
  admitted_checker_contract_ids_and_abis,
  exact_translation_contracts,
  finite_control_contracts,
  residual_trust_roots
}

AnalysisJudgmentRecordBody = {
  proposition_id: AnalysisPropositionId,
  polarity,
  exact_family_conclusion,
  inherited_hypothesis_context_id: AnalysisHypothesisContextId,
  typed_quantitative_result,
  semantic_basis_id: AnalysisSemanticBasisId,
  support_coordinate: AnalysisSupportInstantiationCoordinate,
  validation_basis_id: AnalysisValidationBasisId,
  qualification,
  operation_policy_id: AnalysisOperationPolicyId,
  source_policy_dependency_closure
}

AnalysisQuestionId =
  AnalysisId<"analysis.question">(B, AnalysisQuestionBody)

AnalysisGoalId =
  AnalysisId<"analysis.goal">(B, AnalysisGoalBody)

AnalysisHypothesisContextId =
  AnalysisId<"analysis.hypothesis-context">(
    B, AnalysisHypothesisContextBody)

AnalysisPropositionId =
  AnalysisId<"analysis.proposition">(B, AnalysisPropositionBody)

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
```

Every native rule coordinate and body must resolve in
`AnalysisNativeRuleSemanticsCatalog(B)`. Admission checks its canonical payload,
allowed conclusion family, complete premise-requirement sequence, and typed
transform program against that one contract. A native rule schema contains no
future semantic-basis ID, proposition ID, support binding, checker, or live
capability. An imported theorem uses the disjoint
`ImportedTheoremRuleSource` variant; a theorem ID cannot be re-encoded as a
native rule payload. Unknown rule declarations are `Unsupported`, malformed
payloads are `Malformed`, and provider disagreement is `CheckerFailure`.

Every `AnalysisQuestionBody` first resolves its complete `family` declaration in
`AnalysisFamilySemanticsCatalog(B)`. The family contract admits every and only
the exact subject kinds, context variant, context members, and family payload
that it specifies. Every referenced manifest and experiment profile must resolve,
must have the subject domain required by that contract, and must be listed in the
question context exactly once in canonical order. A family context's
`family_definition_id` must equal the family definition used by every dependent
manifest and experiment profile in that context. A family-instance context must
add the exact concrete side selected by the family contract; it cannot use an
abstract family carrier as a portable subject reference.

An `AnalysisGoalBody` is admitted only after resolving `question_id` to one exact
question body. `conclusion_family` MUST equal that question's `family`, and
`hypothesis_free_conclusion` MUST equal the unique conclusion reconstructed by
that family's `question_to_conclusion_reconstruction_law`; accepting merely a
value of the same conclusion meta-schema is insufficient. Thus a caller cannot
pair one family's question with another family's conclusion, or choose a second
conclusion admitted by the same carrier schema.

Every qualification requirement, named consumer, and typed purpose must likewise
resolve as a complete declaration in `AnalysisUseSemanticsCatalog(B)`. These
coordinates select exact capability acceptance and attenuation laws; display
text and caller-selected strings do not. For an
`ExactQuantifiedWitnessRequirement`, admission resolves
`quantified_role.experiment_profile_id`, selects the in-range quantifier at
`quantifier_ordinal`, and requires its constructor and bound extractor profile
to equal `expected_quantifier_kind` and `exact_profile_id`. The supplied witness
must inhabit that exact quantified carrier. A display binder name, another
existential in the same prefix, or a profile-equivalent algorithm cannot fill
the requirement.

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
hypothesis. A dependency edge, proof-plan ordering, or duplicated goal cannot
fill either binding.

`non_hypothesis_premise_bindings` binds every and only the semantic basis's
`AffirmativeJudgmentCapabilityRequirement` and
`ExactQuantifiedWitnessRequirement` entries. It is disjoint from hypothesis-
node treatment. Theorem truth is an ordinary exact goal node in the target
context, so its established-versus-assumed treatment also belongs only in the
two hypothesis-node maps. Missing, extra, duplicated, wrong-purpose, or wrong-
qualification bindings are malformed or refused according to the common
outcome rules.

An `AnalysisSemanticBasisBody` is admitted only for one exact proposition goal:
its `family` equals the resolved goal's conclusion family, its
`conclusion_schema` reconstructs that exact goal body, and its rule source's
resolved contract admits that family, the complete premise-requirement sequence,
and the typed transform. Each hypothesis-node requirement names the proposition's
exact hypothesis context and authenticated node; every non-hypothesis premise is
disjoint from that node domain. A basis is a reusable semantic derivation schema,
so it contains no support coordinate, live capability, established/assumed
choice, or future judgment ID.

An `AnalysisSupportInstantiationBody` resolves both its proposition and semantic
basis and requires the exact proposition/family/goal triple admitted by that
basis. Its non-hypothesis bindings fill every and only the corresponding premise
requirements; its two hypothesis maps partition every reachable node; and its
source-support domain equals the resolved question context as specified below.
No binding for another proposition, family member, manifest, purpose, or local
owner can be accepted by structural similarity.

An `AnalysisJudgmentRecordBody` resolves the proposition, basis, support, and
validation basis before formation. Its inherited hypothesis context equals the
proposition's context, its `exact_family_conclusion` equals the goal's unique
hypothesis-free conclusion, its semantic basis and support coordinates equal the
ones just resolved, and its typed quantitative result is admitted by that
family's exact result schema and by the basis transform. Polarity,
qualification, operation policy, and policy closure do not relax any of these
equalities. A mismatch is `Malformed` when the body is noncanonical or
ill-typed, and otherwise `Refused`; it never creates a second interpretation.

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

`AllReachableHypothesisNodeRequirements` and `UniqueOrdinalOfGoal` first
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

The active universal Schnorr and AFK questions remain portable because their
semantic manifests name only portable subjects and occurrence/map schemas.
Concrete run views, checked correspondence or loss results, consumer joins,
and live capabilities occur in support or invocation. A future family whose
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
  supported_families_and_models,
  named_consumer_and_typed_purpose_permissions,
  capability_freshness_and_lifetime,
  disclosure_policy,
  unknown_question_disposition,
  persistence_policy,
  cold_replay_policy
}

AnalysisOperationPolicyId =
  AnalysisId<"analysis.operation-policy">(B, AnalysisOperationPolicyBody)
```

Policy never changes proposition meaning. It governs whether an otherwise
well-formed result may be minted, disclosed, persisted, replayed, or consumed
for one named purpose.

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

## 6. Qualified outcomes and negative meaning

```text
AnalysisAttemptOutcome<F> =
    Affirmative(EstablishedAnalysisJudgment<F>)
  | Negative(EstablishedAnalysisNegative<F>)
  | Unsupported(exact coordinate)
  | CannotAnswer(missing exact source, premise, or authority)
  | Refused(exact prohibited or failed applicability condition)
  | Malformed(exact structural or canonical defect)
  | DeterministicLimitExceeded(exact bounded operation)
  | CheckerFailure(exact evaluator/provider disagreement)
```

Only a family with a complete decision or refutation semantics may emit
`Negative`. Failure to derive an affirmative result is not a negative.
Theorem inapplicability is not a negative target property. A wrong model or
map normally refuses the application; an unsupported family or oracle model
is `Unsupported`.

## 7. Requests, replay, and lifecycle

An operational request names the exact question or proposition, acceptable
bases, resource limits, checker policy, named consumer, and typed purpose. It
does not enter proposition identity. A checking invocation additionally
contains every fresh source/checker capability and immutable dependency
snapshot required for that occurrence.

Analysis cold replay reauthenticates the exact semantic bodies, reconstructs
the source manifests, reruns the admitted basis/checker operations, and
compares the inert result. It cannot recreate owner-local authority, K2 causal
generation, strategy membership, random-oracle behavior, or cryptographic
forking.

## 8. Closure boundary

This page closes the reusable K3-C ingress and common calculus only for the
active profiles named by the domain index. It does not select a universal
proof language, theorem database, persistence format, cache, solver, or
general composition algebra. New families must define their own exact source
manifest, experiment, property, negative meaning, quantitative sort and
operations, semantic basis, and validation boundary before admission.
