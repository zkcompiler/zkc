# Analysis theorem applicability, transport, and replay

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative Analysis target
> **Target status:** Minimum theorem-applicability and property-transport seam
> **Provisional owner:** `analysis`
> **Authority:** This page defines a redesign target only. Current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.
> It establishes no theorem truth, transported property, replayed authority,
> implementation support, or consumer reliance.

<!-- zkc-profile-source:analysis-theorem-validation-semantics:start -->

## 1. Three separate contracts

The Analysis Fresh-to-Fiat--Shamir path is:

```text
CheckedFSConstruction
  structural same-Core construction result owned by PIR

ApplicableTheoremInstance
  Analysis result that one exact theorem schema matches exact source/target
  experiments, maps, side conditions, substitutions, and typed transform

PropertyTransport
  Analysis operation consuming one exact affirmative source-property judgment
  plus one exact affirmative applicability result and one explicit theorem-
  truth binding to construct the target conditional judgment
```

None implies the next. In particular:

- an admitted FS Protocol does not imply a checked construction;
- a checked construction establishes no property or theorem applicability;
- theorem applicability establishes neither theorem truth nor a source
  premise;
- an applicable theorem transports nothing without the exact affirmative
  source judgment and an established or retained-assumption theorem-truth
  binding; and
- transport establishes only its independently reconstructed target
  proposition with every retained hypothesis and quantitative term.

## 2. Theorem schema and applicability

### 2.1 Admitted theorem schema

For the closed theorem records on this page,
`TheoremProfileLawRef(body_schema,field_ordinal,signature)` denotes the unique
exact `AnalysisProfileLawRef<signature>` at that field in the directly selected
`AnalysisAFKTransportLanguageProfileId`. This standalone profile imports exactly
`AnalysisCryptographicPropertyLanguageProfileId`; it neither copies that profile's
catalogs nor imports any additional owner profile not referenced by its closed
contracts. A displayed mathematical or English
expansion in a schema-, interpretation-, coherence-, transform-, map-,
side-condition-, failure-, or conclusion-law field is reader-facing expansion
of that ref and is not encoded. Literal coordinates, IDs, enums, ordinals,
canonical payloads, sequences, maps, and records are encoded as displayed by
`AnalysisBodyV0`.

Every extensible theorem-schema component uses the same closed declaration-
plus-payload pattern:

```text
TheoremSchemaComponent<C> = {
  contract_ref: AnalysisProfileDeclarationRef<C>,
  canonical_payload:
    CanonicalValue<resolved and lifted payload type of contract_ref>
}

AnalysisTheoremComponentSemanticsContract<P,C> = {
  exact_component_payload_meta_schema:
    AnalysisProfileLawRef<ClosedTheoremComponentPayloadSchema<C>>,
  admitted_local_binding_kinds_and_occurrence_paths:
    CanonicalSortedUniqueSeq<TheoremBindingOccurrencePath>,
  exact_component_interpretation_law:
    AnalysisProfileLawRef<TheoremComponentInterpretationLaw<C>>,
  cross_component_coherence_law:
    AnalysisProfileLawRef<TheoremComponentCoherenceLaw<C>>,
  failure_classification:
    CommonAnalysisAttemptFailurePartitionRef<P>
}

ResolvedAnalysisTheoremComponentContract(P,component) =
  the one theorem-component contract of the same component kind resolved from
  P's authenticated `AnalysisLanguageProfileLawProgramV0` by the complete
  declaration coordinate and body

TheoremLocalBindingKind =
    AsymptoticFamilyParameter
  | LogicalNatParameter(exact earlier family-binding ordinal)
  | PositivePolynomialParameter(input_sort:LogicalNat)
  | QuantitativeParameter(exact dependent AnalysisQuantitativeSort template)
  | QuantifiedStrategyParameter(exact strategy or extractor role schema)
  | SemanticRole(exact role schema)
  | ChallengeCardinalityRole(exact earlier dependency ordinals)
  | ResourceRole(exact ResourceDimension template)

TheoremLocalBindingDeclaration = {
  local_ordinal: Natural,
  binding_kind: TheoremLocalBindingKind,
  dependency_ordinals: CanonicalSortedUniqueSeq<EarlierLocalOrdinal>,
  exact_denotation_schema: AnalysisProfileLawRef<TheoremLocalDenotationSchema>
}

LocalTheoremBindingRef<K> =
  an in-range local ordinal in the enclosing theorem schema's one binding
  catalog whose declaration has exactly binding kind K

TheoremTemplateOperandSort =
    ConcreteAnalysisSort(AnalysisQuantitativeSort)
  | LocalChallengeCardinality(
      LocalTheoremBindingRef<ChallengeCardinalityRole>)
  | LocalQueryCount(LocalTheoremBindingRef<ResourceRole<QueryCount>>)
  | LocalExpectedCount(LocalTheoremBindingRef<ResourceRole<ExpectedCount>>)
  | LocalPositivePolynomial(
      LocalTheoremBindingRef<PositivePolynomialParameter>)

TheoremTemplateQuantitativeExpr<S> =
  the closed typed `AnalysisLawTerm<TheoremQuantitativeTemplate<S>>` using only
  local parameter ordinals, earlier LocalTheoremOperatorRef ordinals,
  theorem-local role/resource refs, and the arithmetic constructors admitted
  by the theorem-transform contract; it contains no Analysis subject, family,
  formula, proposition, or theorem ID

LocalTheoremOperatorDeclaration = {
  local_ordinal: Natural,
  operand_sorts: CanonicalSeq<TheoremTemplateOperandSort>,
  result_sort: TheoremTemplateOperandSort,
  exact_template: TheoremTemplateQuantitativeExpr<result_sort>
}

AnalysisTheoremSchemaBody = {
  local_binding_catalog:
    CanonicalNonEmptySeq<TheoremLocalBindingDeclaration>,
  source_property_schema:
    TheoremSchemaComponent<"analysis.theorem-property-schema">,
  target_property_schema:
    TheoremSchemaComponent<"analysis.theorem-property-schema">,
  source_experiment_schema:
    TheoremSchemaComponent<"analysis.theorem-experiment-schema">,
  target_experiment_schema:
    TheoremSchemaComponent<"analysis.theorem-experiment-schema">,
  required_source_view_schemas:
    CanonicalNonEmptySeq<TheoremSchemaComponent<
      "analysis.theorem-source-view-schema">>,
  map_schemas:
    CanonicalNonEmptySeq<TheoremSchemaComponent<
      "analysis.theorem-map-schema">>,
  side_condition_and_parameter_schemas:
    CanonicalNonEmptySeq<TheoremSchemaComponent<
      "analysis.theorem-side-condition-schema">>,
  local_quantitative_operator_catalog:
    CanonicalSeq<LocalTheoremOperatorDeclaration>,
  typed_resource_and_loss_transform_program:
    TheoremSchemaComponent<"analysis.theorem-transform-program">,
  exact_conclusion_reconstruction_law:
    TheoremSchemaComponent<"analysis.theorem-conclusion-law">
}

AnalysisTheoremSchemaId(B,body:AnalysisTheoremSchemaBody) =
  AnalysisId<"analysis.theorem-schema">(B,body)

ResolvedAnalysisTheoremSchema(T) =
  the unique authenticated `(direct_profile_id,AnalysisTheoremSchemaBody)`
  whose admitted profiled semantic identity is exactly T

TheoremStatementDigest(T) =
  SHA256(M(AnalysisBodyV0(
    ResolvedAnalysisTheoremSchema(T).direct_profile_id,
    ResolvedAnalysisTheoremSchema(T).body)))

TheoremSourceAuthorityBody = {
  publication_kind:
    AnalysisProfileDeclarationRef<"analysis.theorem-source-kind">,
  stable_source_id: Bytes,
  bibliographic_revision: {
    version: Bytes,
    date: Bytes
  },
  artifact_media_type: Bytes,
  artifact_sha256: Bytes32,
  exact_locators: CanonicalNonEmptySeq<Bytes>
}

TheoremTruthDischargeMetadata = {
  authority_class:
      ImportedPaperOnly
    | CheckedProofArtifact,
  admitted_proof_artifact:
      None
    | Some(TypedSemanticSubjectRef),
  truth_discharge_mode:
      RetainedTheoremTruthAssumption
    | EstablishedByCheckedProof,
  schema_admission_establishes_truth: exactly false
}

AnalysisTheoremSourceValidationBody = {
  theorem_schema_id: AnalysisTheoremSchemaId,
  source_authority: TheoremSourceAuthorityBody,
  truth_discharge_metadata: TheoremTruthDischargeMetadata
}

AnalysisTheoremSourceValidationId(B,body) =
  AnalysisId<
    "analysis.theorem-source-validation",
    AnalysisAFKTheoremSourceValidationLanguageProfileId>(B,body)

TheoremTruthSourceFreeReasonRef =
  the one exact
  AnalysisProfileLawRef<SourceFreeFamilyReason> in
  AnalysisAFKTransportLanguageProfileId whose law states that theorem-truth meaning
  is reconstructed solely from the authenticated theorem-schema subject and
  requires no source manifest or experiment; bibliographic and proof-source
  validation remain outside the question

TheoremTruthQuestion(T:AnalysisTheoremSchemaId) = AnalysisQuestionBody {
  family: TheoremTruth,
  exact_subjects: [T],
  context: SourceFree(TheoremTruthSourceFreeReasonRef),
  family_payload: {
    theorem_schema_id: T,
    conclusion_schema: DenotationOf(T) holds for every admitted parameter
      instance satisfying T's exact premise and side-condition schemas
  },
  named_premise_requirements: []
}

TheoremTruthGoal(T) = AnalysisGoalBody {
  question_id: AnalysisQuestionId(B,TheoremTruthQuestion(T)),
  named_premise_bindings: {}
}

TheoremTruthPropositionBody(T) = AnalysisPropositionBody {
  goal_id: AnalysisGoalId(B,TheoremTruthGoal(T)),
  hypothesis_context_id:
    AnalysisHypothesisContextId(B,{nodes: [], roots: [], exact_named_premise_ids: []})
}

TheoremTruthPropositionId(T:AnalysisTheoremSchemaId) =
  AnalysisPropositionId(B,TheoremTruthPropositionBody(T))
```

All component declaration bodies and their lifted payload laws are part of the
exact theorem semantic-language profile directly committed by the theorem body.
Every component resolves through
`ResolvedAnalysisTheoremComponentContract(P,component)`, and its canonical payload must
match that entry's exact meta-schema and interpretation law. They are not an
open theorem-provider API. A component with the right prose label but a
different declaration, payload, binding ordinal, operator ordinal, type, or
template forms a different schema or is unsupported. `AnalysisTheoremSchemaId`
is an admitted `TypedSemanticSubjectRef<"analysis.theorem-schema">`.

The schema's local binding catalog is the only binder and role environment for
all of its components. Local ordinals are zero-based, contiguous, unique, and
may depend only on earlier ordinals. Every component occurrence of a family,
logical index, quantified polynomial, quantitative parameter, strategy,
extractor, semantic role, challenge cardinality, or resource role must use the
exact typed `LocalTheoremBindingRef` declared for that occurrence. Admission
derives the complete canonical use set by traversing every component and local
operator AST and requires every declaration to have at least one use. A free
display symbol, an undeclared occurrence, a wrong-kind reference, an unused
declaration, or inconsistent cross-component binding is malformed.
Display spellings such as `F`, `n`, `Q`, `Statement`, and `Witness` are aliases
only and never enter the schema body.

The theorem schema is the restricted semantic statement and nothing else.
`TheoremStatementDigest` is a derived view of that admitted profiled body; it is
never a caller-authored field and cannot disagree with the theorem ID. Source
locator, bibliographic revision, PDF digest, imported-paper status, proof
artifact, and truth-discharge metadata live only in
`AnalysisTheoremSourceValidationBody`. Formation requires `ImportedPaperOnly`
to pair with `None` and `RetainedTheoremTruthAssumption`, and
`CheckedProofArtifact` to pair with `Some(exact checked proof artifact)` and
`EstablishedByCheckedProof`. Schema admission establishes no truth in either
case.

The validation body is governed by the narrow
`AnalysisAFKTheoremSourceValidationLanguageProfileId`, which imports exactly the
semantic transport profile. The theorem schema remains governed by
`AnalysisAFKTransportLanguageProfileId` and never imports the validation profile.
This profile edge is directional: changing a validation schema, source-kind
catalog, or validation law cannot rotate theorem semantics, while changing the
semantic transport profile intentionally rotates the child validation profile
and every validation subject under it. A support, validation-basis, or judgment
body that consumes a theorem-source-validation ID is also governed by the child
profile; its semantic basis, proposition, question, and goal remain governed by
the parent semantic transport profile.

Formation first authenticates the named theorem schema under the same exact
transport profile, resolves the source-kind declaration, requires a nonempty
bounded stable source ID and locator sequence, requires exactly 32 digest
bytes, and checks the discharge variant equalities above. The source record
names the bytes and locations that were selected; it does not by itself prove
that retrieved bytes match the digest or that a proof artifact establishes the
theorem. Those checks and their exact algorithms belong in the consuming
`AnalysisValidationBasis`. An unknown source kind is `Unsupported`; an
ill-typed, over-limit, wrong-length, incoherent, or mismatched-theorem body is
`Malformed` or `Refused` under the common outcome partition.

Consequently a source-only correction rotates the theorem-source-validation
ID and every support or validation basis that consumes it, but not the theorem
schema, theorem-truth question, goal, or proposition. A semantic statement,
template, component, local binding, or transform change rotates the theorem
schema; because the validation body names that schema ID, it also rotates every
downstream validation and support identity. No evaluator may recover theorem
meaning from the source record or source authority from the theorem body.

The schema body cannot name its own future ID. Each theorem-owned operator is
therefore declared under one zero-based local ordinal, and the transform stored
inside the schema uses `LocalTheoremOperatorRef(ordinal)`. Admission checks the
catalog and closed local transform template together. After the
schema ID is formed, an `AnalysisSemanticBasis` transform instruction qualifies
that reference as `(AnalysisTheoremSchemaId, LocalTheoremOperatorRef)`, maps it
to one already formed subject-dependent formula ID, and checks exact template
equality under the declared substitution. The global theorem schema never
contains that formula ID. The qualified theorem operator is never a child of
the formula or of an ordinary property question. No family/member ID, operator
display name, citation label, proof basis, or attempted self-reference
participates in theorem formation.

Schema admission checks a closed, typed statement. It does not establish the
theorem. A checked imported proof may provide established theorem authority. A
paper-only theorem is represented by placing the exact
`TheoremTruthGoal(T)` in the target's hypothesis context and marking that
premise `Assumed` in support together with the exact
`AnalysisTheoremSourceValidationId` whose body names T and selects
`ImportedPaperOnly`. `AssumedTheorem(T)` is shorthand for that ordinary
proposition use plus its validation binding, not a second proposition
constructor or theorem receipt.

### 2.2 Applicability question

```text
TheoremApplicabilityPayload = {
  theorem_schema_id,
  applicability_subject_kind:
      ConcreteProtocolInstance
    | AsymptoticFamilyInstance,
  required_structural_result_schemas_and_coordinates,
  required map schemas and exact map proposals,
  required side-condition schemas,
  exact local-binding substitution binding every theorem-local family,
    parameter, strategy, semantic-role, challenge, and resource coordinate,
  exact typed transform instantiation binding every local operator to
    basis-neutral operand/result formula IDs with checked template equality
}

TheoremApplicabilitySelection =
    ConcreteProtocolSelection {
      theorem_schema_id: AnalysisTheoremSchemaId,
      exact_subjects: CanonicalNonEmptySeq<TypedSemanticSubjectRef>,
      source_semantic_read_manifest_id: AnalysisSemanticReadManifestId,
      target_semantic_read_manifest_id: AnalysisSemanticReadManifestId,
      source_experiment_profile_id: AnalysisExperimentProfileId,
      target_experiment_profile_id: AnalysisExperimentProfileId
    }
  | AsymptoticFamilySelection {
      theorem_schema_id: AnalysisTheoremSchemaId,
      family_definition_id:
        AnalysisAsymptoticProtocolFamilyDefinitionId,
      source_family_read_manifest_schema_id:
        AnalysisFamilyReadManifestSchemaId,
      target_family_read_manifest_schema_id:
        AnalysisFamilyReadManifestSchemaId,
      source_family_experiment_profile_id: AnalysisExperimentProfileId,
      target_family_experiment_profile_id: AnalysisExperimentProfileId
    }

ExactApplicabilitySubjects(selection) =
  for ConcreteProtocolSelection, the authenticated canonical subject sequence
  stored by that variant; for AsymptoticFamilySelection, exactly
  [selection.theorem_schema_id,selection.family_definition_id]

ExactApplicabilityContext(selection) =
  for ConcreteProtocolSelection, the one SemanticExperimentContext containing
  its source/target manifests and experiments; for AsymptoticFamilySelection,
  the one FamilySemanticExperimentContext containing its family definition and
  source/target family manifest and experiment schemas

TheoremApplicabilityQuestion(selection,payload) = AnalysisQuestionBody {
  family: TheoremApplicability,
  exact_subjects: ExactApplicabilitySubjects(selection),
  context: ExactApplicabilityContext(selection),
  family_payload: payload : TheoremApplicabilityPayload,
  named_premise_requirements: []
}
```

The exact transport language profile imports the closed family-contract
catalog defined in
`cryptographic-properties.md#21-exact-property-family-contracts`. The
following is its exact theorem-specific two-row projection; no ambient family
registry is consulted:

```text
TransportAnalysisFamilyProfileContracts = CanonicalKeySortedSeq [
  {TheoremTruth,
   AnalysisFamilySemanticsContractFor(TheoremTruth)},
  {TheoremApplicability,
   AnalysisFamilySemanticsContractFor(TheoremApplicability)}
]
```

Each value is the exact resolved owner body, including its
`finite_cover_discharge_contract` and common failure-partition reference. The
transport profile neither expands nor redefines either row. Its authenticated
profile-import DAG must resolve those exact property-family declarations; a
missing, extra, redundant, or locally shadowed declaration refuses formation.
Any portable algorithm or evaluation contract selected by those laws carries
its own exact direct ordinary-module roots; that separate no-extra module
closure is authenticated for the subject and never becomes a profile import.
The two keys above are complete property-family declaration references, not
string labels accepted in place of the imported bodies.

Exactly one selection variant is present. Its theorem schema ID equals the
payload theorem ID and its concrete-versus-family tag equals
`applicability_subject_kind`. For a concrete selection, every manifest,
experiment, structural coordinate, and local-binding substitution resolves to
the listed concrete subjects. For a family selection, every dependent manifest,
experiment, role projection, quantitative dimension, and substitution resolves
to the one listed family definition. The family variant stores only portable
family IDs and symbolic catalog coordinates; abstract mathematical carriers are
derived through the family-language contract and never enter an identity body.
A mixed context, duplicate subject, unbound theorem-local coordinate, or
caller-selected subject sequence is malformed.

The hypothesis-free goal names only theorem schema, exact source/target
semantics, required map schemas, substitutions, and transform contract.
Concrete correspondence proposition IDs belong in support or the canonical
hypothesis context, never in the goal. This prevents a goal -> theorem instance
-> correspondence proposition -> goal identity cycle.

```text
TheoremApplicabilityGoal(selection,payload) = AnalysisGoalBody {
  question_id:
    AnalysisQuestionId(B,TheoremApplicabilityQuestion(selection,payload)),
  named_premise_bindings: {}
}

TheoremApplicabilityProposition(selection,payload,retained_premises) =
AnalysisPropositionBody {
  goal_id:
    AnalysisGoalId(B,TheoremApplicabilityGoal(selection,payload)),
  hypothesis_context_id:
    AnalysisHypothesisContextId(B,retained_premises)
}
```

The hypothesis context may include source/target model correspondence, Fresh
distribution, query-encoding, efficiency, and semantic map propositions. Each
is one ordinary hypothesis node; none is copied into the goal or treated as
established by schema admission. It MUST NOT include theorem truth: truth is
irrelevant to the structural question of whether a theorem statement applies.
The exact theorem-truth proposition enters only property transport.

Checked structural results, exact source-authority bindings, and side-condition
proposition bindings live in `SupportInstantiation`, not in the question or
hypothesis-free goal. The checker first authenticates the selected context and
its separately supplied source-support bindings. It then takes exactly one
variant-specific path:

- for `ConcreteProtocolSelection`, it checks that the Fresh and FS Protocols
  share the exact PIR Core and `FSConstructionView`, checks all required PIR fields
  through the concrete manifests, and checks the exact Relations Statement, claim,
  Witness, relation, and event maps; or
- for `AsymptoticFamilySelection`, it resolves the one family-language contract,
  checks both dependent family manifests and experiment schemas against that
  family, and checks only symbolic family-role, map, and denotation obligations.
  This path neither requires nor fabricates Foundation/PIR/Relations objects.

Both paths then compare strategy classes, quantifier prefixes, public-coin or
oracle models, failures, and resource dimensions to the theorem schema; check
every side condition and local-binding substitution; typecheck the exact
quantitative transform and complete loss ledger; and retain every assumed model,
distribution, or correspondence proposition. Mixing evidence or coordinates
between the two paths is `Refused`.

Successful checking produces an affirmative conditional applicability
judgment plus a fresh attenuated transport port. The port is bound to the exact
theorem schema, goal, source/target manifests, experiment profiles, maps,
substitution, transform, hypotheses, semantic/validation bases, policy
closure, named consumer, and typed purpose. Its ID or inert record cannot
replace the live port.

### 2.3 Qualified failure

- wrong subject, Core, Protocol, construction, map, strategy class, quantifier
  order, model, resource scope, hypothesis, occurrence, or loss parameter:
  `Refused`;
- unsupported theorem family, QROM, malicious-verifier, or missing operation:
  `Unsupported`;
- missing exact premise, source view, or fresh authority: `CannotAnswer`;
- noncanonical schema, duplicate map, invalid expression, or mismatched ID/body:
  `Malformed`;
- bounded evaluation exhaustion: `DeterministicLimitExceeded`; and
- checker/provider contradiction: `CheckerFailure`.

Inapplicability is not a negative target property.

## 3. Property transport

```text
PropertyTransport(
  exact affirmative source-property capability,
  exact affirmative theorem-applicability port,
  exact theorem-truth node treatment:
    established capability with its checked-proof validation
    or Assumed with its imported-source validation,
  exact target-proposition schema to reconstruct)
  -> AnalysisAttemptOutcome<TargetFamily>
```

The checker independently reconstructs the target proposition. It requires:

```text
target hypotheses = canonical union(
  source-judgment hypotheses,
  applicability-judgment hypotheses,
  exact theorem-truth goal,
  assumed correspondence and model hypotheses,
  undischarged side conditions,
  occurrence-local loss premises)

target support partition =
  every node in that complete target context occurs exactly once as
  established or Assumed; theorem truth uses the same ordinary partition

target quantitative result =
  exact evaluation of the theorem-owned typed transform
  under the checked parameter substitution and complete loss ledger
```

The source and applicability inputs carry their authenticated support records.
Transport inherits the exact established-or-`Assumed` treatment of every node
from those records; it does not require all side conditions to have established
capabilities. It may merge equal goals only through `CanonicalGoalDagUnion` and
the exact support-partition rule. The separate theorem-truth argument adds the
one theorem-truth node treatment and nothing else. That treatment includes the
exact theorem-source-validation ID. Its body must name the same theorem schema
as the node. An established treatment additionally requires the exact checked
theorem-truth capability and an `EstablishedByCheckedProof` validation body;
an assumed treatment requires `ImportedPaperOnly` and
`RetainedTheoremTruthAssumption`. A mismatched theorem ID, proof status, or
source-validation body is refused.

The caller cannot supply the target bound, delete inherited hypotheses, or
choose a different target model. Source loss is inherited exactly as directed
by the theorem program. Each Relations lossy occurrence is consumed exactly once if
and only if that program selects it.

An established theorem-truth node requires an exact affirmative capability for
`TheoremTruthPropositionId(T)`. A paper citation cannot supply it. The
paper-only path instead places that exact node in the support's `Assumed` map
and binds the exact `AnalysisTheoremSourceValidationId` for T.
The target proposition contains the same canonical context in either case;
support records whether the premise was discharged or retained and which
source/proof validation justified that treatment. Neither choice changes
applicability, the theorem schema, or the target's hypothesis-free goal.

For the initial AFK profile, the source is the exact affirmative uniform
all-`n` `2`-special-soundness judgment for one authenticated abstract family,
not the finite native Schnorr judgment. The target is adaptive classical-ROM
family knowledge soundness with the theorem-specific error and resource
expressions. Analysis defines no native rule that mints the source capability, so
its absence is `CannotAnswer`. A finite property judgment, well-formed
`CheckedFSConstruction`, concrete Fresh/FS run pair, or theorem-applicability
result is `Refused` when supplied in that source-property slot; a noncanonical
or structurally invalid carrier is `Malformed`.

## 4. Concrete occurrences do not prove properties

Finite runs are useful controls for:

- checking that source occurrence maps resolve;
- exercising PIR generated execution and deterministic replay;
- checking that Statement and commitment precede a challenge;
- observing exact failures and terminal dispositions; and
- falsifying identity and adequacy mistakes.

They are not semantic support for a universal property unless an explicit,
valid theorem rule says so. `RunRecord`, a Fresh/FS pair record,
`RelationRunView`, or an Evidence receipt cannot fill a universal source-
property slot.

## 5. Three non-interchangeable replay notions

### 5.1 PIR deterministic replay

`ReplayRun` checks that one supplied record agrees with the exact PIR transition
semantics under the supplied invocation and capabilities. It may accept a
future-informed record. `CheckedReplayMatch` therefore establishes no causal
generation, strategy membership, nonanticipation, or security property.

### 5.2 Cryptographic rewind, fork, or restoration

A theorem may define a counterfactual experiment that preserves selected
adversary coins/state while changing an oracle response or verifier challenge.
Its extractor capabilities, state relation, scheduling, and distribution law
belong to that theorem's Analysis experiment. They are not implemented by PIR
replay and are unavailable outside the theorem profile.

The exact classical FRI instrument under
[`evaluation/native-fri-ior/`](../../evaluation/native-fri-ior/README.md)
forms one restricted-restoration question as bounded candidate pressure. That
formed question is neither replay authority, an affirmative restoration
judgment, theorem applicability, nor property transport.

### 5.3 Analysis cold replay

Cold replay reauthenticates portable semantic bodies, reconstructs source
manifests, reacquires current capabilities, and reruns the exact checking plan.
It may reproduce an inert qualified record when every portable dependency is
available. It cannot recreate owner-local relation satisfaction, occurrence
authority, causal provenance, theorem proof authority, random-oracle behavior,
or a cryptographic fork.

No equality of bytes or records converts one replay notion into another.

## 6. Persistence and trust boundary

Only portable, policy-permitted bodies and inert records may be persisted.
Live capabilities are never serialized. Any result depending on an owner-local
Witness, satisfaction result, causal capability, or lossy-use consumer join is
same-process and has no exact cold replay.

Logical hypotheses remain separate from residual trust. The former are part of
the conditional proposition; the latter records dependence on checkers,
providers, encoders, runtime isolation, and imported proof systems. Replay
does not discharge either.

## 7. Deferred composition and coverage

Generic property composition, structural Core composition, artifact-wide
coverage, caches, disclosure profiles, persistence schemas, and extension
registries remain deferred. A future composition rule must name exact child and
target subjects, an independently checked structural relation, a theorem edge,
occurrence maps, hypothesis union, and typed loss. Structural composition alone
will still transport no property.

<!-- zkc-profile-source:analysis-theorem-validation-semantics:end -->
