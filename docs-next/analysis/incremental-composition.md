# Incremental Composition Analysis

> **Document kind:** Target semantic specification
> **Document state:** Active target extension; semantic source published
> **Provisional owner:** `analysis`
> **Authority:** None during transition. Current normative property semantics
> remain under [`docs/spec/soundness.md`](../../docs/spec/soundness.md).

<!-- zkc-profile-source:analysis-incremental-core-semantics:start -->

## 1. Purpose and authority boundary

This page gives recursive, folding, accumulation, IVC, NIVC, and PCD consumers
one place to state their static family and theorem obligations without adding a
second execution semantics.

The ownership split is exact:

```text
PIR
  one admitted Protocol and ProverPlan
  one generated run and direct accepted-continuation handoff

Relations
  exact step, instance, recurrence, binding-coverage, and same-step equations

Analysis
  one closed incremental-composition family
  theorem schemas and source validation
  adversary/model/depth quantifiers
  separate property conclusions and retained obligations

Realization
  byte transport, delivery, decoding, and fresh local re-admission
```

Analysis never owns an accumulator occurrence, proof stream, generated run,
continuation capability, transport session, or recursive verifier. It does not
convert a finite sequence of checked steps into an induction theorem. It
authenticates only static descriptions and evaluates exact conditional
propositions through the common Analysis calculus.

This page imports the generic question, goal, proposition, theorem-schema,
hypothesis, semantic-basis, support, validation, judgment, and authority
contracts from [Analysis Semantic Model](analysis-model.md). It imports the
one-step causal and recurrence boundaries from
[Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md),
[Protocol Correspondence](../relations/protocol-correspondence.md), and
[Recursive-Composition Grounding](../relations/recursive-composition-grounding.md).

## 2. Closed incremental-composition family

### 2.1 Static member language

A finite family is a theorem-level description of every statically admissible
step member. It is not a runtime registry and does not make its members one
larger Protocol.

```text
IncrementalCompositionMemberKey =
  CanonicalValue<member_key_type>

FamilyDescriptionAdviceContract = {
  protocol_advice_coordinate: ProtocolValueCoordinate,
  relation_advice_coordinate: RelationPublicRef,
  grounding_equation_id: GroundingEquationId,
  digest_algorithm: PortableAlgorithmRef,
  digest_evaluation: EvaluationContractId
}

IncrementalCompositionMemberDecl = {
  key: IncrementalCompositionMemberKey,
  protocol_id: ProtocolId,
  prover_plan_id: ProverPlanId,
  protocol_relation_binding_id: ProtocolRelationBindingId,
  recurrence_grounding_equation_id: GroundingEquationId,
  binding_coverage_schema_id: RecursionBindingCoverageSchemaId,
  predecessor_ingress_keys:
    CanonicalSeq<WitnessSurfaceKey>,
  carried_public_coordinates:
    CanonicalNonEmptySeq<RelationPublicRef>,
  family_description_advice:
    None | Some(FamilyDescriptionAdviceContract)
}

IncrementalCompositionSelectorTable =
  CanonicalNonEmptyMap<
    CanonicalValue<selector_type>,IncrementalCompositionMemberKey>

CompositionDecisionContract = {
  input_schema: AnalysisProfileLawRef<ClosedInputSchema>,
  output_schema: AnalysisProfileLawRef<ClosedOutputSchema>,
  operation_semantics: AnalysisProfileLawRef<TotalDecisionSemantics>,
  failure_partition: CommonAnalysisAttemptFailurePartitionRef
}

CarriedObligationSlotDecl = {
  role: AnalysisProfileDeclarationRef<
    "analysis.composition-obligation-role">,
  public_coordinate_type: ValueType,
  admissible_discharge_semantics:
    AnalysisProfileLawRef<ClosedObligationDischargeSemantics>
}

IncrementalCompositionFamilyBody = {
  member_key_type: ValueType,
  selector_type: ValueType,
  members:
    CanonicalNonEmptyMap<
      IncrementalCompositionMemberKey,
      IncrementalCompositionMemberDecl>,
  selector_table: IncrementalCompositionSelectorTable,
  update_verifier: CompositionDecisionContract,
  final_decider: CompositionDecisionContract,
  carried_obligation_slots:
    CanonicalSeq<CarriedObligationSlotDecl>
}

IncrementalCompositionFamilyId =
  AnalysisId<"analysis.incremental-composition-family",
             AnalysisIncrementalCompositionLanguageProfileId>(
    B,IncrementalCompositionFamilyBody)
```

Member keys and selector values are semantic values, not display names. Every
map is exact, finite, and canonical. Each selector value resolves to one
existing member; every member has at least one selector value. Several values
may select the same member, but a selector can never create or modify a
Protocol, Plan, relation, equation, schema, algorithm, or law.

Family admission authenticates every complete member preimage. The Plan names
the same Protocol. The protocol/relation binding, recurrence equation, and
coverage schema name the declared Protocol and compatible relation Interfaces.
Every predecessor ingress key resolves to a distinct `WitnessIngress` in that
Plan, and the recurrence equation accounts for each predecessor role. A base
member may have no predecessor; any non-base member has at least one. The
family therefore supports path IVC and finite-arity DAG/PCD joins without a
different execution primitive.

The authenticated subject graph is fixed before an invocation exists. A
runtime value may choose a selector-table entry, but no runtime instance,
witness, transcript, challenge, proof, accumulator, or previous output may
change the member map or any referenced semantic body. A body or dependency
that names the future family ID, reads a live occurrence while forming the
family, or embeds a derived family digest refuses formation.

### 2.2 Family-description advice without a fixpoint

Some recursive relations read a verifier key or digest describing their fixed
family. This does not require a self-referential semantic ID.

For a member with `family_description_advice`, Analysis derives:

```text
FamilyDescriptionPayload(F) =
  AnalysisDomainBodyV0<IncrementalCompositionFamilyBody>(F.body)

DerivedFamilyDescriptionDigest(F,contract) =
  Evaluate(
    contract.digest_algorithm,
    contract.digest_evaluation,
    FamilyDescriptionPayload(F))
```

The payload is the complete family body, not `IncrementalCompositionFamilyId`
and not a caller-authored projection. It contains the digest algorithm and
advice coordinates but contains no digest output, so evaluation is acyclic.
The member relation contains only an ordinary advice slot; it does not contain
the digest value or family ID. The exact grounding equation must bind the
protocol advice occurrence to the relation advice occurrence.

Equality between that occurrence and `DerivedFamilyDescriptionDigest` is an
Analysis proposition. Family formation derives the proposition and its source
coordinates; it does not establish the equality, collision resistance, or
that the digest is a binding commitment. The theorem application retains the
exact equality and algorithm assumptions unless separately discharged.

This construction intentionally differs from hashing the family ID. It avoids
a fixpoint while still making every body change alter the derived description
digest. Supplying an independent digest field, omitting body fields from the
payload, or treating byte equality as a binding theorem is malformed or
refused.

### 2.3 What admission establishes

Successful family admission establishes only:

- exact finite member and selector closure;
- static independence from runtime values;
- exact Protocol/Plan/Relations reference compatibility;
- exact predecessor arity and carried-coordinate coverage;
- an acyclic family-description-advice construction; and
- total typed update-verifier and final-decider contracts.

It does not establish relation satisfaction, fold preservation, accumulator
validity, continuation completeness, theorem truth, security, efficiency, or
that a decider accepts any occurrence. Those are separate propositions.

## 3. Uniformity and occurrence correspondence

The profile declares, rather than silently assumes, these property families:

```text
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

`ClosedIncrementalCompositionFamily` is stronger than admission only where its
theorem-specific payload says so. It may require semantic coherence among the
members, one state interpretation, and uniform algorithms. Admission itself
proves no such mathematical coherence.

For one invocation, `FamilyMemberSelectionCorrespondence` relates the exact
public selector occurrence to the one member selected by the static table.
It consumes owner-issued occurrence authority and does not authorize member
generation. `StepRecurrenceCorrespondence` and
`BindingCoverageCorrespondence` consume the exact Relations results for that
step. Equal values, equal IDs, a replayed result without live authority, or a
different occurrence do not satisfy those premises.

A finite checker may conjoin these results for a concrete chain or DAG and
verify exact adjacency. That result is process-local and nonidentified. It is
evidence for those occurrences only; it is not any family property above.

### 3.1 Exact Relations-result ingress

The two ordinary step premises above cannot enter Analysis as Booleans, copied
records, or ambient checker arguments. Relations exposes the exact owner-local
families `"causal-plan-step-recurrence-result"` and
`"recursion-binding-coverage-result"`; the CycleFold guardrail uses the
separate family `"cyclefold-same-step-grounding-result"`. Analysis gives those
families two closed source profiles rather than introducing a generic
Relations-result adapter.

```text
IncrementalCompositionStepRelationsSourceFamily =
  AnalysisProfileDeclarationRef<"analysis.source-family">(
    "incremental-composition-step-relations-results")

IncrementalCompositionCycleFoldSourceFamily =
  AnalysisProfileDeclarationRef<"analysis.source-family">(
    "incremental-composition-cyclefold-result")

IncrementalCompositionSourceIngressFailurePartitionRef =
  CommonAnalysisAttemptFailurePartitionRef<
    AnalysisIncrementalCompositionLanguageProfileId>

AnalysisCausalStepRecurrenceAdequacy,
AnalysisRecursionBindingCoverageAdequacy,
AnalysisCycleFoldSameStepAdequacy
  = pairwise-distinct AnalysisAdequacyEvaluatorId values in
    AnalysisIncrementalCompositionLanguageProfileId

IncrementalCompositionStepRelationsSourceProfileBody = AnalysisSourceProfile {
  family_tag: IncrementalCompositionStepRelationsSourceFamily,
  slot_schemas: CanonicalSeq [
    ConcreteOwnerReadSlotSchema(
      Relations,"causal-plan-step-recurrence-result",
      CausalPlanStepRecurrenceQuestionCoordinate,
      OccurrenceEvidence,
      CompleteOwnerBodyProjection(
        CausalPlanStepRecurrenceResultViewSchema),
      AnalysisCausalStepRecurrenceAdequacy,
      ExactCheckedResultAuthorityBinding<
        Relations,CheckedCausalPlanStepRecurrence>,
      FreshSourceCapability,
      IncrementalCompositionSourceIngressFailurePartitionRef),
    ConcreteOwnerReadSlotSchema(
      Relations,"recursion-binding-coverage-result",
      RecursionBindingCoverageQuestionCoordinate,
      OccurrenceEvidence,
      CompleteOwnerBodyProjection(
        RecursionBindingCoverageResultViewSchema),
      AnalysisRecursionBindingCoverageAdequacy,
      ExactCheckedResultAuthorityBinding<
        Relations,CheckedRecursionBindingCoverage>,
      FreshSourceCapability,
      IncrementalCompositionSourceIngressFailurePartitionRef)
  ],
  closed_field_read_set:
    DerivedClosedFieldReadSet(slot_schemas)
}

IncrementalCompositionCycleFoldSourceProfileBody = AnalysisSourceProfile {
  family_tag: IncrementalCompositionCycleFoldSourceFamily,
  slot_schemas: CanonicalSeq [
    ConcreteOwnerReadSlotSchema(
      Relations,"cyclefold-same-step-grounding-result",
      CycleFoldSameStepGroundingQuestionCoordinate,
      OccurrenceEvidence,
      CompleteOwnerBodyProjection(
        CycleFoldSameStepGroundingResultViewSchema),
      AnalysisCycleFoldSameStepAdequacy,
      ExactCheckedResultAuthorityBinding<
        Relations,CheckedCycleFoldSameStepGrounding>,
      FreshSourceCapability,
      IncrementalCompositionSourceIngressFailurePartitionRef)
  ],
  closed_field_read_set:
    DerivedClosedFieldReadSet(slot_schemas)
}
```

The failure partition is the common Analysis partition resolved through the
incremental-composition profile. Each adequacy evaluator admits exactly the
incremental-composition Analysis profile and the exact Relations profile as
supported semantic inputs. It authenticates the complete owner question
coordinate, requires overall affirmative polarity, checks that every Protocol,
Plan surface, relation binding, equation, schema, member, and role agrees with
the consuming family/question, and accepts only the complete owner result-view
schema. The three evaluator IDs, source-family declarations, body schemas, and
failure laws are exact profile-law-source entries. Reusing the cryptographic-
property or AFK evaluators by structural similarity is unsupported.

The two source-family declaration bodies permit only
`ConcreteOwnerSource`, fix respectively the exact two-slot and one-slot schema
shown above, name the corresponding evaluator signatures, and select this
failure partition. Their profile contracts repeat those exact restrictions.
An abstract family role, a mixed concrete/abstract profile, an extra owner
family, or a caller-authored field projection is malformed or unsupported.

The corresponding concrete manifests are derived, not authored:

```text
IncrementalCompositionStepResultManifest(
    recurrence_coordinate,coverage_coordinate) =
  AnalysisSemanticReadManifest {
    source_profile_id:
      AnalysisSourceProfileId(
        IncrementalCompositionStepRelationsSourceProfileBody),
    exact_subjects:
      CanonicalStaticSubjectClosure(
        recurrence_coordinate,coverage_coordinate),
    slots: the exact two concrete slots obtained by replacing the two
      coordinate schemas above with recurrence_coordinate and
      coverage_coordinate
  }

IncrementalCompositionCycleFoldResultManifest(cyclefold_coordinate) =
  AnalysisSemanticReadManifest {
    source_profile_id:
      AnalysisSourceProfileId(
        IncrementalCompositionCycleFoldSourceProfileBody),
    exact_subjects:
      CanonicalStaticSubjectClosure(cyclefold_coordinate),
    slots: the exact one concrete slot obtained by replacing the coordinate
      schema above with cyclefold_coordinate
  }
```

`CanonicalStaticSubjectClosure` is the canonical sorted-unique sequence of
every durable semantic subject reached from the complete owner coordinate; it
contains no local result or capability. A step manifest always has both slots.
CycleFold is separate so an ordinary step is not forced to fabricate a
companion check, and a CycleFold result cannot substitute for recurrence or
coverage.

At checking time, `AnalysisSourceSupport` binds each manifest slot to the
identical Relations-issued `OwnerLocalSourceAuthorityBinding` and separately
receives its matching fresh source capability. Because both step bindings and
the CycleFold binding have owner-local result coordinates,
`ExactAnalysisSourceSupportId` is undefined: checking returns a
`LocalAnalysisSourceSupportHandle`, and locality taints the resulting support
and occurrence judgment forward. It does not taint the family, theorem schema,
question, goal, proposition, or semantic basis backward. Missing one step
slot, using two results from different occurrences, changing a static
coordinate, supplying only an underlying grounding result, rebuilding an
envelope, or omitting the fresh bearer refuses. Thus the finite checked step
can establish exactly one occurrence premise without becoming portable
evidence for a family theorem.

## 4. Theorem schema and application

### 4.1 Independent quantified axes

An incremental-composition theorem schema is an ordinary
`AnalysisTheoremSchemaId` whose closed component contracts bind at least:

```text
IncrementalCompositionTheoremCoordinates = {
  family_id: IncrementalCompositionFamilyId,
  topology:
    Path
    | FiniteInDegreeDag(max_predecessors: PositiveNatural),
  execution_depth_domain:
    ExactFinitePrefix(Natural)
    | PolynomialInSecurityParameter
    | AllNaturalDepths,
  compliance_predicate_depth_domain:
    ConstantDepth
    | ExplicitBound(AnalysisQuantitativeFormulaId)
    | PolynomialDepth,
  experiment_model: exact model declaration,
  continuation_quantifier: exact strategy and predecessor-proof quantifiers,
  update_verifier_semantics: exact family contract coordinate,
  final_decider_semantics: exact family contract coordinate,
  recurrence_and_coverage_premises: exact property-family goals,
  theorem_local_assumptions: canonical hypothesis schema,
  conclusions: exact separate property-family schemas
}
```

Execution length and compliance-predicate circuit depth are different axes.
`AllNaturalDepths` does not imply that the compliance predicate has polynomial
depth, and `ConstantDepth` does not bound the number of execution steps. A
standard-model theorem restricted to constant-depth compliance predicates
cannot be relabeled as a polynomial-depth or random-oracle theorem. A
random-oracle heuristic, concrete-hash instantiation, setup assumption, or
extractor restriction remains an exact hypothesis.

The continuation quantifier is also semantic. Strict IVC completeness may
require that any eligible prover can continue from any valid predecessor
proof. A same-process Plan handoff, a proof whose decider was outsourced, or a
nontransferable proof may satisfy a different theorem but cannot fill that
slot by sharing bytes or output type.

Completeness, knowledge soundness, and efficiency are three independent goal
families. A theorem application forms a separate proposition and judgment for
each conclusion it actually provides. There is no result subtype relation and
no bundled `VerifiedRecursiveComposition` conclusion.

<!-- zkc-profile-source:analysis-incremental-core-semantics:end -->

<!-- zkc-profile-source:analysis-incremental-validation-semantics:start -->

### 4.2 Source and theorem truth

The theorem body and its source record remain separate:

```text
AnalysisTheoremSchemaId
  exact mathematical statement and transform

AnalysisTheoremSourceValidationId
  exact paper or proof artifact, digest, locators, status, and truth treatment
```

An imported paper validates correspondence to a written source; it does not
establish theorem truth. Unless an accepted proof authority discharges the
theorem-truth goal, every resulting judgment retains it as a hypothesis. A
source revision can rotate source validation without rotating an unchanged
semantic theorem; a changed depth, model, adversary, decider, premise, or
conclusion rotates the theorem schema.

The existing Analysis machinery is the only attachment mechanism:

```text
exact family + exact theorem schema + exact source validation
  -> AnalysisSemanticBasis
  -> AnalysisSupportInstantiation
  -> AnalysisValidationBasis
  -> one AnalysisJudgmentRecord per exact conclusion
```

There is no additional `TheoremAttachmentId`. Live recurrence records do not
enter any of these preimages. The semantic basis references the family and
theorem schema; support binds every established premise and retained
assumption; validation records the checker and exact source validation actually
used; the judgment preserves the exact conditional conclusion.

<!-- zkc-profile-source:analysis-incremental-validation-semantics:end -->

<!-- zkc-profile-source:analysis-incremental-continuation-semantics:start -->

## 5. Carried obligations and report qualification

### 5.1 Obligations are derived, not supplied

A composition-specific native rule may mark a theorem-premise node as carried
state only through this closed payload:

```text
CarriedObligationBinding = {
  hypothesis_goal_id: AnalysisGoalId,
  member_key: IncrementalCompositionMemberKey,
  slot_ordinal: ordinal in family.carried_obligation_slots,
  public_coordinate: exact member RelationPublicRef,
  discharge_operation:
    AnalysisProfileLawRef<ClosedObligationDischargeOperation>
}

IncrementalCompositionRulePayload = {
  family_id: IncrementalCompositionFamilyId,
  theorem_schema_id: AnalysisTheoremSchemaId,
  carried_obligation_bindings:
    CanonicalMap<AnalysisGoalId,CarriedObligationBinding>,
  conclusion_reconstruction_laws:
    CanonicalNonEmptyMap<property-family coordinate,
                         AnalysisProfileLawRef>
}
```

The rule formation law derives the exact eligible hypothesis-goal set from the
theorem schema and exact family. Every carried slot required by the selected
update/decider semantics appears exactly once, and no unrelated hypothesis may
be labeled carried. A caller cannot submit a smaller or larger set.

For a completed judgment, Analysis derives:

```text
OutstandingCompositionObligations(judgment) =
  every CarriedObligationBinding whose exact hypothesis treatment in
  judgment.support is not Established, in canonical goal-ID order
```

Each entry retains the goal, exact public coordinate, and only operation
authorized to discharge it. An affirmative discharge must bind that exact
goal, coordinate occurrence, operation, result, and fresh result capability.
Missing, duplicate, substituted, stale, or extra discharges refuse. A PIR
`Accept` terminal, a Relations recurrence result, or byte equality cannot
erase an Analysis hypothesis.

### 5.2 Three honest report states

Report qualification is a nonidentified consumer operation over an exact
judgment and live discharge capabilities:

```text
CompositionReportQualification =
    Conditional {
      inherited_hypotheses,
      outstanding_carried_obligations
    }
  | CarriedObligationsDischarged {
      remaining_noncarried_hypotheses
    }
  | HypothesisFree
```

`CarriedObligationsDischarged` means that all deferred accumulator or decider
obligations were checked. It does not mean that theorem truth, a model
idealization, collision resistance, setup, extraction, or another retained
hypothesis disappeared. `HypothesisFree` is available only when the exact
judgment hypothesis context is empty after all authorized discharges.

The operation has no semantic ID and cannot rewrite the underlying PIR,
Relations, or Analysis records. Evidence may record the resulting report
state, but Evidence does not upgrade it.

## 6. Portable continuation

Portable material is not a causal continuation capability. A receiving process
may decode an accumulator, witness, proof, or decider proof and admit a fresh
ordinary input occurrence. It may then establish `FinalDeciderCorrectness` or
another exact Analysis premise for that occurrence.

That path cannot recreate the source run, accepted continuation, consumed
one-use supply, target preparation, or `CheckedCausalPlanStepRecurrence`.
Third-party continuation is therefore a theorem property over the portable
format, verifier/decider, and strategy model. It is never inferred from PIR's
same-process handoff.

## 7. Profile ownership

The extension uses two narrow profiles:

```text
AnalysisIncrementalCompositionLanguageProfileId
  imports exactly:
    AnalysisKernelLanguageProfileId,
    PIRInteractionProfileId,
    PIRInterfacePlanProfileId,
    RelationsProfileId
  owns:
    the incremental-composition family body and compiler,
    exact Relations-result source-family, adequacy-evaluator, source-profile,
    and concrete-manifest contracts,
    family/property/native-rule declarations,
    theorem component contracts,
    carried-obligation grammar,
    report-qualification laws,
    composition-specific evaluator and failure schemas

AnalysisIncrementalCompositionSourceValidationLanguageProfileId
  imports exactly:
    AnalysisIncrementalCompositionLanguageProfileId
  owns:
    theorem-source-kind and source-validation declarations,
    the owner-local source support and validation-bearing theorem support,
    validation, policy, judgment,
    checked-result, authority, consumer, and purpose contracts
```

The composition profile directly opens Protocol and Plan bodies and Relations
equations, so transitive reachability does not remove those direct imports. It
does not import either Fiat--Shamir sibling merely because a member Protocol
may name one: the family treats the authenticated Protocol as a complete
member and does not interpret a construction-specific law. A theorem that
does interpret such a law must use a narrower importing profile.

The exact supported-kind sets, marked semantic source, declaration catalogs,
complete six-field bodies, and profile IDs are published and independently
reconstructed. This establishes persistent target language identity only; it
does not establish theorem truth, implementation conformance, or semantic
freeze.

Adding this family kind does not rotate the six published upstream PIR
profiles. It rotates only downstream profiles whose exact law source or import
closure changes: Relations for its coverage schema, these Analysis profiles,
and any Compiler or Realization profile that directly consumes them.

## 8. Research basis

The boundary was pressure-tested against primary constructions that expose
different failure modes rather than treated as one universal recursion API:

- [Revisiting the Nova Proof System on a Cycle of Curves](https://eprint.iacr.org/2023/969)
  motivates complete instance linkage and keeps digest coverage distinct from
  the assumption that gives a digest binding meaning;
- [ProtoStar](https://eprint.iacr.org/2023/620) and
  [ProtoGalaxy](https://eprint.iacr.org/2023/1106) separate cheap accumulation,
  final decision, and the stronger ability of another prover to continue;
- [Proof-Carrying Data from Accumulation Schemes](https://eprint.iacr.org/2020/499)
  motivates explicit compliance-depth, verifier, and extraction hypotheses;
  its PCD setting also prevents silently treating path IVC and finite-in-degree
  DAG composition as one topology; and
- [HyperNova](https://eprint.iacr.org/2023/573) motivates a setup-fixed
  non-uniform family and the same-step companion-relation guardrail.

These sources constrain the vocabulary and required distinctions. Citation or
source correspondence does not establish any imported theorem, specialization,
or implementation claim; Section 4.2 remains the only source-truth treatment.

## 9. Required refusals and nonclaims

The bounded evaluator must preserve same-boundary positive controls and refuse
at least:

- an unbound recursion-facing instance;
- a runtime-generated or runtime-dependent family member;
- a selector outside the closed table;
- an embedded own family ID or caller-supplied family digest;
- a family-description advice occurrence without exact grounding;
- a theorem request with a changed topology, model, either depth axis,
  adversary quantifier, recurrence discipline, verifier or decider, digest
  rule, assumption, or conclusion;
- a missing hash-binding assumption for a digest path;
- a finite live chain offered as theorem authority;
- a recurrence or coverage occurrence supplied without the exact two-slot
  manifest, owner-local result bindings, and matching fresh capabilities;
- a copied, partial, cross-occurrence, or reconstructed Relations result
  binding, or a CycleFold result offered in an ordinary step slot;
- a carried-obligations-discharged report with an outstanding carried
  obligation, or a hypothesis-free report with any retained hypothesis; and
- a transported value offered as same-process causal authority.

Nothing on this page establishes an IVC, NIVC, PCD, folding, accumulation, or
recursive-proof theorem; arbitrary-party continuation; relation satisfaction;
fold preservation; accumulator validity; theorem truth; standard-model, ROM,
or QROM security; concrete-hash security; knowledge extraction; zero
knowledge; polynomial depth; implementation support; or production readiness.

<!-- zkc-profile-source:analysis-incremental-continuation-semantics:end -->
