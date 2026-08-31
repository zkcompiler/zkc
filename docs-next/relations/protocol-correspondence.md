# Protocol correspondence for relations

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative target
> **Provisional owner:** `relations`
> **Authority:** This page specifies the selected `docs-next/` correspondence
> model. It is non-normative until consolidation and cutover; the current
> specifications under [`docs/`](../../docs/README.md) remain authoritative.

## 1. Scope and ownership

This page owns one closed family of questions over already admitted Relations
and PIR subjects. It keeps mapped structure, whole-surface coverage, external
presentation, concrete-value comparison, artifact interpretation, grounding,
and one-run facts separate. No result from one family silently answers another.

It consumes, without redefining:

- K1 identity, values, portable algorithms, exact dependency closure,
  qualified completion, and authority from
  [Executable Semantic Foundations](../foundation/executable-foundations.md);
- Protocol structure, execution, replay, the public-only `RelationRunView`,
  and the separate causal, purpose-bound confidential initial-Oracle view from
  [Interactive Core and Causal Execution](../pir/interactive-core.md);
- external Interface, source-ID-free `PlanWitnessSurface` meaning, and the
  purpose-bound confidential Plan-witness view from
  [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md); and
- relation Interfaces, instances, split Protocol/Plan bindings, value bridges,
  artifact observations, grounding equations, and commitment slots from
  [Relation Model](relation-model.md).

This page does not own relation satisfaction, Protocol execution, Plan
realization, property Analysis, OIR projection, or realization. A raw carrier
path, label, digest, record, trace, external container, caller-created tuple,
or secret-derived portable identifier is never a correspondence source.

For confidential initial-Oracle grounding this page imports, without
redefining, the PIR names `ConfidentialInitialOracleFamily`,
`ConfidentialInitialOracleCoordinate`,
`ConfidentialInitialOracleDisclosurePolicy`,
`ConfidentialInitialOracleDisclosurePolicyId`,
`ConfidentialInitialOracleView`,
`CheckedConfidentialInitialOracleViewAuthority`,
`ConfidentialInitialOracleViewCapability`, and
`IssueConfidentialInitialOracleView`, together with
`PIRSourceConsumerRoleId`, `PIRSourcePurposeRoleId`, and the exact
`CausallyGeneratedOnly` and `WholeCanonicalCarrier` laws. The public
`RelationRunView` remains a different carrier with a different issuance law.

For causal private Plan-witness grounding this page imports, without
redefining, `ConfidentialPlanWitnessFamily`, its canonical read manifest and
source requirement, the disclosure policy and ID, binding payload, capability
requirement, policy closure, `ConfidentialPlanWitnessView`,
`CheckedConfidentialPlanWitnessViewAuthority`,
`ConfidentialPlanWitnessViewCapability`, and
`IssueConfidentialPlanWitnessView`. The imported source is the exact tagged
`Generated | Finalized` Plan source. It is not the public `RelationRunView`, a
portable secret identity, or a Relations-issued authority.

For direct cross-run Plan-witness handoff this page also imports, without
redefining, the PIR-owned `IssueAcceptedPlanWitnessIngressSupply`,
`ReadyPlanWitnessIngressSupply`,
`ReadyPlanWitnessIngressSupplyCapability`, and
`CausalPlanWitnessHandoffCapability` minted only when that ready supply and
its identical live capability are consumed to form the fresh target
`WitnessIngress` occurrence. Relations may inspect those owner-retained
coordinates only in the joins below. It cannot form a supply, consume one,
copy a private value, or mint the handoff capability.

The Relations language selects the companion page's standalone
`RelationsProfileId`. It imports exactly
`{PIRInterfacePlanProfileId}` and therefore reaches the two K2 PIR profiles
only through that transitive edge. Its supported subject-kind namespace is
exactly `RelationsSemanticSubjectKindCatalogV0`, and its module-declaration
namespace is exactly the disjoint
`RelationsDeclarationContractKindCatalogV0`, both owned in
[Relation Model, Section 2](relation-model.md#2-reused-foundations-and-common-rules).
This page supplies the body grammar for the correspondence question and the
six source-authority subjects already named by that semantic catalog; it does
not append kinds. Analysis, OIR, realization, theorem, and evidence profiles
are absent. A consumer authenticates the exact no-extra four-profile closure;
it cannot supply a shadow PIR profile, flatten imports into module roots, add
a consumer-authored declaration catalog, or treat a declaration kind as a
semantic subject.

The Relations profile's `declaration_catalogs` field is exactly empty. The
14-kind declaration sequence belongs to the final Relations semantic-law
source rather than to that profile field. The bounded executable independently
enumerates the sequence for dispatch tests, but the currently unpublished
semantic-law bytes do not yet publish or authenticate that full dispatch.

The Relations issuer requires only `RelationsProfileId` in evaluator support;
the three imported profiles are authenticated preimages, not three additional
evaluator-support requirements. Conversely, the three-entry Interface/Plan
closure cannot issue a Relations view. An authenticated but evaluator-unknown
Relations root is `Unsupported`; a supported root omitting
`relations.transform` or any emitted Relations owner-authority subject kind is
`Refused`; malformed profile/closure structure is `Malformed`.

## 2. Directional dependency cut

```text
K1 --------------------> RelationInterface
 |                            |
 +--> Protocol --> ProverPlan |
          |              |    |
          |              v    |
          |      PlanWitnessSurface
          |              |    |
          |              +----+--> PlanWitnessBinding
          +-------------------+--> ProtocolRelationBinding

checked correspondence combines exact operands;
it creates no new semantic root
```

`ProtocolRelationBinding` names no external `ProtocolInterfaceId` or Plan.
`PlanWitnessBinding` names one source-ID-free surface and one relation
Interface, never a full Plan. `ProverPlan` contains no Relations-owned ID.
These directions are invariant.

When one operation needs Plan bindings for several relation Interfaces, it
uses:

```text
SelectedPlanWitnessBindings =
  ExactMap<RelationInterfaceId, PlanWitnessBindingId>
```

The key set is every and only selected Interface whose witness surface the
question reads. Each value names that key as its exact
`relation_interface_id`; every surface names the Protocol of the selected
`ProtocolRelationBinding`. A missing, extra, duplicate, wrong-Interface, or
wrong-Protocol entry is rejected before the proposition is evaluated. Missing,
extra, or duplicate keys are `Malformed`; an authenticated binding for the
wrong Interface or Protocol is `Refused`. The map is operation intake, not an
identified aggregate.

## 3. Closed correspondence-question algebra

### 3.1 Local references and policies

All local references below are dense ordinals in the named admitted owner:

```text
StatementEdgeRef       = ordinal in ProtocolRelationBinding.statement_edges
PhaseEdgeRef           = ordinal in ProtocolRelationBinding.phase_edges
OracleEdgeRef          = ordinal in ProtocolRelationBinding.oracle_edges
ClaimMeaningRef        = ordinal in ProtocolRelationBinding.claim_meanings
ReductionMeaningRef    = ordinal in ProtocolRelationBinding.reduction_meanings
CommitmentClauseRef    = ordinal in ProtocolRelationBinding.commitment_groundings
PlanWitnessEdgeRef     = ordinal in PlanWitnessBinding.witness_edges
StatementMemberRef     = ordinal in ProtocolInterface.statement_members
TransportEntryRef      = ordinal in ProtocolInterface.transport_entries
```

A reference always carries the complete owner ID when it leaves that owner.
Equal bodies or values do not merge references.

```text
OccurrenceMappingPolicy = {
  source_functional: Bool,
  target_injective: Bool
}

GroundingEquationOwner =
    StandaloneEquation(GroundingEquationId)
  | CommitmentEquation(ProtocolRelationBindingId, CommitmentClauseRef)

RequiredRunQualification =
    ExactReplayQualified
  | ExactCausallyGenerated

GroundingRunRequirements =
  ExactMap<GroundingRunSlotRef, RequiredRunQualification>

CommitmentRunRequirements =
  ExactMap<CommitmentClauseRef, GroundingRunRequirements>

StatementDomain =
    AllStatementBindings
  | ExactScopes(NonEmptyCanonicalSortedUniqueSeq<ScopeRef>)

ExternalCoveragePolicy = MappedOnly | WholeSelectedSurface

CorrespondenceHistoryBoundary =
    Initial
  | BeforeOccurrence(OccurrenceRef)
  | AfterOccurrence(OccurrenceRef)
  | Completion

DecodedExternalAssignment = {
  protocol_interface_id: ProtocolInterfaceId,
  values: TotalMap<
    ExternalSlotRef,
    CanonicalValue<semantic type of that slot's admitted codec>>
}
```

The two mapping booleans select propositions; they do not alter edge
admission. `source_functional` asks whether one selected source slice maps to
at most one selected target slice. `target_injective` asks whether two selected
source slices never share one target slice.

Whole coverage uses one fixed recursive law. For one exact root occurrence of
type `T`, `SelectorPartition(T,S)` holds exactly when either `S = {Whole}`, or
`Whole` is absent and the following constructor-specific rule holds:

1. for a record, every and only field ordinal occurs as the first step and the
   suffix selectors for each field recursively partition that field type;
2. for a variant, every and only case ordinal occurs as the first step and the
   suffix selectors for each case recursively partition that case payload;
   selecting a case covers that case discriminator as well as its payload;
3. for a positive-capacity bounded sequence, every and only element ordinal
   below the capacity occurs as the first step and the suffix selectors for
   each element recursively partition the element type; an element region
   includes its presence/absence position as well as its payload when present;
4. a zero-capacity sequence and every scalar type have only the `{Whole}`
   partition.

`ExactNonoverlappingCover(R)` groups the finite selected region set `R` by its
complete typed root occurrence and requires `SelectorPartition` for every
root. A root is a full owner-qualified relation role, K2 binding occurrence,
or Plan-surface occurrence, never merely a type or equal value. The recursive
rule rejects duplicate regions, ancestor/descendant overlap, omitted branches,
and a selector for another root. It is a decidable structural law over the
finite admitted schemas; there is no caller-defined coverage predicate.

For `ExternalStatement`, `WholeSelectedSurface` has one exact domain. Every
selected Interface member is treated as its complete external-slot value;
the selected Statement-edge targets must name every and only the distinct K2
Statement bindings named by those members, and their target selectors must
form `ExactNonoverlappingCover` of each such binding value. An edge targeting
an unselected member's binding, a selected member with no covering edge, or a
partial/overlapping target partition is a coverage disagreement. This policy
does not quantify over unselected Interface members; whole Interface coverage
is already the independent `StatementCoverage` admission law.

### 3.2 External and run selectors

```text
ExternalInstanceSelector =
    PublicValue(StatementEdgeRef, StatementMemberRef)
  | OraclePublicBinding(OracleEdgeRef, TransportEntryRef)
  | PhaseValue(PhaseEdgeRef, TransportEntryRef)

RelationBoundRunValueSelector =
    StatementValue(StatementEdgeRef)
  | PhaseValue(PhaseEdgeRef)
  | OraclePublicBinding(OracleEdgeRef)

UnboundRunValueSelector =
    PublicMessageOutput(OccurrenceRef, TypedValueSelector)
  | PublicOraclePublication(OracleRef, OccurrenceRef, TypedValueSelector)
  | PublicOracleQuery(OracleRef, OccurrenceRef, TypedValueSelector)
  | PublicOracleAnswer(OracleRef, OccurrenceRef, TypedValueSelector)
  | TerminalPublicOutput(TerminalRef, OccurrenceRef, output_ordinal,
                         TypedValueSelector)
  | PublicModuleObservation(OccurrenceRef, ModuleEffectRef,
                            output_ordinal, TypedValueSelector)

RunValueSelector =
    RelationBoundRunValueSelector
  | UnboundRunValueSelector

RunMetaSelector =
    ClaimState(ClaimMeaningRef, CorrespondenceHistoryBoundary)
  | ReductionState(ReductionMeaningRef, CorrespondenceHistoryBoundary)
  | CheckResult(CheckRef, OccurrenceRef)
  | TerminalVerdict(TerminalRef, OccurrenceRef)

PublicRunFactSelector = RunValueSelector | RunMetaSelector

RunPresenceExpectation =
    RequireAvailable
  | RequireInactive
  | RequireNotReached

RunFactCheck =
    RelationBoundValue(RelationBoundRunValueSelector)
  | OracleMaterialAgreement(OracleEdgeRef)
  | ExpectedValue(
      RunValueSelector,
      CanonicalValue<RunValueSelectorType(selector)>)
  | ExpectedCheckResult(
      CheckResult(CheckRef, OccurrenceRef),
      MetaBooleanFalse | MetaBooleanTrue)
  | ExpectedTerminalVerdict(
      TerminalVerdict(TerminalRef, OccurrenceRef),
      TerminalVerdict)
  | Presence(PublicRunFactSelector, RunPresenceExpectation)
```

Every selector derives exactly one PIR-owned `RelationRunCoordinate` and exact
type or closed meta type. `RunValueSelectorType` is that owner-derived K1
value type after applying its written `TypedValueSelector`; the caller cannot
assert it. `PublicMessageOutput` is restricted to a standard public Prover or
deterministic-Verifier message. Oracle and module-effect outputs use only their
dedicated constructors. Terminal verdict and each terminal public output are
separate coordinates. A selected Oracle query or answer must have Public
visibility. Thus no fact can be requested through both a generic occurrence
output and a role-specific alias; aliasing selectors make the question
malformed.

Before applying the written selector, `PublicOracleQuery` has base type
`o.index_type` and `PublicOracleAnswer` has base type
`OracleAnswerOutputType(o)`. Thus a logical-access answer selector ranges over
`o.element_type`, not the optional `OracleLookupResultType(o)` used by the
other publication modes.

`RelationBoundValue` obtains its expectation only from the exact relation
instance endpoint and admitted edge `ValueRelation`. Its
`OraclePublicBinding` selector forms only for a `PublicBoundOracleTarget`.
`OracleMaterialAgreement` forms only for a `LogicalOracleTarget` whose PIR
Oracle is `InitialOracle + LogicalAccess`; it selects no public run coordinate
and carries no material, digest, selector, bridge, or occurrence ID. Its exact
relation and PIR material types must both be the same whole
`OracleCarrierType(o)`, and the enclosing question must require
`ExactCausallyGenerated`. A structurally valid public-bound or prover-origin
target is `Unsupported`. A material-arm candidate authored with any other
qualification, including `ExactReplayQualified`, contradicts that fixed arm
grammar and is `Malformed`; an invalid reference or ill-formed target is also
`Malformed`.

`ExpectedValue` carries one canonical value of the selector-derived type and
uses exact Foundation equality; it has no relation-derived expectation. The
two expected-meta constructors are closed because PIR already owns their
finite result types. There is deliberately no generic expected-meta arm for
`RelationClaimHistory` or `RelationReductionHistory`: the current grammar can
ask only whether such a history coordinate is `Available`, `Inactive`, or
`NotReached`. Exact history predicates require a separately admitted grammar
and are unsupported here rather than being guessed from a binding.

`Presence` compares only the outer PIR observation alternative and never
claims equality of an available payload. `RequireInactive` forms only for a
coordinate that PIR classifies as occurrence-produced; other impossible
status/coordinate combinations are malformed. Across all arms, two checks
that derive the same PIR coordinate are malformed, even if their surface
selectors differ.

`PublicOraclePublication` forms only when PIR derives an actual canonical
publication value. A `LogicalAccess` fixation marker has no canonical value
payload and therefore has no `PublicOraclePublication` selector on this page.
The marker's activity remains part of PIR's confidential-view adequacy basis;
it is not a substitute value or an expected-meta arm.

Each `CorrespondenceHistoryBoundary` maps constructor-for-constructor to the
identically spelled PIR `RunBoundary`; it is durable question syntax, not a run
coordinate. `ExactReplayQualified` accepts only a `ReplayQualified` owner view,
and `ExactCausallyGenerated` accepts only a `CausallyGenerated` owner view.

### 3.3 Complete tagged sum

```text
CorrespondenceQuestion =
    MappedStatements {
      binding_id: ProtocolRelationBindingId,
      edges: NonEmptyCanonicalSortedUniqueSeq<StatementEdgeRef>,
      mapping: OccurrenceMappingPolicy
    }
  | WholeRelationPublic {
      binding_id: ProtocolRelationBindingId,
      interface_id: RelationInterfaceId,
      edges: CanonicalSortedUniqueSeq<StatementEdgeRef>
    }
  | WholeStatement {
      binding_id: ProtocolRelationBindingId,
      domain: StatementDomain,
      edges: CanonicalSortedUniqueSeq<StatementEdgeRef>
    }
  | MappedPlanWitness {
      plan_binding_id: PlanWitnessBindingId,
      edges: NonEmptyCanonicalSortedUniqueSeq<PlanWitnessEdgeRef>,
      mapping: OccurrenceMappingPolicy
    }
  | WholeRelationWitness {
      plan_binding_id: PlanWitnessBindingId,
      edges: CanonicalSortedUniqueSeq<PlanWitnessEdgeRef>
    }
  | WholePlanWitnessSurface {
      plan_binding_id: PlanWitnessBindingId,
      edges: CanonicalSortedUniqueSeq<PlanWitnessEdgeRef>
    }
  | ClaimReductionShape {
      binding_id: ProtocolRelationBindingId,
      claims: CanonicalSortedUniqueSeq<ClaimMeaningRef>,
      reductions: CanonicalSortedUniqueSeq<ReductionMeaningRef>
    }
  | ExternalStatement {
      protocol_interface_id: ProtocolInterfaceId,
      binding_id: ProtocolRelationBindingId,
      edges: NonEmptyCanonicalSortedUniqueSeq<StatementEdgeRef>,
      members: NonEmptyCanonicalSortedUniqueSeq<StatementMemberRef>,
      coverage: ExternalCoveragePolicy
    }
  | ExternalInstance {
      instance_id: RelationInstanceId,
      protocol_interface_id: ProtocolInterfaceId,
      binding_id: ProtocolRelationBindingId,
      selectors: NonEmptyCanonicalSortedUniqueSeq<ExternalInstanceSelector>
    }
  | ArtifactComparison {
      observation_id: RelationArtifactObservationId,
      relation_interface_id: RelationInterfaceId,
      artifact_question_id: ArtifactComparisonQuestionId
    }
  | EquationGrounding {
      equation_id: GroundingEquationId,
      run_requirements: GroundingRunRequirements
    }
  | CommitmentGroundingCheck {
      binding_id: ProtocolRelationBindingId,
      clauses: NonEmptyCanonicalSortedUniqueSeq<CommitmentClauseRef>,
      run_requirements: CommitmentRunRequirements
    }
  | RunGrounding {
      instance_id: RelationInstanceId,
      binding_id: ProtocolRelationBindingId,
      checks: NonEmptyCanonicalSortedUniqueSeq<RunFactCheck>,
      required_qualification: RequiredRunQualification
    }
  | PlanWitnessRunGrounding {
      plan_binding_id: PlanWitnessBindingId,
      instance_id: RelationInstanceId,
      edges: NonEmptyCanonicalSortedUniqueSeq<PlanWitnessEdgeRef>
    }

CorrespondenceQuestionBody(question) =
  RelationsBodyV0<CorrespondenceQuestion>(question)

CorrespondenceQuestionId =
  ProfiledSemanticId<"relations.correspondence-question">(
    B, RelationsProfileId,
    CorrespondenceQuestionBody(question))
```

Variant tags and record fields follow the written order. A question contains
only durable IDs, owner-scoped references, canonical policies, selectors, and
qualification requirements. It contains no source capability, run, decoded
assignment, secret occurrence, observation handle, checker, or result.

Question formation authenticates every owner ID, resolves every local
reference, derives every selector type, admits every expected canonical value,
rejects duplicate or aliased reads,
and enforces exact same-Protocol and same-Interface dependencies. It does not
evaluate mapping, coverage, equality, shape, equation, or run facts. Those
remain constructibly negative propositions.

Every `RunGrounding` contains at least one `RelationBoundValue` or
`OracleMaterialAgreement` check. This makes its `instance_id` and `binding_id`
semantically necessary rather than identity-bearing context for an unrelated
run assertion. Each such check's edge belongs to that binding and its relation
endpoint belongs to the exact instance Interface. Other checks may provide
explicit public expectations or presence facts in the same binding's
Protocol. A standalone run-monitoring question with no relation-bound public
value or initial logical-Oracle material agreement is outside this page's
algebra.

If any `OracleMaterialAgreement` occurs, `q.required_qualification` is exactly
`ExactCausallyGenerated`. Every such edge is a `LogicalOracleTarget`, names an
`InitialOracle + LogicalAccess` PIR Oracle, and has the exact whole-carrier type
agreement specified above. Repeating an edge in two material-agreement checks
is malformed. No public `RelationRunCoordinate` is derived for this arm.

Every `PlanWitnessRunGrounding` edge belongs to `q.plan_binding_id`, and its
relation endpoint belongs to the exact Interface of `q.instance_id`. The
sequence is nonempty, canonical sorted-unique, and contains no caller-selected
qualification. Causal Plan generation is a fixed law of this arm. In the
written tagged-sum order its exact body tag is `V(13,...)`:

```text
CorrespondenceQuestionBody[PlanWitnessRunGrounding](q) =
  V(13,R{
    0:ContentRef(q.plan_binding_id),
    1:ContentRef(q.instance_id),
    2:S[N(edge)... in canonical increasing order]
  })
```

It contains no Plan ID, private value, run, occurrence, source capability,
qualification selector, or consumer predicate.

For an admitted `RunGrounding` question `q`, Relations derives:

```text
RunGroundedBridgeUseScope(q) = {
  protocol_bindings: [q.binding_id],
  plan_witness_bindings: [],
  artifact_questions: []
}

RunSelectorBridgeUseCoordinate(q,StatementValue(e)) =
  ProtocolStatementEdge(q.binding_id,e.ordinal)
RunSelectorBridgeUseCoordinate(q,PhaseValue(e)) =
  ProtocolPhaseEdge(q.binding_id,e.ordinal)
RunSelectorBridgeUseCoordinate(q,OraclePublicBinding(e)) =
  ProtocolOracleEdge(q.binding_id,e.ordinal)

RunGroundedPotentialLossyCoordinates(q) =
  the canonical sorted-unique sequence of
  RunSelectorBridgeUseCoordinate(q,selector) for every
  RelationBoundValue(selector) in q.checks whose resolved exact admitted
  binding edge names an admitted lossy bridge

RunGroundedLossySelection(q,set) = {
  bridge_use_set: set,
  coordinates: RunGroundedPotentialLossyCoordinates(q)
}

PlanWitnessGroundedBridgeUseScope(q) = {
  protocol_bindings: [],
  plan_witness_bindings: [q.plan_binding_id],
  artifact_questions: []
}

PlanWitnessGroundedPotentialLossyCoordinates(q) =
  the canonical sorted-unique sequence of
  PlanWitnessEdge(q.plan_binding_id,edge.ordinal) for every edge in q.edges
  whose exact admitted binding edge names an admitted lossy bridge

PlanWitnessGroundedLossySelection(q,set) = {
  bridge_use_set: set,
  coordinates: PlanWitnessGroundedPotentialLossyCoordinates(q)
}
```

`RunGroundedPotentialLossyCoordinates(q)` is derived from the admitted
question, its exact admitted binding, and the admitted lane of every bridge
named by a selected edge. It does not inspect a `BridgeUseSet`, premise, or
consumer join, so it decides the conditional intake without circularity.
When that sequence is nonempty, `set.scope` must equal
`RunGroundedBridgeUseScope(q)` and every potential coordinate must resolve to
its exact checked lossy entry in that full set. The selection coordinates must
equal the potential sequence exactly. The selection is therefore a total
owner-derived function, not a caller-authored subset. The sequence may be
empty; the lossy set, premise, and join intake is required exactly when it is
nonempty.

The same total owner-derived law applies to
`PlanWitnessGroundedPotentialLossyCoordinates`: when nonempty, the exact
`BridgeUseSet` scope and selection above are required; when empty, no lossy
premise or source join is admitted. The relation-side live source for each
lossy coordinate is issued only by `IssuePrivateWitnessFieldSource` for the
exact assignment occurrence and exact question-bound consumer and purpose.

`ClaimReductionShape` requires at least one selected claim or reduction; a
selected reduction also derives reads for every claim meaning it cites.

A request for a well-formed family outside this tagged sum is `Unsupported`.
An unknown version-`0` tag or payload shape is `Malformed`; it is not an
extension point.

For `EquationGrounding`, the run-requirement key set is exactly the run slots
in `RequiredGroundingOperandSlots(equation)`. For
`CommitmentGroundingCheck`, its
outer key set is exactly `clauses` and each inner key set is exactly the run
slots in that clause's required operand set. Empty required run-slot sets
therefore have exactly empty maps; no ambient qualification or default is
permitted.

## 4. One derived read manifest

### 4.1 Closed read vocabulary

```text
ProtocolStaticReadBody =
    StatementBinding(BindingRef)
  | PhaseSource(PhaseTarget)
  | OracleDeclarationAndPublication(OracleTarget)
  | ClaimDeclaration(ClaimRef)
  | ReductionDeclaration(ReductionRef)
  | CheckDeclaration(CheckRef)
  | TerminalDeclaration(TerminalRef)
  | MessageDeclaration(OccurrenceRef)
  | ModuleObservationDeclaration(OccurrenceRef, ModuleEffectRef,
                                 output_ordinal)

ProtocolStaticRead = {
  protocol_id: ProtocolId,
  read: ProtocolStaticReadBody
}

ProtocolInterfaceReadBody =
    InvocationAssignment(InvocationInputRef)
  | StatementMember(StatementMemberRef)
  | TransportEntry(TransportEntryRef)
  | ExternalSlot(ExternalSlotRef)
  | InterfaceCodec(InterfaceCodecRef)

ProtocolInterfaceRead = {
  protocol_interface_id: ProtocolInterfaceId,
  read: ProtocolInterfaceReadBody
}

PlanSurfaceRead =
  WitnessSurfaceEntry(PlanWitnessSurfaceId, WitnessSurfaceKey)

RelationsRead =
    RelationRole(RelationPublicRef | RelationWitnessRef |
                 RelationOracleRef | RelationPhaseRef)
  | StatementEdge(ProtocolRelationBindingId, StatementEdgeRef)
  | PhaseEdge(ProtocolRelationBindingId, PhaseEdgeRef)
  | OracleEdge(ProtocolRelationBindingId, OracleEdgeRef)
  | ClaimMeaning(ProtocolRelationBindingId, ClaimMeaningRef)
  | ReductionMeaning(ProtocolRelationBindingId, ReductionMeaningRef)
  | PlanWitnessEdge(PlanWitnessBindingId, PlanWitnessEdgeRef)
  | RelationInstanceField(RelationInstanceId,
                          RelationPublicRef | RelationOracleRef |
                          RelationPhaseRef)
  | ValueBridgeLaw(ValueBridgeId)
  | BridgeUsePremise(BridgeUseCoordinate)
  | BridgeUseConsumerSourceJoin(BridgeUseCoordinate)
  | ArtifactClause(ArtifactComparisonQuestionId,
                   RelationArtifactObservationId, clause_ordinal)
  | GroundingSource(GroundingEquationOwner, source_ordinal)
  | GroundingStep(GroundingEquationOwner, step_ordinal)
  | GroundingEquality(GroundingEquationOwner, equality_ordinal)
  | CommitmentClause(ProtocolRelationBindingId, CommitmentClauseRef)
  | RelationTransform(RelationTransformId)

CorrespondenceRunRead =
    EquationRun {
      owner: GroundingEquationOwner,
      slot: GroundingRunSlotRef,
      protocol_id: ProtocolId,
      manifest: RelationRunReadManifest,
      required_qualification: RequiredRunQualification
    }
  | BindingRun {
      protocol_id: ProtocolId,
      manifest: RelationRunReadManifest,
      required_qualification: RequiredRunQualification
    }

ConfidentialInitialOracleCoordinateFor(binding,edge) = {
  protocol_id: binding.protocol_id,
  oracle: edge.protocol.oracle,
  publication: edge.protocol.publication_occurrence
}

ConfidentialInitialOraclePolicyFor(question,binding,edge) = {
  family: ConfidentialInitialOracleFamily,
  coordinate: ConfidentialInitialOracleCoordinateFor(binding,edge),
  extent: WholeCanonicalCarrier,
  qualification: CausallyGeneratedOnly,
  consumer_id: PIRSourceConsumerRoleId(
    PIRInteractionProfileId,
    ConfidentialInitialOracleFamily, CorrespondenceQuestionId(question)),
  purpose_id: PIRSourcePurposeRoleId(
    PIRInteractionProfileId,
    ConfidentialInitialOracleFamily, CorrespondenceQuestionId(question))
}

ConfidentialInitialOracleAgreementRead = {
  edge: OracleEdgeRef,
  relation_oracle: RelationOracleRef,
  pir_coordinate:
    exact ConfidentialInitialOracleCoordinateFor(binding,edge),
  material_type: OracleCarrierType(pir_coordinate.oracle),
  policy_qualification: CausallyGeneratedOnly,
  disclosure: WholeCanonicalCarrier
}

ConfidentialPlanWitnessSelection = {
  plan_binding_id: PlanWitnessBindingId,
  plan_witness_surface_id: PlanWitnessSurfaceId,
  keys: NonEmptyCanonicalSortedUniqueSeq<WitnessSurfaceKey>,
  source_requirement: ConfidentialPlanWitnessSourceRequirement
}

ConfidentialPlanWitnessSelectionFor(
  exact admitted PlanWitnessRunGrounding question,
  exact admitted PlanWitnessBinding binding) = {
  require PlanWitnessBindingId(binding) = question.plan_binding_id,
  plan_binding_id: question.plan_binding_id,
  plan_witness_surface_id: binding.plan_witness_surface_id,
  keys: canonical sorted-unique sequence of
    binding.witness_edges[edge].protocol.ref for every edge in question.edges,
  source_requirement:
    FinalizedRequired iff at least one selected key resolves in the exact
      admitted PlanWitnessSurface to
      ProducedWhenAcceptedTerminalReached,
    GeneratedSufficient otherwise
}

ConfidentialPlanWitnessPolicyFor(question,selection) = {
  family: ConfidentialPlanWitnessFamily,
  plan_witness_surface_id: selection.plan_witness_surface_id,
  manifest: selection.keys,
  qualification: CausallyGeneratedPlanOnly,
  source_requirement: selection.source_requirement,
  consumer_id: PIRSourceConsumerRoleId(
    PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessFamily, CorrespondenceQuestionId(question)),
  purpose_id: PIRSourcePurposeRoleId(
    PIRInterfacePlanProfileId,
    ConfidentialPlanWitnessFamily, CorrespondenceQuestionId(question))
}

CorrespondenceReadManifest = {
  protocol: CanonicalSortedUniqueSeq<ProtocolStaticRead>,
  protocol_interface: CanonicalSortedUniqueSeq<ProtocolInterfaceRead>,
  plan_surface: CanonicalSortedUniqueSeq<PlanSurfaceRead>,
  relations: CanonicalSortedUniqueSeq<RelationsRead>,
  run: FiniteSeq<CorrespondenceRunRead>,
  confidential_initial_oracle:
    CanonicalSortedUniqueSeq<ConfidentialInitialOracleAgreementRead>,
  confidential_plan_witness: Option<ConfidentialPlanWitnessSelection>
}
```

There is exactly one manifest:

```text
ManifestFor(q: admitted CorrespondenceQuestion) =
  the canonical least manifest derived by the rules below
```

Set-like read families use their written canonical order. Run reads preserve
question order and then grounding-slot or run-check order; no caller order
enters the result.

The caller never supplies or widens it. Derivation is exhaustive:

| Question | Exact derived reads |
|---|---|
| `MappedStatements` | selected Statement edges; their relation roles, K2 bindings, selectors, and bridges |
| `WholeRelationPublic` | the complete public-role sequence of the selected relation Interface plus selected Statement edges and endpoints |
| `WholeStatement` | every K2 Statement binding in `domain` plus selected Statement edges and sources |
| `MappedPlanWitness` | selected witness edges, relation witness roles, surface entries, selectors, and bridges |
| `WholeRelationWitness` | the complete witness-role sequence plus selected witness edges and surface entries |
| `WholePlanWitnessSurface` | every entry in the selected surface plus selected witness edges and relation sources |
| `ClaimReductionShape` | selected claim/reduction meanings and the exact K2 claim/reduction declarations, recipes, explicit `RelationTransform` reads, side inputs, challenges, and full publication requirements they cite |
| `ExternalStatement` | selected Interface members, Statement edges, invocation assignments reached by `SuppliesInvocation`, explicit external-slot and codec reads, and bindings |
| `ExternalInstance` | selected instance fields, Interface members/transports, binding edges, explicit external-slot and codec reads, and bridges |
| `ArtifactComparison` | the exact admitted artifact question, issued observation fields, selected relation Interface facts, selectors, and bridges named by each clause |
| `EquationGrounding` | the exact admitted equation; every source, step, equality, exactly `RequiredGroundingOperandSlots(equation)`, and one exact run read per run slot |
| `CommitmentGroundingCheck` | every typed construction input and publication slot plus the exact source, step, and equality in each selected closed grounding |
| `RunGrounding` | the binding edge for every `RelationBoundRunValueSelector` or `OracleMaterialAgreement` appearing in any check; the instance field selected only by each `RelationBoundValue` check; when the owner-derived `RunGroundedPotentialLossyCoordinates(q)` is nonempty, the premise and consumer-source join for every coordinate in that sequence; the unique public `RelationRunCoordinate` derived from each public check; and one exact confidential initial-Oracle agreement read for each material-agreement arm. Expected values are authenticated question literals, not owner reads. |
| `PlanWitnessRunGrounding` | every selected Plan-witness binding edge, its exact relation-witness endpoint and surface entry, both selectors and the admitted value relation; the exact selected instance; when `PlanWitnessGroundedPotentialLossyCoordinates(q)` is nonempty, every required premise and private-witness consumer-source join; and one confidential Plan-witness selection whose keys are the canonical sorted-unique surface keys of those edges and whose source requirement is derived from their occurrence classes |

The `confidential_initial_oracle` field is empty for every question except
`RunGrounding`; for that family its key set is exactly the distinct
`OracleMaterialAgreement` edge sequence derived from `q.checks`. An empty field
creates no confidential owner request or ambient authority.

The `confidential_plan_witness` field is `Some` exactly for
`PlanWitnessRunGrounding` and `None` for every other arm. Its nonempty key set
is derived, never caller-supplied. It selects `FinalizedRequired` exactly when
any selected surface entry is `ProducedWhenAcceptedTerminalReached`;
otherwise it selects `GeneratedSufficient`. The option cannot be present with
an empty key set.

Every phrase in the table is expanded to the closed read arms above before
canonical sorting. No arm silently carries an unlisted owner subtree. The
exact fixed `CorrespondenceReadClosure` then reaches a fixed point:

```text
InvocationAssignment(i) -> ExternalSlot(slot(i)), InterfaceCodec(codec(slot(i)))
StatementMember(m) -> ExternalSlot(slot(m)), InterfaceCodec(codec(slot(m))),
                      and InvocationAssignment(target(m)) when SuppliesInvocation
TransportEntry(t) -> ExternalSlot(slot(t)), InterfaceCodec(codec(slot(t)))
ExternalSlot(s) -> InterfaceCodec(codec(s)) and every exact inverse-use field
InterfaceCodec(c) -> every transitive structural child and exact General-law
                     semantic dependency named by c
ReductionMeaning(_,r) -> RelationTransform(transform(r))
```

The closure includes the exact semantic codec declaration and General-law
coordinate, never its admission certificate or live evidence capability. Those
remain authority inputs retained by the admitted Interface and its owner-issued
view capability. A transform read selects the complete identified
`RelationTransformBody`, including input/output Interfaces and the exact public
derivation ABI. Merely reading a `RelationTransformId` from one reduction
meaning is not a transform read.

Reading one edge includes, through explicit canonical manifest arms, its
complete typed endpoints and the exact admitted bridge plus affirmative
bridge-law result when the edge is not same-type.
For `RunGrounding` and `PlanWitnessRunGrounding`, each coordinate in its exact
owner-derived potential lossy sequence additionally reads the affirmative
occurrence-local source premise and affirmative consumer-source join bound to
that use coordinate. Other structural, coverage, Plan-shape, and artifact
questions do not acquire such a read merely because an edge names a lossy
bridge; the current target defines no live source-consumer join for them.
Concretely, coordinate `c` adds both `BridgeUsePremise(c)` and
`BridgeUseConsumerSourceJoin(c)` to the Relations submanifest.
The exact full `BridgeUseSet` and `LossyUseSelection` are separately
authenticated Section 9 operation operands; they are not manifest read arms.
Reading one Oracle edge additionally includes the relation access declaration,
PIR Oracle origin, publication mode, index/answer/carrier types, domain or
binding construction, and publication occurrence. A public-bound target reads
the `PublicBinding` construction and output coordinate; a logical target reads
`InitialOracle + LogicalAccess` and has no publication-value read. Reading a
reduction meaning includes the exact side-input, challenge, and
`(publication,next_challenge)` ordinal maps; it does not read a refinement
theorem or output-agreement proof.

For a material-agreement arm, the derived
`ConfidentialInitialOracleAgreementRead` contains only the static edge,
relation endpoint, imported PIR coordinate, exact common material type, and the
fixed causal whole-carrier policy. It contains neither carrier, assignment
occurrence, supply occurrence, capability, trace, digest, nor result. The
matching live sources are operation operands. This field is not part of the
public run submanifest and does not widen `RelationRunView`.

Its coordinate is formed field-for-field with the imported PIR grammar:
`protocol_id` is the exact binding Protocol, `oracle` is the logical target's
Oracle reference, and `publication` is that target's unique publication
occurrence. Its required policy is exactly
`ConfidentialInitialOraclePolicyFor(q,binding,edge)` above; no Relations alias,
label, or alternate policy family participates.

For a Plan-witness grounding arm, the confidential selection contains only
the static binding, source-ID-free surface, canonical key set, and derived
source requirement. It contains no Plan ID, private value, run, occurrence,
capability, or digest. Its required policy is exactly
`ConfidentialPlanWitnessPolicyFor(
q,ConfidentialPlanWitnessSelectionFor(q,binding))` above; the matching
live owner view remains a separate operation operand and never widens the
static `PlanSurfaceCorrespondenceView`.

### 4.2 Exact owner-issued view carriers

The four source owners issue separate attenuated carriers. They do not return a
generic map whose value type or provenance is selected by Relations:

```text
ProtocolStaticCorrespondenceEntry = {
  read: ProtocolStaticRead,
  exact_pir_field_manifest: PIRStaticViewReadManifest,
  exact_pir_projection: PIRStaticViewProjection
}

ProtocolStaticCorrespondenceView = {
  protocol_id: ProtocolId,
  requested_reads: CanonicalSortedUniqueSeq<ProtocolStaticRead>,
  entries:
    CanonicalSeq<ProtocolStaticCorrespondenceEntry in requested-read order>
}

ProtocolInterfaceCorrespondenceEntry = {
  read: ProtocolInterfaceRead,
  exact_interface_field_manifest: ProtocolInterfaceOwnerReadManifest,
  exact_interface_projection: ProtocolInterfaceOwnerViewProjection
}

ProtocolInterfaceCorrespondenceView = {
  protocol_interface_id: ProtocolInterfaceId,
  requested_reads: CanonicalSortedUniqueSeq<ProtocolInterfaceRead>,
  entries:
    CanonicalSeq<ProtocolInterfaceCorrespondenceEntry in requested-read order>
}

PlanSurfaceCorrespondenceView = {
  plan_witness_surface_id: PlanWitnessSurfaceId,
  requested_reads: CanonicalSortedUniqueSeq<PlanSurfaceRead>,
  entries: CanonicalSeq<exact PlanWitnessSurfaceEntry in requested-read order>
}

RelationsCorrespondenceEntry<r: RelationsRead> = {
  read: r,
  value: ExactRelationsReadValue(r)
}

RelationsCorrespondenceView = {
  requested_reads: CanonicalSortedUniqueSeq<RelationsRead>,
  entries: CanonicalSeq<RelationsCorrespondenceEntry in requested-read order>
}
```

`ExactRelationsReadValue` is a fixed total owner resolver over the closed
`RelationsRead` sum and `RelationsBodyV0`. It selects the complete typed local
subtree named by the read and the exact admitted body/capability on which that
subtree depends. In particular `RelationTransform(id)` resolves the complete
authenticated `RelationTransformBody(id)` rather than the occurrence of `id`
inside a reduction meaning. It has no caller callback, default arm, textual
path, or proposition-dependent override.

`PIRFieldExpansion(read)` and `InterfaceFieldExpansion(read)` are fixed total
owner translations from each corresponding read constructor to the exact
field manifest required by the K2 and Interface closure laws. Their unions must
equal the realized projection manifests; two high-level reads may share a
field, but the field occurs once in the canonical union and its inverse-use
ledger records both reads. A field with no requesting read or a read with no
complete field expansion is malformed.

The owner operations are:

```text
IssueProtocolStaticCorrespondenceView(
  exact AdmittedProtocol,
  exact protocol submanifest,
  exact PIR static-view bindings and matching fresh capabilities)
    -> CorrespondenceOwnerViewIssueOutcome<ProtocolStaticCorrespondenceView>

IssueProtocolInterfaceCorrespondenceView(
  exact AdmittedProtocolInterface,
  exact Interface submanifest,
  exact Interface admission/source binding and matching fresh capability,
  exact consumer: same-regime SemanticContentId<Kconsumer>,
  exact purpose: same-regime SemanticContentId<Kpurpose>)
    -> CorrespondenceOwnerViewIssueOutcome<ProtocolInterfaceCorrespondenceView>

IssuePlanSurfaceCorrespondenceView(
  exact PlanWitnessSurface,
  exact checked extraction binding and matching fresh extraction capability,
  exact Plan-surface submanifest)
    -> CorrespondenceOwnerViewIssueOutcome<PlanSurfaceCorrespondenceView>

IssueRelationsCorrespondenceView(
  every and only exact admitted Relations operand named by the submanifest,
  every exact admitted/check-result source binding and matching capability,
  exact Relations submanifest,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
    -> CorrespondenceOwnerViewIssueOutcome<RelationsCorrespondenceView>

CorrespondenceOwnerViewIssueOutcome<V> =
    Affirmative({
      view: V,
      exact_owner_view_authority_binding: OwnerLocalSourceAuthorityBinding,
      fresh_owner_view_capability
    })
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed
  | DeterministicLimitExceeded | CheckerFailure
```

Every owner independently rederives its required closure and source values.
Requested reads, realized reads, returned entries, and the appropriate
canonical submanifest must agree exactly. An absent exact named subject,
module, declaration, algorithm, or profile preimage after its coordinate forms
is `MissingDependency`; an authenticated supported source whose required live
read or capability is unavailable is `CannotAnswer`; an unsupported owner
constructor is `Unsupported`; a wrong namespace, kind, regime, or exact ABI is
`KindMismatch`; a stale capability or failed authenticated owner/purpose
predicate is `Refused`; and an extra, duplicate, aliased, reordered,
unconsumed, or ill-formed entry is `Malformed`. None is Negative, and no
partial carrier or binding is returned.

For `IssueRelationsCorrespondenceView`, the identity set of supplied Relations
operands equals the identity set requested by the Relations submanifest. A
requested transform whose exact ID forms but whose named preimage is absent is
`MissingDependency`; an admitted transform whose required live owner handle is
unavailable is `CannotAnswer`; an unrequested extra transform is `Malformed`
even when every returned entry happens to ignore it. The live capability
retains exactly that equal source set, never a larger ambient owner
environment. Its binding satisfies the Section 4.3 predicate for family
`"relations-correspondence-view"`, source
`CorrespondenceViewSource(view.requested_reads)`, and manifest
`CorrespondenceViewReads(view.requested_reads)`; the local coordinate is the
identical issued view object.

The transform branch applies a fixed precedence before source lookup: a
formed coordinate with the wrong namespace, kind, or regime is `KindMismatch`;
only an exact same-kind transform coordinate can reach the lookup and become
`MissingDependency`; and any unrequested supplied transform is `Malformed`.
The bounded executable has no independently admitted live transform handle
that can become unavailable after its durable preimage is present, so it does
not currently exercise this operation's `CannotAnswer` branch. Adding a test-
only availability flag would not be evidence for that semantic distinction.

Each static owner binding specializes K1
`OwnerLocalSourceAuthorityBinding`. The PIR Interface binding has owner `"pir"`
and family `"interface-correspondence-view"`; the Relations binding is formed
only by the closed Relations specialization below.

### 4.3 Exact Relations source-authority subjects

Foundation owns the inert `PortableSourceAuthorityBinding` and
`OwnerLocalSourceAuthorityBinding` envelopes but deliberately does not assign
meaning to their owner fields. Relations selects exactly eight capability
families for the source operations in this target:

```text
RelationsSourceCapabilityFamilyV0 =
  MetaSymbol in {
    "relation-definition-view",
    "relations-correspondence-view",
    "relation-instance-field",
    "private-witness-field",
    "artifact-observation-field",
    "causal-plan-step-recurrence-result",
    "recursion-binding-coverage-result",
    "cyclefold-same-step-grounding-result"
  }

RelationsSourceFamilySymbol(f) = f
```

There is no unknown-family or custom-family arm. A family outside this sum is
`Unsupported`; accepting another family requires a Relations profile/law
change rather than an open-default parse.

The consumer and purpose roles are open only in the coordinate they wrap. A
`RelationsDownstreamCoordinate` is one exact same-regime
`SemanticContentId<K>` for some exact kind `K`; that kind is retained by the
typed ID but is not interpreted or re-encoded by Relations:

```text
RelationsSourceConsumer = {
  family: RelationsSourceCapabilityFamilyV0,
  downstream_coordinate: RelationsDownstreamCoordinate
}

RelationsSourcePurpose = {
  family: RelationsSourceCapabilityFamilyV0,
  downstream_coordinate: RelationsDownstreamCoordinate
}

RelationsSourceConsumerBody =
  RelationsBodyV0(RelationsSourceConsumer)
RelationsSourcePurposeBody =
  RelationsBodyV0(RelationsSourcePurpose)

RelationsSourceConsumerId =
  RelationsId<"relations.source-consumer">(
    B, RelationsSourceConsumerBody)
RelationsSourcePurposeId =
  RelationsId<"relations.source-purpose">(
    B, RelationsSourcePurposeBody)
```

`RB(RelationsDownstreamCoordinate)` is exactly `O(ContentRefV0(id))`; no label, fixture name,
display string, or untyped bytes can stand in for the downstream coordinate.
The role bodies contain the family tag and that one content reference, in
written field order. Swapping roles, coordinates, or families changes the
role ID.

The source and manifest fields are closed indexed sums, not arbitrary
`MetaValueV0` payloads:

```text
RelationInstanceSourceEndpoint =
    RelationPublicValue(RelationPublicRef, TypedValueSelector)
  | RelationPhaseValue(RelationPhaseRef, TypedValueSelector)
  | RelationOraclePublicBindingValue(RelationOracleRef, TypedValueSelector)

RelationWitnessSourceEndpoint =
  RelationWitnessValue(RelationWitnessRef, TypedValueSelector)

ArtifactObservationSourceEndpoint =
  ArtifactValue(ArtifactFactSelector)

RelationsSourceDescriptorV0 =
    DefinitionViewSource {
      coordinate: RelationDefinitionViewCoordinate
    }
  | CorrespondenceViewSource {
      requested_reads: CanonicalSortedUniqueSeq<RelationsRead>
    }
  | InstanceSource {
      instance_id: RelationInstanceId
    }
  | PrivateWitnessSource {
      instance_id: RelationInstanceId
    }
  | ArtifactObservationSource {
      observation_id: RelationArtifactObservationId
    }
  | CausalPlanStepRecurrenceResultSource {
      question_coordinate: CausalPlanStepRecurrenceQuestionCoordinate
    }
  | RecursionBindingCoverageResultSource {
      question_coordinate: RecursionBindingCoverageQuestionCoordinate
    }
  | CycleFoldSameStepGroundingResultSource {
      question_coordinate: CycleFoldSameStepGroundingQuestionCoordinate
    }

RelationsSourceManifestV0 =
    DefinitionViewFields(RelationDefinitionReadManifest)
  | CorrespondenceViewReads(
      CanonicalSortedUniqueSeq<RelationsRead>)
  | InstanceField(RelationInstanceSourceEndpoint)
  | PrivateWitnessField(RelationWitnessSourceEndpoint)
  | ArtifactObservationField(ArtifactObservationSourceEndpoint)
  | CompleteCausalPlanStepRecurrenceResult
  | CompleteRecursionBindingCoverageResult
  | CompleteCycleFoldSameStepGroundingResult
```

The payload and remaining owner subjects are:

```text
RelationsSourceBindingPayload = {
  owner_domain: "relations",
  family: RelationsSourceCapabilityFamilyV0,
  source: RelationsSourceDescriptorV0,
  manifest: RelationsSourceManifestV0,
  consumer_id: RelationsSourceConsumerId,
  purpose_id: RelationsSourcePurposeId
}

RelationsSourceNoPolicy = {
  family: RelationsSourceCapabilityFamilyV0,
  payload_id: RelationsSourceBindingPayloadId,
  disposition: "owner-defines-no-additional-operation-policy"
}

RelationsSourceCapabilityRequirement = {
  family: RelationsSourceCapabilityFamilyV0,
  payload_id: RelationsSourceBindingPayloadId,
  consumer_id: RelationsSourceConsumerId,
  purpose_id: RelationsSourcePurposeId,
  bearer_law: "fresh-identical-bearer-capability"
}

RelationsSourcePolicyClosure = {
  family: RelationsSourceCapabilityFamilyV0,
  payload_id: RelationsSourceBindingPayloadId,
  no_policy_id: RelationsSourceNoPolicyId,
  requirement_id: RelationsSourceCapabilityRequirementId
}

RelationsSourceBindingPayloadBody =
  RelationsBodyV0(RelationsSourceBindingPayload)
RelationsSourceNoPolicyBody =
  RelationsBodyV0(RelationsSourceNoPolicy)
RelationsSourceCapabilityRequirementBody =
  RelationsBodyV0(RelationsSourceCapabilityRequirement)
RelationsSourcePolicyClosureBody =
  RelationsBodyV0(RelationsSourcePolicyClosure)

RelationsSourceBindingPayloadId =
  RelationsId<"relations.source-binding-payload">(
    B, RelationsSourceBindingPayloadBody)
RelationsSourceNoPolicyId =
  RelationsId<"relations.source-no-policy">(
    B, RelationsSourceNoPolicyBody)
RelationsSourceCapabilityRequirementId =
  RelationsId<"relations.source-capability-requirement">(
    B, RelationsSourceCapabilityRequirementBody)
RelationsSourcePolicyClosureId =
  RelationsId<"relations.source-policy-closure">(
    B, RelationsSourcePolicyClosureBody)
```

The fixed strings above are exact semantic symbols. They are not prose slots.
All records and variants use the written field and alternative order under
`RelationsBodyV0`; each of the six subjects therefore has one exact body
compiler without introducing another ID constructor.

Formation requires all of the following:

1. the payload owner is exactly `"relations"`, and every subject has the exact
   `RelationsProfileId` and one common semantic regime;
2. the consumer and purpose IDs authenticate their complete bodies, have the
   payload family, and wrap the exact supplied downstream coordinates in their
   respective roles;
3. the family selects exactly the matching source/manifest pair in this table:

   | family | source descriptor | manifest | envelope coordinate |
   |---|---|---|---|
   | `"relation-definition-view"` | the admitted definition and exact profile coordinate | the exact nonempty canonical definition-field manifest | the exact issued view object, owner-local |
   | `"relations-correspondence-view"` | the exact canonical Relations read sequence | the identical exact read sequence | the exact issued view object, owner-local |
   | `"relation-instance-field"` | one admitted `RelationInstanceId` | one public, phase, or Oracle-public-binding endpoint belonging to that instance's Interface | `RelationInstanceId`, portable |
   | `"private-witness-field"` | the exact `instance_id` retained by one fresh `PrivateWitnessAssignment` | one witness endpoint belonging to that instance's Interface | the exact assignment occurrence, owner-local |
   | `"artifact-observation-field"` | one admitted `RelationArtifactObservationId` | one artifact selector belonging to that observation's admitted profile | `RelationArtifactObservationId`, portable |
   | `"causal-plan-step-recurrence-result"` | one exact `CausalPlanStepRecurrenceQuestionCoordinate` | `CompleteCausalPlanStepRecurrenceResult` | the exact affirmative `CheckedCausalPlanStepRecurrence`, owner-local |
   | `"recursion-binding-coverage-result"` | one exact `RecursionBindingCoverageQuestionCoordinate` | `CompleteRecursionBindingCoverageResult` | the exact affirmative `CheckedRecursionBindingCoverage`, owner-local |
   | `"cyclefold-same-step-grounding-result"` | one exact `CycleFoldSameStepGroundingQuestionCoordinate` | `CompleteCycleFoldSameStepGroundingResult` | the exact affirmative `CheckedCycleFoldSameStepGrounding`, owner-local |

4. for a field family, every selector forms against its admitted owner and
   derives its type; for a checked-result family, the static question
   coordinate reconstructs exactly from the identical affirmative local result
   and that result's owner capability; equal values, another field, another
   instance or observation, another assignment or result occurrence, a partial
   result projection, or another process generation do not match;
5. the no-policy subject contains exactly the payload ID and fixed disposition;
   the requirement contains exactly the same payload, consumer, purpose, and
   fixed bearer law; and the closure contains exactly that payload, no-policy,
   and requirement triple, with no omitted or extra policy input; and
6. strict decode consumes the complete body and re-encoding reproduces it.

The three field-source issuance operations make the role intake explicit:

```text
IssueRelationInstanceFieldSource(
  exact admitted RelationInstance,
  exact RelationInstanceSourceEndpoint belonging to that instance,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> RelationsFieldSourceIssueOutcome<PortableSourceAuthorityBinding>

IssuePrivateWitnessFieldSource(
  exact fresh PrivateWitnessAssignment and secret-value capability,
  exact RelationWitnessSourceEndpoint belonging to its instance,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> RelationsFieldSourceIssueOutcome<OwnerLocalSourceAuthorityBinding>

IssueArtifactObservationFieldSource(
  exact admitted RelationArtifactObservation,
  exact matching fresh interpretation-or-replay authority,
  exact ArtifactObservationSourceEndpoint belonging to its profile,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> RelationsFieldSourceIssueOutcome<PortableSourceAuthorityBinding>

RelationsFieldSourceIssueOutcome<B> =
    Affirmative({binding: B, fresh_source_capability})
  | Unsupported | MissingDependency | CannotAnswer | KindMismatch
  | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

Each operation constructs the consumer and purpose role IDs from exactly its
two intake coordinates and copies those IDs into the payload and requirement.
No ambient default, diagnostic label, or caller-authored role ID is accepted.
There is no semantic Negative: a field source is issued exactly or returns one
qualified noncompletion.

For either envelope, `owner_domain = "relations"`, `capability_family` is
`RelationsSourceFamilySymbol(family)`, `owner_binding_payload` is the exact
payload ID, `operation_policy` is
`OwnerDefinesNoPolicy(no_policy_id)`, `owner_policy_closure` is the exact
closure ID, and `capability_requirement` is
`OwnerCapabilityRequirement("relations", family_symbol, requirement_id)`.
Foundation validates this carrier agreement; Relations authenticates the six
profiled bodies and the table-specific source law.

`RelationsSourceAuthorityBindingMatches(f,source,manifest,consumer,purpose,b)`
is exactly the conjunction of those formation equations, the matching table
row, and equality of every written envelope field. It is a predicate over the
one Foundation envelope `b`, not a seventh binding type, content ID, or receipt.
`RelationsLiveSourceAuthorityMatches(f,source,manifest,consumer,purpose,b,c)`
holds exactly when the binding predicate holds, `c` is the identical live
bearer atomically issued by Relations for that exact `b`, and `c` retains the
same family, source, manifest, original downstream coordinates, admitted owner
handles, issuance/assignment occurrence, process generation, evaluator,
lifetime, and revocation state. A document that merely says “exact source
authority” without selecting the binding predicate's six arguments, and the
live predicate's seventh bearer argument, does not satisfy the corresponding
predicate.

The definition and correspondence views and the private-witness field use an
`OwnerLocalSourceAuthorityBinding`; their local coordinate is respectively
the exact issued view or exact `PrivateWitnessAssignment` occurrence. The
relation-instance and artifact-observation fields use a
`PortableSourceAuthorityBinding` whose portable coordinate is respectively
the exact `RelationInstanceId` or `RelationArtifactObservationId`. Portability
does not move authority: the inert envelope can be stored, but cold use must
reauthenticate the subject and recreate the exact fresh owner capability.

Every live capability retains the identical envelope object, original
downstream consumer and purpose coordinates, admitted owner handles, complete
manifest, selected field and derived type where applicable, issuance or
assignment occurrence, process generation, evaluator, lifetime, and
revocation state. Passing that identical live bearer is the only delegation.
A relation-instance source must read the exact total-map entry. A private-
witness source must read the exact secret capability in the named assignment.
An artifact source must read an `Observed` field under fresh interpretation or
affirmative replay authority; `Unread`, a missing `At` occurrence, or an
unavailable otherwise matching read is `CannotAnswer` and issues no live source
capability. `Whole` over `Observed([])` remains the exact empty sequence rather
than absence of a source.
A reconstructed envelope, copied capability, equal value, stale generation,
cross-family role, or different consumer or purpose is `Refused`; an absent or
expired otherwise matching live source is `CannotAnswer`. The private-witness
payload contains no secret value or occurrence reference, and neither local
binding has a canonical body.

These are the complete source families selected by this document. The last
three are narrow exports for the exact recursive-composition checks defined by
this page and by
[Recursive-Composition Grounding](recursive-composition-grounding.md); they do
not define a generic checked-result source family. Each uses the complete-result
manifest arm only, derives its portable payload from the exact static question
coordinate, and uses the checked result itself as the Foundation owner-local
coordinate. No result field can be projected independently. Exporting any
other checked operation requires another exact Relations family, descriptor,
manifest, and owner formation law in a later profile revision.

The invocation-issued
[`PublicSetupInvocationView`](../pir/interactive-core.md#134-invocation-issued-public-setup-view)
is the only portable exception among the four correspondence owner views: its inert
`PortableSourceAuthorityBinding` is keyed by the view ID, but its live
capability is still exact and nontransferable. `CheckCorrespondence` consumes
the exact owner products and cannot call an unqualified raw-body lookup.

```text
CorrespondenceOwnerViewSet = {
  protocol: None | Some(affirmative ProtocolStaticCorrespondenceView issuance),
  protocol_interface:
    None | Some(affirmative ProtocolInterfaceCorrespondenceView issuance),
  plan_surface: None | Some(affirmative PlanSurfaceCorrespondenceView issuance),
  relations: None | Some(affirmative RelationsCorrespondenceView issuance)
}

OwnerViewSetMatches(manifest,views) iff
  each component is None exactly when its canonical submanifest is empty,
  each present view's requested reads equal that submanifest byte-for-byte,
  each binding and fresh capability is the exact issuance object for that
    exact view, typed consumer, and purpose, and
  the four realized field/read unions contain no cross-owner alias
```

Run reads remain execution-issued `RelationRunView` operands with their exact
fresh authority. They are not folded into a static owner view and cannot be
replaced by a completed-record lookup.

Confidential material agreement uses a fifth, deliberately non-view-set input
class:

```text
ConfidentialInitialOracleGroundingInput = {
  edge: OracleEdgeRef,
  relation_assignment:
    exact OracleMaterialAssignment for the question's RelationInstance,
  relation_secret_capability:
    identical live SecretValueCapability for the edge's RelationOracleRef,
  pir_view: exact ConfidentialInitialOracleView for the derived coordinate,
  pir_authority: exact CheckedConfidentialInitialOracleViewAuthority,
  pir_capability: identical live ConfidentialInitialOracleViewCapability,
  disclosure_policy_id:
    exact ConfidentialInitialOracleDisclosurePolicyId of
      ConfidentialInitialOraclePolicyFor(question,binding,edge)
}

ConfidentialInitialOracleGroundingInputs(q) =
  ExactMapOver<
    every and only OracleEdgeRef selected by OracleMaterialAgreement in q,
    ConfidentialInitialOracleGroundingInput>

RunGroundingExecutionBasis =
    Causal {
      protocol: identical admitted Protocol handle,
      invocation: identical CoreInvocation object,
      completed_record: identical CompletedProtocolRecord object,
      generation: identical live CausalGenerationCapability
    }
  | Replay {
      protocol: identical admitted Protocol handle,
      invocation: identical CoreInvocation object,
      completed_record: identical CompletedProtocolRecord object,
      replay_match: identical fresh CheckedReplayMatch
    }

RunGroundingExecutionBasisFor(q,public_view,confidential_inputs) =
  the basis retained by the public CheckedRelationRunViewAuthority when the public
  run submanifest is nonempty; otherwise the Causal basis retained by the
  confidential input at the first canonical OracleEdgeRef for RunGrounding or
  first canonical PlanWitnessEdgeRef for PlanWitnessRunGrounding; require every
  remaining run-bearing authority and capability to retain that exact same
  object-identical basis

ConfidentialPlanWitnessGroundingInput(q,binding) = {
  selection:
    exact ConfidentialPlanWitnessSelectionFor(q,binding),
  relation_assignment:
    exact fresh PrivateWitnessAssignment for q.instance_id,
  relation_secret_capabilities:
    ExactMapOver<q.edges,
      identical live SecretValueCapability for the edge's RelationWitnessRef>,
  pir_view:
    exact ConfidentialPlanWitnessView for
      ManifestFor(q).confidential_plan_witness,
  pir_authority: exact CheckedConfidentialPlanWitnessViewAuthority,
  pir_capability: identical live ConfidentialPlanWitnessViewCapability,
  disclosure_policy_id:
    exact ConfidentialPlanWitnessDisclosurePolicyId of
      ConfidentialPlanWitnessPolicyFor(q,selection),
  binding_payload_id: exact ConfidentialPlanWitnessBindingPayloadId,
  capability_requirement_id:
    exact ConfidentialPlanWitnessCapabilityRequirementId,
  policy_closure_id: exact ConfidentialPlanWitnessPolicyClosureId
}
```

The policy named by each map value must resolve to the exact imported policy
body derived by `ConfidentialInitialOraclePolicyFor(q,binding,edge)`. The same
`CorrespondenceQuestionId` of `q` is supplied to the consumer and purpose role
constructors, but the resulting IDs remain nominally distinct. The PIR
coordinate, view, authority, capability, Protocol, invocation, completed run,
initial-supply occurrence, and causal generation must all be the identical
issuance basis.
Only an affirmative `IssueConfidentialInitialOracleView` outcome for that
exact basis may populate the PIR fields; a raw carrier or declassified trace
cannot.
The relation assignment must be the exact same-instance owner occurrence and
the secret capability must be its identical bearer for the selected relation
Oracle. This input map is live operation state. It has no body compiler,
semantic ID, portable encoding, copy constructor, or cold-replay form.

`RunGroundingExecutionBasisFor` is an operation-local derived relation, not a
caller-supplied operand, portable body, semantic subject, or ID. A well-formed
`RunGrounding` always has at least one run-bearing source: a relation-bound
public check creates a public run read, while a material-only question has a
nonempty confidential input map. A `PlanWitnessRunGrounding` has its one
nonempty confidential Plan-witness input. If any material-agreement arm or a
Plan-witness arm is present, the selected basis must be `Causal`, and every
run-bearing input must retain the identical generation capability. Equality of
Protocol IDs, invocation IDs, record bytes, carriers, or receipts cannot
substitute for object identity.

For `PlanWitnessRunGrounding`, the four PIR policy artifacts must be the exact
closed tuple derived from the question ID, binding surface, canonical key set,
and source requirement. The view, authority, and capability must be the
identical affirmative `IssueConfidentialPlanWitnessView` products for either a
valid `Generated` source or the required `Finalized` source. The relation
assignment belongs to the exact question instance and each secret capability
is its identical bearer for the selected witness endpoint. The input is live
operation state, has no semantic ID or portable form, and exposes neither the
view nor any secret value through the checked-result body.

## 5. Completed result payloads and authority

This page imports the common qualified-outcome partition from K1 and the
relation model exactly once. It defines only correspondence payloads:

```text
QuestionCoordinate =
    Edge(StatementEdgeRef | PhaseEdgeRef | OracleEdgeRef |
         PlanWitnessEdgeRef)
  | RelationOccurrence(RelationPublicRef | RelationWitnessRef)
  | StatementOccurrence(BindingRef)
  | PlanSurfaceOccurrence(PlanWitnessSurfaceId, WitnessSurfaceKey)
  | ClaimMeaning(ClaimMeaningRef)
  | ReductionMeaning(ReductionMeaningRef)
  | ExternalSelector(ExternalInstanceSelector)
  | ArtifactClause(ArtifactComparisonQuestionId, artifact_clause_ordinal)
  | GroundingEquality(GroundingEquationOwner, equality_ordinal)
  | CommitmentClause(CommitmentClauseRef)
  | RunCheck(RunFactCheck)

CorrespondenceAgreement =
    EdgeAgrees(QuestionCoordinate)
  | CoverageMember(QuestionCoordinate)
  | ShapeAgrees(QuestionCoordinate)
  | ValueAgrees(QuestionCoordinate)
  | EqualityTrue(QuestionCoordinate)
  | RelationBoundValueAgrees(QuestionCoordinate)
  | OracleMaterialAgrees(QuestionCoordinate)
  | ExpectedValueAgrees(QuestionCoordinate)
  | ExpectedMetaAgrees(QuestionCoordinate)
  | PresenceAgrees(QuestionCoordinate)

CorrespondenceDisagreement =
    MappingPolicyDisagreement(QuestionCoordinate)
  | MissingCoverage(QuestionCoordinate)
  | OverlappingCoverage(QuestionCoordinate, QuestionCoordinate)
  | ShapeDisagreement(QuestionCoordinate)
  | ValueDisagreement(QuestionCoordinate)
  | MetaDisagreement(QuestionCoordinate)
  | EqualityFalse(QuestionCoordinate)
  | OracleMaterialDisagreement(QuestionCoordinate)
  | PresenceOrOccurrenceDisagreement(QuestionCoordinate)

CheckedCorrespondence = {
  question_id: CorrespondenceQuestionId,
  manifest: CorrespondenceReadManifest,
  agreements: CanonicalSortedUniqueSeq<CorrespondenceAgreement>,
  disagreements: CanonicalSortedUniqueSeq<CorrespondenceDisagreement>
}
```

`Completed(Affirmative(...))` requires an empty disagreement sequence.
`Completed(Negative(...))` requires a nonempty disagreement sequence and
retains every independently established agreement. Two well-typed endpoint
values may disagree and yield Negative; an ill-typed selector, wrong reference
kind, wrong owner, or unresolvable coordinate is malformed before the
proposition exists and never yields Negative. After formation, a formed typed
reference supplied on the wrong required subject axis is `KindMismatch`; this
does not turn a formation defect into a substantive disagreement.

Endpoint type, selector type, and expected-value type mismatches make question
formation malformed; they cannot produce an admitted proposition and therefore
have no disagreement constructor.

`OracleMaterialAgrees` and `OracleMaterialDisagreement` name only the exact
`RunCheck(OracleMaterialAgreement(edge))` coordinate. They serialize neither
carrier, either local occurrence, a trace or record reference, a capability,
nor a material-derived digest. The operation-local capability may retain the
live inputs for its own lifetime, but the checked-result body does not.

Only completed affirmative or negative results receive the exact
question-, operand-, and manifest-bound fresh operation-local capability.
IDs, serialized records, manifests, and source bindings are inert and grant no
authority. Section 4.3 deliberately does not invent a generic checked-result
source family: exporting this result to another owner requires a later exact
family, typed consumer and purpose, source descriptor, and manifest rather
than treating this operation-local capability as transferable authority.

## 6. Structural and coverage operations

All named operations below are specializations of:

```text
CheckCorrespondence(
  admitted CorrespondenceQuestion,
  every exact admitted operand named by the question,
  exact CorrespondenceOwnerViewSet for ManifestFor(question),
  exact RelationRunView sequence for its run submanifest,
  exact ConfidentialInitialOracleGroundingInputs(question),
  exact optional ConfidentialPlanWitnessGroundingInput(question,binding)
    for the uniquely resolved PlanWitnessBinding,
  every matching live owner-view capability and
    CheckedRelationRunViewAuthority,
  exact evaluator support and limits)
  -> Qualified<CheckedCorrespondence>
```

The structural families are:

```text
CheckMappedStatementCorrespondence(MappedStatements)
CheckWholeRelationPublicCoverage(WholeRelationPublic)
CheckWholeStatementCoverage(WholeStatement)
CheckMappedPlanWitnessCorrespondence(MappedPlanWitness)
CheckWholeRelationWitnessCoverage(WholeRelationWitness)
CheckWholePlanWitnessSurfaceCoverage(WholePlanWitnessSurface)
CheckClaimReductionShape(ClaimReductionShape)
```

Mapped checks establish exact references, selectors, types, bridge direction,
and the selected functionality/injectivity propositions. They do not establish
whole coverage or runtime equality.

Whole relation-public coverage requires the selected relation-side slices to
form one exact nonoverlapping cover of every `RelationPublicRef` value in the
named Interface. Whole Statement coverage requires the selected target slices
to cover every Statement occurrence in `StatementDomain`. Session Context and
Public Parameter bindings are never in that domain. Neither direction implies
the other.

Whole relation-witness coverage covers every `RelationWitnessRef` in the
binding's exact Interface. Whole Plan-surface coverage covers every
`WitnessIngress` or `DerivedWitnessExport` entry in the exact surface. Advice,
confidential context, randomness, state, and unexported values are absent from
both propositions.

`ClaimReductionShape` checks only:

1. exact K2 claim source, contract, scope, and usage;
2. recipe source domains and result-Interface typing;
3. ordered input/output claim meanings against the exact K2 declaration;
4. exact side-input, challenge, and complete publication-requirement ordinal
   maps, including every `next_challenge`;
5. transform input/output Interface and public-derivation ABI agreement; and
6. occurrence, scope, guard, and order coordinates already owned by K2.

It does not check witness evolution, a relation refinement, prover/verifier
output agreement, reduction soundness/completeness, or any cryptographic
property.

## 7. External presentation and instance operations

```text
CheckExternalStatementPresentation(ExternalStatement)
CheckExternalInstanceCorrespondence(ExternalInstance,
                                    exact DecodedExternalAssignment,
                                    matching codec-evaluation authority)
```

External Statement presentation follows each selected Interface member through
its exact codec and flow to one selected scoped Statement edge. It checks
audience, direction, type, multiplicity, scope, and the selected mapped/whole
coverage proposition. Under `WholeSelectedSurface`, it additionally checks the
exact member/binding domain and recursive target partitions defined in Section
3.1; it does not silently widen to every member of the Interface.
Verifier-private invocation inputs remain covered by the Interface assignment
lens but can never be Statement members.

External instance correspondence compares canonical typed values through the
selected public, Oracle-binding, or phase path. An Oracle-public-binding path
forms only through a `PublicBoundOracleTarget` and additionally requires the
exact PIR `PublicBinding` publication mode, compatible relation/PIR index and
answer types, admitted binding construction, public publication occurrence,
and matching public transport entry. A `LogicalOracleTarget` has no public
publication value and cannot be smuggled through this external selector; its
material agreement belongs only to the causal run-grounded operation. A phase
path names its exact challenge or public occurrence and transport entry.
Repeated equal values are checked at distinct coordinates.

For a transport selector, `Inactive` is a well-formed
`PresenceOrOccurrenceDisagreement`; `Active(v)` compares only its typed payload
`v` through the selected edge's `ValueRelation`. The wrapper is never passed to
that relation as though it had payload type. The assignment's key domain is
every and only the admitted Interface's external slots, and each value has its
slot codec's exact semantic type. Missing, extra, wrong-type, or ill-shaped
assignments are `Malformed`; absent matching codec authority or a
caller-constructed assignment is `Refused`. Neither is Negative.

These operations concern one decoded external assignment. They say nothing
about what a verifier run consumed and do not inspect private relation or Plan
material.

## 8. Artifact, equation, and commitment operations

```text
CheckArtifactInterfaceComparison(
  ArtifactComparison,
  exact admitted ArtifactComparisonQuestion,
  exact admitted RelationInterface,
  exact owner-issued RelationArtifactObservation,
  matching fresh interpretation-or-replay authority)

CheckGroundingEquation(
  EquationGrounding,
  exact GroundingInvocation and every required fresh source capability)

CheckCommitmentGrounding(
  CommitmentGroundingCheck,
  SelectedCommitmentInvocations,
  every required fresh source capability)
```

where:

```text
SelectedCommitmentInvocations =
  ExactMap<CommitmentClauseRef, GroundingInvocation>
```

Its key set is exactly the question's `clauses`; each invocation's
`equation_id` is identical to that binding clause's equation ID and its operand
map exactly exhausts `RequiredGroundingOperandSlots(equation)`. Its run
operands have exactly the qualification required by the question's matching
inner run-requirement map.
Missing, extra, duplicate, wrong-equation, or wrong-qualification entries do
not create a false proposition. A bad key domain or wrong equation is
`Malformed`; a wrong authenticated subject is `Refused`; and an absent required
capability or qualification is `CannotAnswer`.

Artifact comparison can consume only an observation issued by the relation
model's exact interpretation operation over authenticated bytes. `Unread`
yields `CannotAnswer`; `Observed([])` is an observed absence and may yield a
meaningful disagreement. An invalid selector is malformed. The result concerns
only selected fields and relation facts.

Grounding evaluation reads exactly the derived operand-slot set, evaluates
steps in topological order, and records every equality. A false equality is
Negative. A missing secret occurrence, unread artifact field, missing run fact,
unsupported algorithm, or operational noncompletion is not false equality.

Each commitment grounding connects every typed construction input and its one
publication target to exact equation sources, the exact construction step, and
the exact equality. The construction ABI and every selected coordinate must
agree before evaluation. A true equation establishes only that exact
construction equality at those occurrences; it establishes no binding,
hiding, extraction, opening knowledge, or verifier soundness. A commitment is
not a lossy value bridge.

## 9. Run-grounded operations

### 9.1 Public and initial-Oracle grounding

```text
CheckRunGroundedCorrespondence(
  admitted RunGrounding q,
  exact admitted RelationInstance,
  exact admitted ProtocolRelationBinding,
  when q's public run submanifest is nonempty:
    PIR-issued public-only RelationRunView and matching fresh authority,
  exact ConfidentialInitialOracleGroundingInputs(q),
  when RunGroundedPotentialLossyCoordinates(q) is nonempty:
    exact BridgeUseSet set for RunGroundedBridgeUseScope(q) and fresh
      affirmative authority,
    exact LossyUseSelection equal to RunGroundedLossySelection(q,set),
    exact overall-Affirmative CheckedLossyUsePremiseSet for that selection and
      fresh capability,
    fresh affirmative CheckLossyUseAtConsumerSource result and capability for
      every coordinate in that exact selection)
  -> Qualified<CheckedCorrespondence>
```

Before reading a selected value or carrier, the operation derives exactly one
`RunGroundingExecutionBasisFor` and validates every run-bearing source against
it. When present, the public run view's Protocol and qualification must match the
question. Its issuance authority must retain the exact invocation and source
binding required by the operation. Its payload contains every and only the
public coordinates in `ManifestFor(question)`; the full
`CompletedProtocolRecord` remains in PIR's private source binding and is not a
correspondence read. A material-only question has an empty public run
submanifest and therefore supplies no `RelationRunView`; this does not convert
the confidential view into a public run view.

A source from another invocation, completed-record object, causal generation,
or replay occurrence is `Refused`, even if all selected values and canonical
record bytes are equal. A missing live basis authority is `CannotAnswer`; an
ill-formed authority carrier is `Malformed`; and disagreement between an
owner-authenticated authority and its retained basis is `CheckerFailure`.
These checks precede substantive agreement classification, so mixed-run
operands can never produce `Negative` or an affirmative partial result.

For every lossy-source authority used by this operation, both downstream
coordinates supplied to the two nominal role constructors are the exact
`CorrespondenceQuestionId` of `q`. The resulting consumer and purpose IDs are
still distinct because their subject kinds differ. This binds the source to
this exact run-grounding proposition without adding a label or a new purpose
registry; a different question ID cannot reuse the authority.

For every `RelationBoundValue` check, Relations selects the exact instance
value and exact `Available` run value and applies the edge's admitted
`ValueRelation`. A lossy bridge use additionally requires its exact checked
occurrence-local source premise from one overall-Affirmative
`CheckedLossyUsePremiseSet` over the exact
`RunGroundedLossySelection(q,set)`. For every coordinate in that selection it
consumes a fresh affirmative
`CheckLossyUseAtConsumerSource` result whose live `LossySourceBinding` equals
the exact `RelationInstance` field binding and source capability consumed by
this operation, including owner, subject, field coordinate, local occurrence
where applicable, process generation, and capability contract. A premise
checked for another instance, generation, or equal-valued occurrence is
refused; a static `BridgeUseCoordinate` cannot establish the join. The result
retains its ordinary exact question, manifest, and agreement coordinates; it
does not serialize the live selection or joins. The fresh overall-Affirmative
checked-result capability retains the exact `LossyUseSelection`, premise-set
capability, and every consumer-source join result and capability. Only that
fresh capability licenses Analysis to consume
`SelectedBridgeUseCardinality(selection,b)`. Missing premise or join authority
is `CannotAnswer`, never inequality.
`Inactive` or `NotReached` yields a presence disagreement rather than a value
disagreement.

For every `OracleMaterialAgreement(edge)`, Relations requires the exact map
entry derived in Section 4.2. It independently authenticates the relation
assignment, selected relation Oracle, PIR coordinate, whole-carrier type,
disclosure policy, exact question-bound consumer and purpose, causal
qualification, view authority, and both live capabilities. It then reads the
whole relation carrier and the whole PIR carrier through their respective
identical bearers and compares them by Foundation same-type equality. It does
not pass either value to a caller-supplied predicate or bridge.

For the selected `LogicalOracleTarget` edge `e`, the complete comparison law
is:

```text
relation_material =
  ReadWholeCarrier(
    matching OracleMaterialAssignment for q.instance_id and e.relation.ref,
    identical live SecretValueCapability for e.relation.ref)

pir_material =
  ReadWholeCarrier(
    matching ConfidentialInitialOracleView whose coordinate is {
      protocol_id: binding.protocol_id,
      oracle: e.protocol.oracle,
      publication: e.protocol.publication_occurrence
    },
    identical CheckedConfidentialInitialOracleViewAuthority,
    identical live ConfidentialInitialOracleViewCapability)

Type(relation_material)
  = Type(pir_material)
  = ResolvedOracleDecl(e.relation.ref).material_type
  = OracleCarrierType(e.protocol.oracle)

FoundationSameTypeEquality(relation_material,pir_material) = true
```

The two `ReadWholeCarrier` operations are available only through the exact
question-bound live inputs above. The equation is therefore neither a lookup
by carrier bytes nor an ambient equality predicate.

Equal carriers add `OracleMaterialAgrees` for that edge. Unequal well-formed
carriers add `OracleMaterialDisagreement` for that edge, including when the
only difference is at an unqueried Oracle entry. The result names only the
edge. It retains no carrier, occurrence, trace, record, capability, or digest.
An absent exact authenticated subject, profile, policy, or algorithm preimage
is `MissingDependency`. A missing or expired otherwise matching live source is
`CannotAnswer`; a wrong
assignment occurrence, initial-supply occurrence, invocation, run, policy,
consumer, purpose, reconstructed bearer, or replay-qualified runtime source is
`Refused`; a wrong kind, regime, or type is `KindMismatch`; an unsupported
origin or publication mode is `Unsupported`; a structural defect is
`Malformed`; exact
bound exhaustion is `DeterministicLimitExceeded`; and an evaluator or
postcondition inconsistency is `CheckerFailure`. None of those outcomes is a
material disagreement.

For `ExpectedValue`, an `Available` payload is compared with the question's
exact typed canonical value using Foundation equality. `ExpectedCheckResult` and
`ExpectedTerminalVerdict` compare only their respective closed meta types.
A different well-formed value or meta value is Negative; a different outer
observation alternative is a presence disagreement. `Presence` compares the
outer `Available | Inactive | NotReached` tag only and, when it agrees, records
`PresenceAgrees`; it makes no claim about an available payload.

In particular, a `Presence(ClaimState(...),RequireAvailable)` or
`Presence(ReductionState(...),RequireAvailable)` proves only that PIR exposed
that public history coordinate at the requested boundary. It does not compare
the history, prove claim creation, prove a reduction application, or establish
relation meaning. Exact claim/reduction-state comparison is `Unsupported` in
the current grammar. A different repeated occurrence, inactive guarded
occurrence, or unreached boundary is Negative only when an admitted check
selected a different status or expectation. A missing manifest entry or
caller-created value is respectively `CannotAnswer` or `Refused`.

`ExactReplayQualified` requires a `ReplayQualified` public view and answers
what exact PIR replay consumed. `ExactCausallyGenerated` requires a
`CausallyGenerated` public view and the still-live PIR causal capability;
replay cannot mint it. Any `OracleMaterialAgreement` requires the latter and
also requires a PIR `CausallyGeneratedOnly` confidential-view policy. Neither
qualification proves relation satisfaction, honest strategy, coin
distribution, or implementation isolation.

No private witness, verifier-private query or answer, prover Oracle, Plan
state, advice, randomness, or strategy-local value is readable by this public
operation. Initial logical-Oracle material is readable only inside the exact
agreement operation, only as the whole same-typed carrier, and only under the
two purpose-bound live authorities above. It is not returned to the caller or
made available through the public selector vocabulary.

### 9.2 Causal Plan-witness grounding

```text
CheckPlanWitnessRunGrounding(
  admitted PlanWitnessRunGrounding q,
  exact admitted RelationInstance,
  exact admitted PlanWitnessBinding binding,
  exact ConfidentialPlanWitnessGroundingInput(q,binding),
  when PlanWitnessGroundedPotentialLossyCoordinates(q) is nonempty:
    exact BridgeUseSet set for PlanWitnessGroundedBridgeUseScope(q) and fresh
      affirmative authority,
    exact LossyUseSelection equal to
      PlanWitnessGroundedLossySelection(q,set),
    exact overall-Affirmative CheckedLossyUsePremiseSet for that selection and
      fresh capability,
    fresh affirmative CheckLossyUseAtConsumerSource result and capability for
      every coordinate in that exact selection,
  exact evaluator support and deterministic limits)
    -> Qualified<CheckedCorrespondence>
```

Before reading either selected value, the operation derives the one causal
`RunGroundingExecutionBasisFor(q,None,{the exact confidential Plan-witness
input})`. The input's view authority, capability, completed Plan run, Protocol
causal authority, invocation, and `CompletedProtocolRecord` must all retain
that object-identical basis. The affirmative operation-local capability
retains the derived basis for the later same-run join; the portable result body
does not serialize it.

For every selected edge, the operation resolves the exact surface entry,
relation witness endpoint, both selectors, selected types, and admitted value
relation. The relation value is read from the exact fresh assignment bearer.
The Plan value is read only from the exact purpose-bound confidential view.
`SuppliedForGeneration` names the prepared-session private occurrence;
`ProducedWhenSourceDecisionActive` requires its source decision to be active
in the retained generated run; and
`ProducedWhenAcceptedTerminalReached` requires the exact `Finalized` source
and atomically issued active continuation arm.

The policy, payload, requirement, and closure are derived from the exact
`CorrespondenceQuestionId(q)` through nominally distinct PIR consumer and
purpose role IDs. A caller cannot substitute a label, another question, an
equal surface, or a wider manifest. Each lossy edge additionally consumes its
question-bound premise and the `IssuePrivateWitnessFieldSource` bearer for the
same assignment occurrence through `CheckLossyUseAtConsumerSource`.

An edge whose value relation completes true adds
`ValueAgrees(Edge(edge))`; one that completes false adds
`ValueDisagreement(Edge(edge))`. The latter is semantic Negative. An absent
exact authenticated subject, profile, policy, or algorithm preimage is
`MissingDependency`. A missing, inactive, unfinalized, or expired required
source is `CannotAnswer`; a cross-
run, cross-Plan, cross-surface, wrong-policy, wrong-consumer, or wrong-purpose
source is `Refused`; wrong kind or type is `KindMismatch`; a duplicate,
partial, noncanonical, or extra manifest is `Malformed`; replay qualification
is `Refused`; and bounded evaluator failures retain their ordinary
qualified lanes. None becomes a value disagreement.

The fresh checked-result capability retains the exact question, binding,
instance, assignment and secret bearers, confidential view/authority/bearer,
lossy inputs, completed Plan run, and Plan/Protocol causal authorities. The portable
`CheckedCorrespondence` body retains only its question ID, manifest, and
agreement/disagreement coordinates.

```text
JoinPlanWitnessAndPublicRunGrounding(
  exact affirmative CheckedCorrespondence private_result for
    PlanWitnessRunGrounding,
  identical live private checked-result capability,
  exact affirmative CheckedCorrespondence public_result for a causal
    RunGrounding question,
  identical live public checked-result capability and
    CheckedRelationRunViewAuthority)
    -> Qualified<Affirmative({
         result: CheckedSameRunPlanWitnessCorrespondence,
         capability: CheckedSameRunPlanWitnessCorrespondenceCapability
       })>
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

The join requires the identical admitted `RelationInstance`, `ProtocolId`,
live `CoreInvocation` object, live `CompletedProtocolRecord` object, and
identical live `CausalGenerationCapability` on both sides. Equal bytes,
values, records, or separately generated occurrences do not join. It imposes
the additional exact-use condition that both affirmative inputs retain the
same operation-derived basis returned by `RunGroundingExecutionBasisFor`; a
caller-supplied or reconstructed tuple cannot stand in for that basis. It
imposes no generic "intended fold output" beyond the coordinates already selected by
the two questions. The result and capability are process-local and
nonidentified. The capability retains the two identical input results and
their checked-result, run-view, Plan-generation, and Protocol causal
capabilities;
it therefore retains the private question, binding, surface extraction,
assignment occurrence, and completed Plan run rather than reconstructing them
from either result body. The join establishes only that the selected public
and private correspondence results belong to one causal run—not witness
satisfaction, fold preservation, output-to-next-input handoff, or IVC
induction.

### 9.3 Direct causal Plan-witness handoff

The next operation selects one already-agreeing private edge from each of two
same-run results. The source edge must resolve to a
`DerivedWitnessExport`; the target edge must resolve to a fresh
`WitnessIngress`. Selection is operation-local and has no question body or
semantic ID:

```text
JoinCausalPlanWitnessHandoff(
  exact affirmative CheckedSameRunPlanWitnessCorrespondence source_run,
  identical live CheckedSameRunPlanWitnessCorrespondenceCapability
    source_run_capability,
  exact PlanWitnessEdgeRef source_edge selected by source_run's private
    PlanWitnessRunGrounding question,
  exact source RelationInstance operand and exact source
    PrivateWitnessAssignment occurrence retained by source_run_capability,
  exact source CompletedPlanRun object retained by source_run_capability,
  exact Finalized ConfidentialPlanWitnessSource retained by
    source_run_capability whose CompletedPlanContinuation is the handoff
    source continuation,
  exact affirmative CheckedSameRunPlanWitnessCorrespondence target_run,
  identical live CheckedSameRunPlanWitnessCorrespondenceCapability
    target_run_capability,
  exact PlanWitnessEdgeRef target_edge selected by target_run's private
    PlanWitnessRunGrounding question,
  exact target RelationInstance operand and exact target
    PrivateWitnessAssignment occurrence retained by target_run_capability,
  exact target CompletedPlanRun object retained by target_run_capability,
  identical live CausalPlanWitnessHandoffCapability handoff_capability)
    -> Qualified<Affirmative({
         result: CheckedPlanWitnessHandoffCorrespondence,
         capability: CheckedPlanWitnessHandoffCorrespondenceCapability
       })>
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

The operation performs the following complete match before issuing its
result:

1. each same-run capability opens exactly one affirmative public/private pair
   and retains the identical question, binding, admitted relation instance,
   private assignment occurrence, Plan surface and checked extraction,
   `CoreInvocation`, `CompletedProtocolRecord`, `CompletedPlanRun`, and Plan
   and Protocol causal capabilities used by that pair;
2. `source_edge` and `target_edge` occur exactly once in their respective
   private questions and both already have `ValueAgrees(Edge(edge))` in the
   checked result;
3. the source private grounding used a `Finalized` confidential source whose
   `CompletedPlanContinuation` and `CausalPlanContinuationCapability` are the
   identical source objects retained by `handoff_capability`; a merely
   `Generated` source is insufficient for this join even when the selected
   decision-derived export ordinarily has `GeneratedSufficient` disclosure;
4. the source binding edge's Plan key resolves through the retained checked
   extraction to the exact `DerivedWitnessExportRef`. For a decision-derived
   export, the identical continuation capability links its already sealed
   decision occurrence to that exact export's active continuation-output
   occurrence; for a terminal-derived export it links the exact terminal
   occurrence directly. This owner-retained export-ref/occurrence relation,
   not value equality, must name the source output occurrence retained by
   `handoff_capability`. The target edge's Plan key likewise resolves to the
   exact `PrivateMaterialRef` of kind `WitnessIngress` and fresh private-
   material occurrence retained by that capability;
5. the source and target selected Plan types equal the exact source and target
   types of the handoff capability, and the capability records the direct
   same-type copy from that source occurrence to that target occurrence; and
6. the capability is the identical bearer created when the exact
   `ReadyPlanWitnessIngressSupply` was consumed during preparation of the
   target Plan session, is retained by the target
   `CausalPlanGenerationCapability`, and in turn retains the source
   continuation, source Plan-generation, and target preparation occurrences.

The two relation instance operands are role-distinct even when their
`RelationInstanceId` values are equal. The two private assignments, selected
edges, Plan runs, export and ingress occurrences, and causal capabilities
remain distinct exact operands. Equality of instance IDs, values, surface
keys, result bodies, record encodings, or separately reconstructed
capabilities cannot satisfy any item above.

`CheckedPlanWitnessHandoffCorrespondence` and its capability are
noncopyable, nonserializable, process-local, and nonidentified. They retain
the complete source and target operands, selected edges, same-run results and
capabilities, and the identical handoff capability. They establish the exact
direct causal chain

```text
source relation-secret occurrence
  -> selected source Plan export occurrence
  -> fresh target WitnessIngress occurrence
  -> target relation-secret occurrence
```

under the two already-checked edge relations. They do not infer equality
between the two relation selectors when those edge relations or selectors
differ, relation satisfaction, fold preservation, or a public recurrence.
A selected edge outside its question, an extra or duplicate selector, or an
ill-shaped pair is `Malformed`; a well-formed non-export/non-ingress pair is
`Unsupported`; a `Generated` rather than identical `Finalized` source, or a
wrong live run, continuation, occurrence, assignment, surface, Plan, or bearer
is `Refused`; an expired otherwise matching bearer is `CannotAnswer`;
and a type or regime mismatch is `KindMismatch`. There is no Negative arm:
the underlying value disagreements are already Negative inputs and therefore
cannot enter this affirmative-only join.

### 9.4 One-step causal recurrence conjunction

An arbitrary true equation over two runs is not a recurrence proposition. The
final join therefore takes one public selection that fixes the complete
source-output-to-target-input chain. These references are dense ordinals in
the exact admitted grounding equation. The selection has no standalone ID,
but it has the written `RB` body when embedded in the owner-defined question
coordinate below:

```text
GroundingSourceRef = ordinal in GroundingEquation.sources
GroundingEqualityRef = ordinal in GroundingEquation.equalities

PublicRecurrenceEquationLeg = {
  left_tip: GroundingValueRef,
  right_tip: GroundingValueRef,
  equality: GroundingEqualityRef
}

CausalPublicRecurrenceSelection = {
  source_run_slot: GroundingRunSlotRef,
  target_run_slot: GroundingRunSlotRef,
  source_instance_slot: GroundingInstanceSlotRef,
  target_instance_slot: GroundingInstanceSlotRef,
  source_output_source: GroundingSourceRef,
  source_instance_source: GroundingSourceRef,
  target_instance_source: GroundingSourceRef,
  target_statement_source: GroundingSourceRef,
  source_output_grounding: PublicRecurrenceEquationLeg,
  instance_transition: PublicRecurrenceEquationLeg,
  target_input_grounding: PublicRecurrenceEquationLeg
}

CausalPlanStepRecurrenceQuestionCoordinate = {
  equation_grounding_question_id: CorrespondenceQuestionId,
  public_selection: CausalPublicRecurrenceSelection,
  source_plan_witness_binding_id: PlanWitnessBindingId,
  source_edge: PlanWitnessEdgeRef,
  target_plan_witness_binding_id: PlanWitnessBindingId,
  target_edge: PlanWitnessEdgeRef
}
```

This coordinate is not a new semantic subject. It is a canonical Relations
law coordinate over already identified static subjects. Formation
authenticates the `EquationGrounding` question and both Plan-witness bindings;
requires each edge to occur exactly once in its named binding; derives the
source `DerivedWitnessExport` and target `WitnessIngress` surface roles; and
requires the selection to fit the question's exact equation. It contains no
run, instance, assignment, private value, result, capability, or future ID. A
changed edge, equation, selection ordinal, or binding is therefore a different
coordinate without turning one live recurrence occurrence into a durable
subject.

Let `P_source` be the exact admitted Protocol authenticated for
`e.run_slots[s.source_run_slot]`, and let `C_source` be the exact admitted
`InteractiveCore` whose ID is `P_source.core_id`. The operation-local closed
predicate `CausalRecurrencePublicOutputCoordinate(P_source,C_source,c)` is true
exactly for:

```text
OccurrenceOutput(o,0)
  when C_source.occurrences[o].effect is ProverMessage or
       DeterministicVerifierMessage
OraclePublication(oracle,o)
  when the effect at o is PublishOracle(oracle) and its publication mode is
       FullCanonicalOracle or PublicBinding
TerminalPublicOutput(t,o,k)
  when the effect at o is ReachTerminal(t) and k is an exact public-output
       ordinal of t
PublicModuleObservation(o,k)
  when the effect at o is a supported ModuleEffect and k is an exact
       declaration-owned public module-observation output ordinal
```

It is false for every other coordinate, including `BindingValue`,
`ChallengeValue`, public or private Oracle Query/Answer, a logical-access
fixation marker, Check/Reduction output, a raw Oracle/Terminal/Module
`OccurrenceOutput`, a private or structural output, and an unsupported module
effect. Thus the source is an exact owner-classified publication or public
output, not merely any value that happens to have an occurrence ordinal.

`SingleDynamicGroundingPath(e,root,tip)` is the following closed structural
predicate. `tip` is either `Source(root)` or a step reachable from it. In the
transitive input closure of `tip`, the only nonconstant source is `root`; each
dynamic predecessor traces transitively to that root, and any other leaves are
exact `Constant` sources. Every cited step is in range, topologically earlier
than its consumer, and has the exact admitted ABI already checked for `e`.
Thus identity, branching/merging transformations of one dynamic value, and
fixed parameters are supported, while a second dynamic value cannot be hidden
inside a purported one-occurrence path.

`CausalPublicRecurrenceSelectionMatches(q,e,s,checked)` holds exactly when
`q` is the exact admitted `EquationGrounding` question for `e` and:

1. the source and target run slots are distinct and exhaust `e.run_slots`, the
   source and target instance slots are distinct and exhaust
   `e.instance_slots`, `e.artifact_slots` is empty, and the four source
   references are pairwise distinct;
2. `e.sources[s.source_output_source]` is
   `ProtocolValue(s.source_run_slot,c,p)` and
   `CausalRecurrencePublicOutputCoordinate(P_source,C_source,c)` holds;
3. `e.sources[s.target_statement_source]` is
   `ProtocolValue(s.target_run_slot,BindingValue(b),p)` for an exact binding
   `b` whose class is `Statement`;
4. `e.sources[s.source_instance_source]` and
   `e.sources[s.target_instance_source]` are respectively
   `InstancePublic(s.source_instance_slot,r_source,p_source)` and
   `InstancePublic(s.target_instance_slot,r_target,p_target)`;
5. `source_output_grounding` has a left path rooted at
   `source_output_source`, a right path rooted at
   `source_instance_source`, and names the equality whose exact left and right
   values are those two tips;
6. `instance_transition` similarly connects `source_instance_source` to
   `target_instance_source`, and `target_input_grounding` connects
   `target_instance_source` to `target_statement_source`;
7. the three equality references are distinct and exhaust every equality in
   `e`; every step lies in at least one of the six selected single-dynamic
   paths; and every source is one of the four selected dynamic roots or a
   constant used by at least one selected path; and
8. the selected tips have the exact types written by their equalities,
   `checked.question_id` is the exact `CorrespondenceQuestionId(q)`, and for
   each selected leg `leg`, `checked.agreements` contains the exact coordinate
   `EqualityTrue(GroundingEquality(
   StandaloneEquation(q.equation_id),leg.equality))`. Because the three
   references exhaust `e.equalities` and `checked` is affirmative, these are
   every equality outcome for this equation rather than three caller-selected
   true facts from a larger result.

This exact-exhaustion rule rejects a self-equality, constant-only equality,
unrelated true clause, unused extra clause, confidential witness or Oracle-
material source, artifact source, extra public source, or hidden dynamic
dependency. It remains general over typed public representations because each
of the six sides may use its own explicit fixed-parameter transformation path.
The operation proves those exact written transformations; it does not infer
their cryptographic adequacy or information preservation.

The final Relations operation conjoins the matched public chain with the
private handoff. It adds no recurrence question or identified result:

```text
JoinCausalPlanStepRecurrence(
  exact affirmative CheckedPlanWitnessHandoffCorrespondence private_handoff,
  identical live CheckedPlanWitnessHandoffCorrespondenceCapability
    private_handoff_capability,
  exact affirmative CheckedCorrespondence public_recurrence for an admitted
    EquationGrounding question q,
  identical live public_recurrence checked-result capability,
  exact admitted GroundingEquation equation and exact GroundingInvocation
    invocation retained by that capability,
  exact CausalPublicRecurrenceSelection selection satisfying
    CausalPublicRecurrenceSelectionMatches(
      q,equation,selection,public_recurrence))
    -> Qualified<Affirmative({
         result: CheckedCausalPlanStepRecurrence,
         capability: CheckedCausalPlanStepRecurrenceCapability
       })>
     | Unsupported | MissingDependency | CannotAnswer | KindMismatch
     | Refused | Malformed | DeterministicLimitExceeded | CheckerFailure
```

Formation requires all of the following, without an ambient slot convention:

1. `q.equation_id` is the exact ID of `equation`; the checked result is
   overall-Affirmative and its fresh capability retains the identical
   `invocation`, complete computed table, source-authority bindings, and
   capabilities;
2. the equation's required run-slot set is exactly
   `{selection.source_run_slot,selection.target_run_slot}`, and
   `q.run_requirements` maps both and only both slots to
   `ExactCausallyGenerated`; the two live run occurrences are distinct even
   when their Protocol IDs or record bodies are equal;
3. the two `QualifiedRun` operands and their live view capabilities retain,
   respectively, the exact source and target `CoreInvocation`,
   `CompletedProtocolRecord`, and `CausalGenerationCapability` objects
   retained by `private_handoff_capability`;
4. `InstanceSlot(selection.source_instance_slot)` and
   `InstanceSlot(selection.target_instance_slot)` are distinct required
   operand slots,
   and their exact `RelationInstance` operands are respectively the source and
   target instances retained by `private_handoff_capability`; the matching
   source-authority bindings and capabilities are the identical ones consumed
   by the affirmative equation evaluation; and
5. `CausalPublicRecurrenceSelectionMatches(
   q,equation,selection,public_recurrence)` holds for the exact affirmative
   result, so its three selected equalities establish the exhaustive source-
   output, cross-instance, and target-input chain rather than an unrelated true
   equation; and
6. the source and target private-assignment occurrences, selected witness
   edges, source export, target ingress, source and target Plan runs, and
   `CausalPlanWitnessHandoffCapability` are exactly those retained by
   `private_handoff_capability`.

The operation also derives the unique
`CausalPlanStepRecurrenceQuestionCoordinate` from `q`, `selection`, and the
two selected Plan-witness bindings and edges retained by `private_handoff`.
The affirmative result and capability retain that exact coordinate. A caller
cannot supply a coordinate independently or replace one of its fields after
the checks above.

The instance slot occurrences remain source- and target-qualified even when
their content IDs are equal. A repeated ID does not merge two slots, and an
equal value, equation result body, run record, or fresh causal execution does
not substitute for an identical retained operand or capability.

`CheckedCausalPlanStepRecurrence` and its capability are noncopyable,
nonserializable, process-local, and nonidentified. They establish only the
conjunction of (a) the exact affirmative public equation over these two
causally generated runs and exact instance-slot occurrences and (b) the exact
direct private handoff above. They do not establish relation satisfaction,
relation refinement, fold or accumulation correctness, an unbounded
recurrence, IVC/NIVC induction, a decider theorem, or any security property.
An out-of-range, duplicate, or ill-shaped selection is `Malformed`; a formed
affirmative equation that violates the closed public-recurrence shape is
`Unsupported`; a wrong exact run, instance-slot occurrence, invocation,
assignment, selected edge, handoff, or source capability is `Refused`; an
expired otherwise matching live capability is `CannotAnswer`; a type, owner,
or regime mismatch is `KindMismatch`; and an inconsistent affirmative input is
`CheckerFailure`. This join has no Negative arm because either a false public
equality or a private edge disagreement is already a Negative prerequisite
rather than a completed recurrence conjunction.

For the narrow cross-owner use selected by Analysis, Relations exposes one
purpose-bound source operation:

```text
IssueCausalPlanStepRecurrenceResultSource(
  exact affirmative CheckedCausalPlanStepRecurrence result,
  identical live CheckedCausalPlanStepRecurrenceCapability result_capability,
  exact consumer: RelationsDownstreamCoordinate,
  exact purpose: RelationsDownstreamCoordinate)
  -> RelationsFieldSourceIssueOutcome<OwnerLocalSourceAuthorityBinding>
```

It derives family `"causal-plan-step-recurrence-result"`, source
`CausalPlanStepRecurrenceResultSource(result.question_coordinate)`, manifest
`CompleteCausalPlanStepRecurrenceResult`, the two role IDs, payload, no-policy
declaration, requirement, and closure from the exact result. The Foundation
local coordinate is that identical result object. The separately returned
fresh source capability retains the result capability, consumer, purpose,
question coordinate, process generation, and lifetime. A copied result,
reconstructed envelope, other question coordinate, stale capability, partial
field request, or equal run values refuse. This operation exports only the
already-checked one-step conjunction; it does not make it portable or promote
it to an induction premise.

## 10. Combined results, persistence, and nonclaims

An operation may combine affirmative mapped Statement results with an exact
`SelectedPlanWitnessBindings` map and the corresponding affirmative mapped
Plan-witness results. Every selected Interface key and Protocol must agree.
The aggregate retains each original question/result and source binding; it has
no new semantic ID or authority and implies neither `PlanRealizes` nor relation
satisfaction.

Structural, coverage, external-public, artifact, and equation checks may cold
replay only when every exact subject, source observation, purpose view,
algorithm, manifest, and result preimage is portable. Replay reauthenticates,
readmits, reissues owner views, reruns the checker, and requires complete result
equality before fresh authority is created.

A run-grounded result cold-replays only in the `ReplayQualified` lane. Causal
generation, private occurrences, and source-local capabilities never cold
replay. A fresh authorized execution creates fresh occurrence coordinates and
results. Consequently a question containing `OracleMaterialAgreement` has no
cold-replay lane: replay may validate observed answers, but it cannot establish
that a newly supplied carrier is the whole initial carrier used by the earlier
causal generation.

`PlanWitnessRunGrounding`, the same-run join, the direct handoff join, and the
one-step recurrence join have no cold-replay lane. Reauthentication may
recover the durable `PlanWitnessRunGrounding` question and its portable
checked-result body. The three nonidentified joins have no standalone question
or result body to recover; only their durable input questions and portable
input-result bodies can be reauthenticated. In every case only fresh generated
Plan runs and their live private authorities can recreate the live
proposition. The direct handoff operation supports the one same-process path
in which consuming an exact `ReadyPlanWitnessIngressSupply` creates the fresh
target `WitnessIngress` and its causal capability. Persistence, serialization,
network or storage transport, decoding, and physical supplier provenance stay
with Realization and cannot be inferred from equal bytes or semantic values.

No correspondence result establishes:

- truth, satisfiability, or adequate modeling of a relation definition;
- relation satisfaction, witness possession, or witness validity;
- correctness, completeness, termination, or fidelity of a Prover Plan;
- equivalence between relation satisfaction and Protocol acceptance;
- relation refinement, witness evolution, reduction soundness, completeness,
  fold preservation, any handoff other than the exact direct same-process
  operation above, recurrence beyond one selected pair, IVC induction,
  security, knowledge, zero knowledge, or Fiat--Shamir theorem applicability;
- artifact provenance beyond the exact issued interpretation source;
- OIR validity, endpoint support, realization, or implementation
  correspondence; or
- compatibility with another semantic regime.

Those require separately owned admitted subjects and qualified judgments.
