# Protocol correspondence for relations

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-B target
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
- Protocol structure, execution, replay, and the public-only
  `RelationRunView` from
  [Interactive Core and Causal Execution](../pir/interactive-core.md);
- external Interface and source-ID-free `PlanWitnessSurface` meaning from
  [Protocol Interfaces and Prover Plans](../pir/interfaces-and-plans.md); and
- relation Interfaces, instances, split Protocol/Plan bindings, value bridges,
  artifact observations, grounding equations, and commitment slots from
  [Relation Model](relation-model.md).

This page does not own relation satisfaction, Protocol execution, Plan
realization, property Analysis, OIR projection, or realization. A raw carrier
path, label, digest, record, external container, or caller-created tuple is
never a correspondence source.

The K3-B Relations language selects the companion page's standalone
`RelationsProfileId`. It imports exactly
`{PIRInterfacePlanProfileId}` and therefore reaches the two K2 PIR profiles
only through that transitive edge. Its supported subject-kind catalog is the
closed `RelationsId` subject set owned by the companion Relation Model plus
`"relations.correspondence-question"`, `"relations.source-binding-payload"`,
`"relations.source-capability-requirement"`, `"relations.source-consumer"`,
`"relations.source-no-policy"`, `"relations.source-policy-closure"`, and
`"relations.source-purpose"`. Its inline declaration catalogs contain
the exact Relations bodies, correspondence-question algebra, complete read
vocabulary, owner-view schemas, closure and field-expansion laws, and checked
correspondence result schema, plus the Relations-local source-binding payload,
no-policy, policy-closure, typed consumer/purpose, and capability-requirement
subject kinds. Analysis, OIR, realization, theorem, and evidence
profiles are absent. A consumer authenticates the exact no-extra four-profile
closure; it cannot supply a shadow PIR profile, flatten imports into module
roots, or add a consumer-authored declaration catalog.
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

`RelationBoundValue` obtains its expectation only from the exact relation
instance endpoint and admitted edge `ValueRelation`. `ExpectedValue` carries
one canonical value of the selector-derived type and uses exact K1 equality;
it has no relation-derived expectation. The two expected-meta constructors are
closed because K2 already owns their finite result types. There is deliberately
no generic expected-meta arm for `RelationClaimHistory` or
`RelationReductionHistory`: K3-B can ask only whether such a history coordinate
is `Available`, `Inactive`, or `NotReached`. Exact history predicates require a
separately admitted grammar and are unsupported here rather than being guessed
from a binding.

`Presence` compares only the outer PIR observation alternative and never
claims equality of an available payload. `RequireInactive` forms only for a
coordinate that PIR classifies as occurrence-produced; other impossible
status/coordinate combinations are malformed. Across all arms, two checks
that derive the same PIR coordinate are malformed, even if their surface
selectors differ.

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

Every `RunGrounding` contains at least one `RelationBoundValue` check. This
makes its `instance_id` and `binding_id` semantically necessary rather than
identity-bearing context for an unrelated run assertion. Each such check's
edge belongs to that binding and its relation endpoint belongs to the exact
instance Interface. Other checks may provide explicit public expectations or
presence facts in the same binding's Protocol. A standalone run-monitoring
question with no relation-bound value is outside this page's algebra.

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

CorrespondenceReadManifest = {
  protocol: CanonicalSortedUniqueSeq<ProtocolStaticRead>,
  protocol_interface: CanonicalSortedUniqueSeq<ProtocolInterfaceRead>,
  plan_surface: CanonicalSortedUniqueSeq<PlanSurfaceRead>,
  relations: CanonicalSortedUniqueSeq<RelationsRead>,
  run: FiniteSeq<CorrespondenceRunRead>
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
| `RunGrounding` | the binding edge for every `RelationBoundRunValueSelector` appearing in any check; the instance field selected only by each `RelationBoundValue` check; when the owner-derived `RunGroundedPotentialLossyCoordinates(q)` is nonempty, the premise and consumer-source join for every coordinate in that sequence; plus the unique public `RelationRunCoordinate` derived from every check. Expected values are authenticated question literals, not owner reads. |

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
For `RunGrounding`, each coordinate in its exact owner-derived potential lossy
sequence additionally reads the affirmative occurrence-local source premise and
affirmative consumer-source join bound to that use coordinate. Other structural, coverage,
Plan, and artifact questions do not acquire such a read merely because an edge
names a lossy bridge; K3-B defines no live source-consumer join for them.
Concretely, coordinate `c` adds both `BridgeUsePremise(c)` and
`BridgeUseConsumerSourceJoin(c)` to the Relations submanifest.
The exact full `BridgeUseSet` and `LossyUseSelection` are separately
authenticated Section 9 operation operands; they are not manifest read arms.
Reading one Oracle edge additionally includes the relation access declaration,
K2 Oracle index/answer types, `PublicBinding` publication mode, binding
construction, and publication occurrence. Reading a reduction meaning includes
the exact side-input, challenge, and `(publication,next_challenge)` ordinal
maps; it does not read a refinement theorem or output-agreement proof.

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
  exact Interface admission/source binding and matching fresh capability)
    -> CorrespondenceOwnerViewIssueOutcome<ProtocolInterfaceCorrespondenceView>

IssuePlanSurfaceCorrespondenceView(
  exact PlanWitnessSurface,
  exact checked extraction binding and matching fresh extraction capability,
  exact Plan-surface submanifest)
    -> CorrespondenceOwnerViewIssueOutcome<PlanSurfaceCorrespondenceView>

IssueRelationsCorrespondenceView(
  every and only exact admitted Relations operand named by the submanifest,
  every exact admitted/check-result source binding and matching capability,
  exact Relations submanifest)
    -> CorrespondenceOwnerViewIssueOutcome<RelationsCorrespondenceView>

CorrespondenceOwnerViewIssueOutcome<V> =
    Affirmative({
      view: V,
      exact_owner_view_authority_binding: OwnerLocalSourceAuthorityBinding,
      fresh_owner_view_capability
    })
  | CannotAnswer | Unsupported | Refused | Malformed
  | DeterministicLimitExceeded | CheckerFailure
```

Every owner independently rederives its required closure and source values.
Requested reads, realized reads, returned entries, and the appropriate
canonical submanifest must agree exactly. A missing required entry or source
capability is `CannotAnswer`; an unsupported owner constructor is
`Unsupported`; a wrong subject, stale capability, or unauthenticated source is
`Refused`; an extra, duplicate, aliased, reordered, unconsumed, or ill-formed
entry is `Malformed`. None is Negative, and no partial carrier or binding is
returned.

For `IssueRelationsCorrespondenceView`, the identity set of supplied Relations
operands equals the identity set requested by the Relations submanifest. A
missing requested transform is `CannotAnswer`; an unrequested extra transform
is `Malformed` even when every returned entry happens to ignore it. The live
capability retains exactly that equal source set, never a larger ambient owner
environment.

Each static owner binding specializes K1
`OwnerLocalSourceAuthorityBinding`. The PIR Interface binding has owner `"pir"`
and family `"interface-correspondence-view"`; the Relations binding has owner
`"relations"` and family `"relations-correspondence-view"`. In both cases the local coordinate is
the exact issued view object. The domain-profiled binding payload names the
complete source and closed submanifest, while an explicit no-policy declaration,
policy closure, and `OwnerCapabilityRequirement` bind the exact typed consumer
and purpose. The fresh capability retains that identical envelope object plus
the admitted handles, submanifest, realized reads, evaluator, and issuance
occurrence. Local bindings, capabilities, and issued aggregates are
noncopyable and nonserializable. Passing the identical capability object is the
only bearer delegation; reconstructed, cross-owner, cross-family, or
cross-purpose substitutes grant no source authority.

Consumer and purpose intake follows the same open downstream-coordinate,
closed owner-role rule as PIR. Each may be any exact same-regime downstream
`TypedContentId`; Relations wraps it under `RelationsProfileId` as a distinct
`relations.source-consumer` or `relations.source-purpose` identity over
`(family,ContentRef(coordinate))`. The payload and owner requirement use those
nominal role IDs, while the live capability retains and exactly compares the
original coordinates. Relations therefore imports no downstream vocabulary,
and consumer/purpose or cross-family substitution changes authority.

The invocation-issued `PublicSetupInvocationView` is the only portable
source-view exception in this cut: its inert
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
proposition exists and never yields Negative.

Endpoint type, selector type, and expected-value type mismatches make question
formation malformed; they cannot produce an admitted proposition and therefore
have no disagreement constructor.

Only completed affirmative or negative results receive the ordinary exact
question-, operand-, consumer-, and purpose-bound checked-result binding and a
fresh live capability. IDs, serialized records, manifests, and source bindings
are inert and grant no authority.

## 6. Structural and coverage operations

All named operations below are specializations of:

```text
CheckCorrespondence(
  admitted CorrespondenceQuestion,
  every exact admitted operand named by the question,
  exact CorrespondenceOwnerViewSet for ManifestFor(question),
  exact RelationRunView sequence for its run submanifest,
  every matching live owner-view and run-view capability,
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
selected public, Oracle-binding, or phase path. An Oracle path additionally
requires the exact K2 `PublicBinding` publication mode, compatible relation/K2
index and answer types, admitted binding construction, public publication
occurrence, and matching public transport entry. A phase path names its exact
challenge or public occurrence and transport entry. Repeated equal values are
checked at distinct coordinates.

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

## 9. Public run-grounded operation

```text
CheckRunGroundedCorrespondence(
  admitted RunGrounding q,
  exact admitted RelationInstance,
  exact admitted ProtocolRelationBinding,
  PIR-issued public-only RelationRunView,
  matching fresh run-view authority,
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

The run view's Protocol and qualification must match the question. Its
issuance authority must retain the exact invocation and source binding required
by the operation. Its payload contains every and only the public coordinates
in `ManifestFor(question)`; the full `CompletedProtocolRecord` remains in
PIR's private source binding and is not a correspondence read.

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

For `ExpectedValue`, an `Available` payload is compared with the question's
exact typed canonical value using K1 equality. `ExpectedCheckResult` and
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
K3-B. A different repeated occurrence, inactive guarded occurrence, or
unreached boundary is Negative only when an admitted check selected a different
status or expectation. A missing manifest entry or caller-created value is
respectively `CannotAnswer` or `Refused`.

`ExactReplayQualified` requires a `ReplayQualified` view and answers what exact
K2 replay consumed. `ExactCausallyGenerated` requires a `CausallyGenerated`
view and the still-live K2 causal capability; replay cannot mint it. Neither
qualification proves relation satisfaction, honest strategy, coin
distribution, or implementation isolation.

No private witness, Oracle material, verifier-private query or answer, Plan
state, advice, randomness, or strategy-local value is readable here. A later
private supply-occurrence question requires a distinct PIR owner view and new
question variant; until then it is `Unsupported`.

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
results.

No correspondence result establishes:

- truth, satisfiability, or adequate modeling of a relation definition;
- relation satisfaction, witness possession, or witness validity;
- correctness, completeness, termination, or fidelity of a Prover Plan;
- equivalence between relation satisfaction and Protocol acceptance;
- relation refinement, witness evolution, reduction soundness, completeness,
  security, knowledge, zero knowledge, or Fiat--Shamir theorem applicability;
- artifact provenance beyond the exact issued interpretation source;
- OIR validity, endpoint support, realization, or implementation
  correspondence; or
- compatibility with another semantic regime.

Those require separately owned admitted subjects and qualified judgments.
