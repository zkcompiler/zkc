# Analysis Named-Premise Intake

> **State:** `Affirmative/API-A-FINITE-PREMISE-INTAKE` for the bounded
> proposal model; owner partition publication remains `CannotAnswer`
> **Authority:** None. This note proposes owner text but changes no Analysis or
> PIR owner page, profile, identity, theorem, or property.
> **Executable evidence:**
> [`evaluation/analysis-premise-intake-probe`](../../../../evaluation/analysis-premise-intake-probe/README.md)

## 1. Question and answer

This lane asks one exact question:

> Can a closed Analysis-owned named-premise catalog and intake operation make
> every required assumption explicit and identity-bearing for the finite
> Schnorr subject while failing closed on omission or coordinate substitution?

The bounded proposal answers yes. Two independent finite evaluators agree on
ten premise bodies, their identities, four complete intakes, seven
single-premise omissions, one wrong-coordinate substitution, and two distinct
provider-map judgments. The aggregate is
`Affirmative/API-A-FINITE-PREMISE-INTAKE`.

One owner dependency remains unavailable at this branch cutoff. The current
PIR page lists generated-run branches and qualified noncompletion in
`interactive-core.md` Section 12.3 lines 1688--1710, but it does not publish a
closed `ProtocolOutcomeLane` coordinate or profile-qualified partition. The
probe therefore uses a proposal-local symbolic coordinate and retains
`CannotAnswer/API-C-OUTCOME-PARTITION-UNPUBLISHED`. No owner fact is inferred
from the decision input.

## 2. What the current Analysis target lacks

The current pages already have the necessary surrounding calculus: exact
question/goal/proposition identities, hypothesis DAGs, semantic basis,
support, validation, qualified outcomes, and judgment identities. The missing
pieces are narrower and exact:

1. `analysis-model.md` Section 4.1 lines 2082--2115 has no first-class named
   premise body, no requirement slots on `AnalysisQuestionBody`, no bindings
   on `AnalysisGoalBody`, and no premise-ID projection in hypothesis nodes or
   contexts.
2. `analysis-model.md` Section 4.1 lines 2246--2261 admits only hypothesis-node,
   affirmative-judgment-capability, and quantified-witness requirements.
   There is no `NamedPremiseRequirement` variant.
3. `analysis-model.md` Section 4.1 lines 2725--2758 has generic premise schemas
   and support maps, but no exact named-premise binding case and no law that
   compares the support map with the premises named by the goal and inherited
   hypothesis context.
4. `analysis-model.md` Section 4.1 lines 2773--2786 makes the proposition,
   inherited hypothesis context, semantic basis, support, validation, and
   policy identity-bearing, but does not expose the exact premise-ID set in the
   judgment body.
5. `analysis-model.md` Section 3 lines 1696--1742 has no
   `analysis.named-premise` body-dispatch case. Section 6 lines 3686--3706
   already has the required `CannotAnswer(missing ... premise ...)` outcome,
   but no intake operation selects it for a missing named slot.
6. `cryptographic-properties.md` Section 3 lines 479--515 defines the finite
   challenge model. Lines 542--560 say an ordinary hypothesis must relate the
   nominal domain and Fresh-law projections to that model, but no record binds
   an exact `pir.public-coin-law` declaration coordinate, model, and hypothesis
   by name.
7. `cryptographic-properties.md` Section 7 lines 4863--4937 has Fresh
   distribution, exact classical random-oracle-process, and sampler-adequacy
   goals in a hypothesis DAG. It has no family-indexed premise catalog, source
   field, evidence depth, or regime-transport field, and its sampler goal
   combines Fresh and Fiat--Shamir interfaces rather than recording the
   challenge-source distinction at intake.
8. `semantic-relations.md` Section 3 lines 99--175 can import the full relation
   model, interface, Protocol relation binding, and Plan witness binding. It
   does not select the five exact fields needed here as named property-premise
   coordinates, and it has no ProverPlan state or recipe source slots.
9. No Analysis page defines a provider-specific total carrier map over a
   PIR-owned Protocol outcome partition. The phrase `ProtocolOutcomeLane` is
   absent from all current Analysis owner pages and profile manifests.
10. `profile-publication.md` Sections 2--4 and the kernel,
    cryptographic-property, and semantic-transport manifests have no named-
    premise publication law or `analysis.named-premise` supported kind. The
    property and transport manifests therefore cannot currently form the
    concrete premise bodies proposed below.

No addition belongs to `transport-composition-and-replay.md`,
`incremental-composition.md`, or either source-validation profile. Those pages
may consume a premise-bearing judgment through their existing typed imports,
but they should not restate the premise catalog or become premise authorities.

## 3. Selected ownership

The proposal uses the existing profile topology:

```text
common Analysis kernel
  owns the closed premise grammar, identity rule, and intake operation

cryptographic-property profile
  owns concrete Fresh distribution premises
  owns provider outcome-carrier maps for concrete Protocol partitions
  owns the five concrete Schnorr relation and Plan premise coordinates

semantic-transport profile
  owns per-family Fiat--Shamir sampler-adequacy premises
  owns per-family Fiat--Shamir oracle-process premises
```

The common kernel does not acquire a provider, family, or PIR fact. It defines
only the typed grammar and total intake law. Concrete premise bodies are formed
under the existing child profile whose authenticated import closure can name
their owner coordinates. The property profile does not define the PIR outcome
partition; it maps an exact PIR-owned partition into one provider carrier.
The transport profile does not turn a random-oracle or sampler hypothesis into
truth.

The five exact Schnorr coordinates remain bound to the selected Fresh Protocol
candidate. Their transport field is `RebindRequired`; this proposal does not
reuse the Fresh-bound Plan as a Fiat--Shamir Plan. The Fresh/Fiat--Shamir
same-Core comparison in the executable concerns challenge intake only.

## 4. Proposed delta

Nothing in this section has been applied. It is exact proposed owner text for
owner review.

### 4.1 `docs-next/analysis/analysis-model.md`, Section 4.1

**Exact change.** Insert the following closed grammar immediately before
`AnalysisQuestionBody`:

```text
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
  | PIRProtocolOutcomePartitionCoordinate(
      ProtocolId,ProtocolOutcomeLane)
  | RelationsModelEvaluatorCoordinate(RelationSemanticModelId)
  | RelationsWitnessPlanJoinCoordinate(
      RelationInterfaceId,PrivateWitnessOrdinal,
      PlanWitnessBindingId,WitnessEdgeOrdinal)
  | PIRPlanStateCoordinate(
      ProverPlanId,PersistentStateOrdinal,PlanExecutionStateOrdinal)
  | PIRPlanRecipeCoordinate(
      ProverPlanId,DecisionOrdinal,RecipeNodeOrdinal,
      PlanStrategyStepCoordinate)

AnalysisNamedPremiseBoundValue<K> =
    BoundModel(TypedSemanticSubjectRef,
               AnalysisLawTerm<ExactModelBindingLaw<K>>)
  | BoundHypothesis(AnalysisLawTerm<ExactNamedHypothesis<K>>)
  | BoundProviderOutcomeCarrierMap(
      AnalysisProviderOutcomeCarrierMapBody)

AnalysisNamedPremiseSource =
    OwnerSemanticCoordinate(TypedSemanticSubjectRef)
  | CandidateOwnerCoordinate(TypedSemanticSubjectRef)
  | FamilyHypothesisSource(AnalysisFamilyCoordinate)
  | ProviderDeclarationSource(
      AnalysisProfileDeclarationRef<"analysis.provider-declaration">)

AnalysisPremiseEvidenceDepth = T1 | T2 | T3

AnalysisPremiseRegimeTransport =
    ExactRegimeOnly(SemanticRegimeId)
  | ExactCoordinateOnly(
      CanonicalNonEmptySortedUniqueSeq<SemanticRegimeId>)
  | RebindRequired(
      CanonicalNonEmptySortedUniqueSeq<SemanticRegimeId>)

AnalysisProviderOutcomeCarrierMapBody = {
  provider_declaration:
    AnalysisProfileDeclarationRef<"analysis.provider-declaration">,
  protocol_outcome_partition:
    PIRProtocolOutcomePartitionCoordinate,
  provider_carrier: AnalysisProfileLawRef<ClosedProviderCarrier>,
  total_lane_map:
    CanonicalMap<ProtocolOutcomeLane,
                 CanonicalValue<provider_carrier>>
}

AnalysisNamedPremiseBody<K> = {
  kind: exactly K,
  coordinate: AnalysisPremiseCoordinate admitted for K,
  bound_model_or_hypothesis: AnalysisNamedPremiseBoundValue<K>,
  source: AnalysisNamedPremiseSource admitted for K,
  evidence_depth: AnalysisPremiseEvidenceDepth,
  regime_transport: AnalysisPremiseRegimeTransport
}

AnalysisNamedPremiseId<P,K> =
  AnalysisId<"analysis.named-premise",P>(
    B,AnalysisNamedPremiseBody<K>)

AnalysisNamedPremiseRequirement = {
  slot: ExactAsciiSymbol,
  kind: AnalysisNamedPremiseKind,
  coordinate: AnalysisPremiseCoordinate admitted for kind
}
```

The kind-to-coordinate, kind-to-bound-value, and kind-to-source relations are
closed profile laws. An unknown case is `Unsupported`; a malformed field or
disallowed pairing is `Malformed`. `T1`, `T2`, and `T3` retain the existing
research meanings: source-grounded boundary mapping, complete typed
constructive binding, and frozen executable falsification. Evidence depth
records what evidence accompanies the premise identity; it never changes an
assumption into an established proposition.

Replace the question, goal, hypothesis-node, hypothesis-context, premise-
requirement, premise-binding, support, and judgment displays by these additive
fields and variants:

```text
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
    CanonicalMap<AnalysisNamedPremiseRequirement,
                 AnalysisNamedPremiseId>
}

AnalysisHypothesisNode = {
  local_ordinal,
  goal_id: AnalysisGoalId,
  dependency_ordinals: CanonicalSortedUniqueSeq<EarlierLocalOrdinal>,
  exact_named_premise_ids:
    exactly PremiseIdsOfGoal(goal_id)
}

AnalysisHypothesisContextBody = {
  nodes: CanonicalSeq<AnalysisHypothesisNode>,
  roots: CanonicalSortedUniqueSeq<LocalOrdinal>,
  exact_named_premise_ids:
    CanonicalSortedUniqueUnion(
      every node.exact_named_premise_ids reachable from roots)
}

AnalysisPremiseRequirement =
    NamedPremiseRequirement(AnalysisNamedPremiseRequirement)
  | HypothesisNodeRequirement { ... }
  | AffirmativeJudgmentCapabilityRequirement { ... }
  | ExactQuantifiedWitnessRequirement { ... }

ExactPremiseBinding =
    ExactNamedPremiseBinding(AnalysisNamedPremiseId)
  | PortableAffirmativeJudgmentBinding(...)
  | OwnerLocalAffirmativeJudgmentBinding(...)
  | ExactQuantifiedWitnessBinding(...)

AnalysisSupportInstantiationBody = {
  semantic_basis_id: AnalysisSemanticBasisId,
  proposition_id: AnalysisPropositionId,
  non_hypothesis_premise_bindings:
    CanonicalMap<AnalysisPremiseRequirement,ExactPremiseBinding>,
  exact_named_premise_ids:
    exactly PremiseIdsOfProposition(proposition_id),
  established_hypothesis_node_bindings: ...,
  assumed_hypothesis_node_bindings: ...,
  source_support_bindings: ...
}

AnalysisJudgmentRecordBody = {
  proposition_id: AnalysisPropositionId,
  polarity: AnalysisPolarity,
  exact_family_conclusion: ExactFamilyConclusion<GoalFamily>,
  inherited_hypothesis_context_id: AnalysisHypothesisContextId,
  exact_named_premise_ids:
    exactly PremiseIdsOfProposition(proposition_id),
  typed_quantitative_result: ExactFamilyQuantitativeResult<GoalFamily>,
  semantic_basis_id: AnalysisSemanticBasisId,
  support_coordinate: AnalysisSupportInstantiationCoordinate,
  validation_basis_id: AnalysisValidationBasisId,
  qualification: AnalysisQualificationCoordinate,
  operation_policy_id: AnalysisOperationPolicyId,
  derived_source_policy_dependency_closure:
    CanonicalSortedUniqueSeq<TypedContentId>
}
```

Add this total intake operation after the ID constructors:

```text
IntakeAnalysisNamedPremises(
    exact question,
    supplied: CanonicalMap<AnalysisNamedPremiseRequirement,
                           AnalysisNamedPremiseId>) =
  1. authenticate the question and every supplied premise under the question's
     exact direct Analysis profile;
  2. derive the required key set from
     question.named_premise_requirements;
  3. return CannotAnswer for any missing key or absent named premise source;
  4. return Refused when a supplied premise is well formed but its kind or
     coordinate differs from the requirement at that slot;
  5. return Malformed for an extra, duplicate, noncanonical, or caller-ordered
     key;
  6. require every premise's regime_transport to admit the question's exact
     regime without inference; RebindRequired never transports a premise;
  7. form exactly one AnalysisGoalBody whose binding map has the required key
     set and no other key; and
  8. expose the canonical sorted premise-ID projection to every hypothesis
     node, hypothesis context, support instantiation, and judgment that uses
     that goal.
```

Extend `ExactNonHypothesisPremiseBindingMap` so its derived key set includes
every `NamedPremiseRequirement`, and add
`"analysis.named-premise" -> AnalysisNamedPremiseBody` to the active body
dispatch. The property or transport profile selected by the concrete body,
not the kernel alone, owns admission of that body.

**Identity effect.** A named-premise body changes identity when any of kind,
coordinate, bound model/hypothesis, source, evidence depth, or regime transport
changes. A goal includes exact premise IDs; hypothesis contexts, propositions,
supports, and judgments therefore rotate when the premise selection changes,
even if their Core and top-level property subject are unchanged. Adding the
common grammar changes the marked kernel law source and rotates the kernel and
all six profiles in its import closure on adoption. Existing question, goal,
context, proposition, support, and judgment bodies require explicit migration;
there is no default empty field except for constructors whose profile law fixes
the unique empty requirement sequence.

**Evidence.** `API-A-CLOSED-SCHEMA`, `API-A-COMPLETE-INTAKE`,
`API-A-HYPOTHESIS-SET`, `API-C-MISSING-PREMISE`, and
`API-R-PREMISE-COORDINATE`.

**Reversal condition.** Reject this delta if owner review finds that the
existing goal and support identities can name the same six premise fields,
enforce total slot coverage, and distinguish alternate bindings without a new
body kind. Any replacement must reproduce the omission and coordinate-
substitution controls and retain visible premise IDs in every consuming
hypothesis set.

**Nonclaims.** This grammar does not establish a premise, theorem, property,
provider correspondence, or owner adoption.

### 4.2 `docs-next/analysis/cryptographic-properties.md`, Sections 3 and 7

**Exact change.** Add the following catalog constructors under the
cryptographic-property and semantic-transport marked fragments:

```text
FreshPublicCoinDistributionPremise(
    law_coordinate:ProtocolDeclarationRef<"pir.public-coin-law">,
    distribution_model:AnalysisDistributionProfileId,
    sampling_hypothesis:AnalysisLawTerm<ExactFreshSamplingHypothesis>,
    source:AnalysisNamedPremiseSource,
    evidence_depth:AnalysisPremiseEvidenceDepth) =
  AnalysisNamedPremiseBody<FreshPublicCoinDistribution> {
    coordinate: PIRPublicCoinLawCoordinate(law_coordinate),
    bound_model_or_hypothesis:
      BoundHypothesis(sampling_hypothesis binding law_coordinate exactly to
                      distribution_model),
    source,
    evidence_depth,
    regime_transport: ExactRegimeOnly(FreshRegimeId)
  }

FiatShamirFamilySamplerPremise(F,model,hypothesis,source,depth) =
  AnalysisNamedPremiseBody<FiatShamirSamplerAdequacy> {
    coordinate: AnalysisFamilyPremiseCoordinate(F,SamplerAdequacy),
    bound_model_or_hypothesis:
      BoundHypothesis(hypothesis naming the exact adequacy form, including the
                      exhaustion term or exact-total case),
    source,
    evidence_depth: depth,
    regime_transport:
      ExactRegimeOnly(ClassicalRandomOracleRegimeId)
  }

FiatShamirFamilyOracleProcessPremise(F,model,hypothesis,source,depth) =
  AnalysisNamedPremiseBody<FiatShamirOracleProcess> {
    coordinate: AnalysisFamilyPremiseCoordinate(F,OracleProcess),
    bound_model_or_hypothesis: BoundHypothesis(hypothesis),
    source,
    evidence_depth: depth,
    regime_transport:
      ExactRegimeOnly(ClassicalRandomOracleRegimeId)
  }

ProviderOutcomeCarrierPremise(P,provider,carrier,total_map,source,depth) =
  AnalysisNamedPremiseBody<ProviderOutcomeCarrierMap> {
    coordinate:
      PIRProtocolOutcomePartitionCoordinate(P,ProtocolOutcomeLane),
    bound_model_or_hypothesis:
      BoundProviderOutcomeCarrierMap {
        provider_declaration: provider,
        protocol_outcome_partition:
          PIRProtocolOutcomePartitionCoordinate(P,ProtocolOutcomeLane),
        provider_carrier: carrier,
        total_lane_map: total_map
      },
    source,
    evidence_depth: depth,
    regime_transport: ExactCoordinateOnly([RegimeOf(P)])
  }
```

Formation requires exactly one Fresh distribution premise for every
`pir.public-coin-law` coordinate selected by a question. A Fiat--Shamir
challenge selects no Fresh-law premise. It requires the sampler-adequacy and
oracle-process entries for its exact family. Classical random-oracle,
quantum-random-oracle, and concrete primitive/process regimes require distinct
premise bodies and transport declarations; no family or spelling match
transports them.

`ProviderOutcomeCarrierPremise` requires `total_map` to have exactly the
profile-qualified PIR partition of `P` as its domain. A Fresh Protocol has the
five selected lanes `Accepted`, `Rejected`, `Aborted`, `StrategyStopped`, and
`OperationalNoncompletion`; `InterpretationFailed` appears only when the PIR
profile publishes an interpretation-failure schema. Missing provider images
are `CannotAnswer`, not collapse to `false`, `None`, or `Rejected`.

Add these exact property-profile entries for the current finite Schnorr
subject:

| Kind | Exact coordinate | Bound model or hypothesis | Source depth | Transport |
|---|---|---|---|---|
| Fresh public-coin distribution | semantic module `zkcidv0:foundation.semantic-module:de7f837dc849ff52fb045259839dfb9efde015a65781ad064feb5a91b0ae29b7`, `pir.public-coin-law` declaration ordinal 0 | fresh uniform draw on the finite additive three-element challenge model, independent of prior prover view | `T1` | exact Fresh only |
| provider outcome carrier | selected Fresh Protocol's exact PIR outcome partition | total provider map into `Option[Bool]` or another exact provider carrier | `T1` | exact Protocol/partition only |
| relation predicate | `RelationSemanticModel(...).evaluator` | `Y = x . G` in additive `Z/3Z`, `G=1` | `T3` coordinate evidence | rebind for another Protocol/regime |
| witness type | `RelationInterface(...).private_witness[0]` joined by `PlanWitnessBinding.witness_edges[0]` | `x : Z3` at witness ingress `x` | `T3` coordinate evidence | rebind for another Protocol/regime |
| Prover private state | `ProverPlan(...).persistent_state[0] -> PlanExecutionState[0]` | nonce `r : Z3` | `T3` coordinate evidence | rebind for another Protocol/regime |
| honest commit | decision-zero recipe node zero into `PlanStrategyStep(0)` | provider operation corresponds to `A := r` | `T3` coordinate evidence | rebind for another Protocol/regime |
| honest respond | decision-two recipe node zero into `PlanStrategyStep(2)` | provider operation corresponds to `z := r+c*x mod 3` | `T3` coordinate evidence | rebind for another Protocol/regime |

Add exactly two semantic-transport-profile entries per admitted family:

| Kind | Family coordinate | Required content | Initial depth | Transport |
|---|---|---|---|---|
| Fiat--Shamir sampler adequacy | `AnalysisFamilyPremiseCoordinate(F,SamplerAdequacy)` | one named adequacy form with exhaustion explicit | `T1` for the selected candidate | exact classical-random-oracle regime only |
| Fiat--Shamir oracle process | `AnalysisFamilyPremiseCoordinate(F,OracleProcess)` | complete adaptive query/answer process hypothesis | `T1` for the selected candidate | exact classical-random-oracle regime only |

The `T3` labels above concern reproducible finite coordinate selection and
mutation evidence. They do not establish relation truth, algorithm honesty, or
provider correspondence. The current Schnorr Plan is Fresh-Protocol-bound, so
the proposal deliberately does not form a complete Fiat--Shamir property
judgment from those five entries.

**Identity effect.** Every public-coin-law coordinate and family receives a
separate premise ID. Two provider maps over the same exact PIR partition differ
in `bound_model_or_hypothesis` and therefore produce distinct premise, goal,
proposition, support, and judgment identities. Fresh and Fiat--Shamir questions
over one Core name disjoint challenge-premise sets.

**Evidence.** `API-A-CATALOG`, `API-A-REGIME-SEPARATION`,
`API-A-PROVIDER-MAP-IDENTITY`, and
`API-C-OUTCOME-PARTITION-UNPUBLISHED`.

**Reversal condition.** Remove or revise an entry if its owner coordinate is
not published, its exact source model is replaced, the property owner selects
a different premise kind, or a regime-specific proof requires a narrower
transport rule. The provider-map entry cannot become owner-authenticated until
PIR publishes the exact partition coordinate.

**Nonclaims.** The entries are proposed assumptions and maps. They establish
no distribution, sampler adequacy, oracle process, relation, honest strategy,
theorem applicability, completeness, security, or provider implementation
correspondence.

### 4.3 `docs-next/analysis/profile-publication.md` and profile manifests

**Exact change.** In Section 2, add “named-premise grammar and total intake” to
the common kernel's owned calculus. Do not add provider or family declarations
to the kernel supported-kind list. In Section 3, add
`analysis.named-premise` to
`AnalysisCryptographicPropertySupportedKinds` and state that the profile owns
Fresh-law, concrete provider-map, and concrete relation/Plan premise bodies. In
Section 4, add `analysis.named-premise` to
`AnalysisAFKTransportSupportedKinds` and state that the profile owns family
sampler-adequacy and oracle-process premise bodies.

Apply the same literal supported-kind additions and one exact subject row in:

- `docs-next/analysis/profiles/cryptographic-property.json`; and
- `docs-next/analysis/profiles/afk-transport.json`.

The kernel manifest retains its current supported subject kind. Its marked
common semantic-law fragment changes because it defines the shared grammar and
intake law. The source-validation children add no local premise kind; their
imported profile identities rotate transitively. The incremental-composition
branch also rotates through the common-kernel change but gains no local
premise catalog in this delta.

**Identity effect.** Adoption rotates the common kernel profile and its full
six-profile import closure. The property and transport supported-kind catalogs
also rotate directly. The publication table must be reconstructed from the
adopted owner bytes; no identity in this note is publishable.

**Evidence.** `API-A-CLOSED-SCHEMA` and
`API-A-INDEPENDENT-RECONSTRUCTION`.

**Reversal condition.** If publication reconstruction shows that the common
law cannot remain owner-neutral, move the grammar into the property profile
and accept the loss of reuse rather than adding imports from the kernel to PIR,
Relations, or a provider. Never introduce a new top-level premise authority to
avoid an import-closure rotation.

**Nonclaims.** This is a profile-delta proposal, not an adopted manifest edit,
published identity, compatibility result, or migration authorization.

## 5. Executable result

The finite catalog has ten entries of nine kinds: five at `T1`, none at `T2`,
and five at `T3`. The complete Fresh Schnorr intake names seven premises. Each
single deletion returns `CannotAnswer/API-C-MISSING-PREMISE`; a declaration-
ordinal substitution returns `Refused/API-R-PREMISE-COORDINATE`.

The challenge-only Fresh intake names the public-coin distribution premise.
The challenge-only Fiat--Shamir intake over the same Core instead names the
family sampler-adequacy and oracle-process premises. Their premise-ID sets are
disjoint. Two total provider maps over the same five-lane Fresh partition yield
distinct judgment IDs. Both evaluator paths agree on the complete projection
before comparison with the frozen expected findings.

## 6. Nonclaims

This result is a bounded executable design probe. It is not a mechanized proof,
does not establish any premise or property, does not validate a theorem or
provider, does not authenticate the proposal-local outcome-partition
coordinate, does not transport Fresh premises into Fiat--Shamir, and does not
adopt or publish owner text or profile identities.

## Handoff

### Files changed

- Added `evaluation/analysis-premise-intake-probe/README.md`, `fixture.json`,
  `model.py`, `independent.py`, `run.py`, and `expected-findings.json`.
- Added this proposal note.
- Registered `research.analysis-premise-intake` in `checks/manifest.json`, the
  `retained-bounded-instruments` lifecycle group, and `evaluation/README.md`.
- Moved the lifecycle count pins in
  `checks/tests/test_evaluation_lifecycle.py` from 53 to 54 research checks,
  55 to 56 packages, and 15 to 16 retained packages.
- No Analysis, PIR, Foundation, or Relations owner page or profile was edited.

### Commands and outcomes

All repository checks below used the clone-local alternate index and object
store; the real `.git` index remained untouched.

- Alternate-index inventory setup and lock-artifact correction: exit 0, 0.6 s
  total.
- `python3 -B evaluation/analysis-premise-intake-probe/run.py --check`: exit 0,
  0.03 s.
- `python3 -B checks/run.py validate`: exit 0, 0.04 s; 71 checks and six tiers
  validated.
- `UV_NO_SYNC=1 UV_OFFLINE=1 UV_CACHE_DIR=$PWD/.uv-cache python3 -B
  checks/run.py run --tier developer`: exit 0, 1.07 s; all eight checks
  passed, including lifecycle inventory.
- `python3 -B checks/run.py run --check
  research.analysis-premise-intake`: exit 0, 0.10 s; the registered check
  passed.
- JSON parsing, forbidden-shorthand scan, staged whitespace check, and exact
  staged-name/stat audit: exit 0, 0.2 s.

### Aggregate outcome

The frozen package aggregate is
`Affirmative/API-A-FINITE-PREMISE-INTAKE`, with findings digest
`a91f91a093e162d1859a0b412ca4552364d38b484d7d1cc8b89eff4d777ed4b4`.
This establishes only the bounded proposal's schema closure, exact intake
behavior, independent reconstruction agreement, and named mutation controls.

### Nonclaims

No theorem or cryptographic property is established. No provider
implementation is validated. No premise is proved, no cross-regime transport
is justified, and no owner text, owner identity, or profile is adopted or
published.

### Surprises and where the brief was wrong

- During probe development, two transient report snapshots were accidentally
  written under `/tmp`, outside the requested clone-only scope. Both were
  deleted before alternate-index validation; no external report artifact
  remains. This was a lane-procedure deviation, not a change to the result.
- The current branch does not publish the named `ProtocolOutcomeLane`
  coordinate that the brief treats as available. It lists outcome branches,
  so the probe uses a visibly proposal-local symbolic coordinate and retains
  `CannotAnswer/API-C-OUTCOME-PARTITION-UNPUBLISHED` rather than deriving an
  owner partition.
- The selected Schnorr Plan coordinates are Fresh-Protocol-bound. The
  same-Core Fresh/Fiat--Shamir result is therefore intentionally a
  challenge-intake comparison, not silent transport of the five property
  premises into a Fiat--Shamir property judgment.
- This dedicated clone has no local `AGENTS.md` or `.claude/CLAUDE.md`; their
  primary-checkout copies were read through the permitted read-only mount.
