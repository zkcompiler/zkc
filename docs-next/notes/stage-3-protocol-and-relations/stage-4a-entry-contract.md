# Stage 4A Analysis-to-Compiler entry contract

> **Document kind:** Temporary Stage 3.5 downstream handoff contract
> **Document state:** Bounded entry contract; no Stage 4A activation
> **Authority:** None. This page does not define an Analysis or Compiler
> judgment, admit a subject, mint a capability, authorize implementation or
> migration, or establish any property or compilation result.
> **Frozen basis:** The [Stage 3 target](target-semantic-model.md) at SHA-256
> `107255938efa6af7802030b93bdbc9dcb4d5535335866cffa304df33083a7f5b`
> and the [Stage 3 convergence record](convergence.md).
> **Successor owners:** [`analysis/`](../../analysis/README.md), followed by
> [`compiler/`](../../compiler/README.md).
> **Peer handoff:** [Stage 4B OIR-to-Realization entry
> contract](stage-4b-entry-contract.md).
> **Disposition:** Replace this page with reviewed durable Analysis and Compiler
> contracts after the entry obligations below are discharged.

## 1. Purpose and order

Stage 4A proceeds in this order:

```text
admitted Stage 3 subjects
  + purpose-specific immutable views and adequacy predicates
  + exact question, model, theorem/rule, assumptions, and parameters
  -> Analysis-owned qualified judgment

admitted predecessor and independently admitted candidate successor
  + exact checked predecessor/successor relation
  + exact Analysis judgments used by declared constraints or objectives
  + complete finite comparison domain
  -> Compiler-owned qualified decision
```

Analysis defines property meaning before Compiler may cite property results in a
constraint or objective. Compiler requirements may expose an insufficient
Analysis envelope and send a concrete read-set counterexample upstream, but
optimization policy, candidate availability, scores, or selection cannot change
the meaning of an Analysis property.

This page fixes only the downstream intake boundary. The separate activation
decision required by the [v0 design program](../../project/v0-design-program.md)
has not been made.

## 2. Frozen Stage 3 intake

Stage 4A begins from process-local authority reconstructed by the Stage 3 owner,
not from an ID, carrier, signature, persisted result, or producer assertion.

| Intake | Minimum authority and scope | Permitted use | Prohibited inference |
|---|---|---|---|
| Protocol or Core facts | Exact `AdmittedProtocol`; an attenuated `AdmittedCoreView` only where challenge interpretation is deliberately outside the question | Read the purpose-specific events, schedule, values, objects, randomness, challenges, claims, checks, failures, terminals, obligations, dependencies, and interpretation facts declared by the question | A Core view cannot assert Fresh/FS interpretation or widen to Protocol authority |
| Interface facts | Exact `AdmittedProtocolInterface` for the same `ProtocolId`, with retained dependency views | Read external names, codecs, statement/proof bindings, application roles, and terminal outcomes only when the question declares them | Interface admission is not relation correspondence, endpoint support, or a property result |
| Plan facts | Exact `AdmittedPlan`; an affirmative exact `CheckedPlanRealizes` over that Plan and its retained `AdmittedProtocol` is additionally required whenever the conclusion depends on structural obligation coverage | Read only the declared Plan fields under a complete read set and adequacy predicate | Plan admission or realization does not establish value correctness, distributional fidelity, termination, completeness, cost, provider behavior, or proof production |
| Relation facts | Exact externally reconstructed `RelationDefinitionRef` when read, exact admitted zkc-owned relation subjects, and each narrow A/N checked capability whose exact question or operation basis and read closure contain every checked field consumed | Use the external definition reference only as an opaque cited input; use exact `AdmittedRelationInterface`, `AdmittedRelationInstance`, `AdmittedRelationBinding`, and other zkc-owned subject facts; consume exact checked comparison, grounding, structural-correspondence, or instance-correspondence results only when the question names them | A definition reference, binding, artifact observation, result shape, or correspondence capability does not establish satisfaction or a cryptographic property |
| Execution facts | The exact invocation tuple `(AdmittedProtocol, CoreInvocationInputs, ProverTrace, RandomnessReplay, ExactProtocolExecutionCapabilities)` together with the `Qualified<CoreExecutionRecord>` returned by that invocation | Analyze that exact invocation tuple, or a later-owned occurrence or model explicitly bound to it | Stage 3 mints no runtime-occurrence subject; one execution is not a universal trace, distribution, completeness, or implementation-correctness theorem |
| FS construction | Admitted Fresh and FS Protocols, exact `AdmittedTranscriptConstruction`, and affirmative exact `CheckedFSConstruction` retaining the construction maps | Form the exact structural premise of `FSCompile` | Equal Core IDs, target admission, maps alone, or a negative FS result cannot serve as an affirmative construction premise |
| Core composition | Exact ordered child `AdmittedCoreView`s derived from independently admitted child Protocols, the independently admitted target `AdmittedProtocol`, exact `AdmittedCoreCompositionSpec`, and affirmative exact `CheckedCoreComposition` retaining `ResolvedCoreCompositionMaps` | Form the exact structural premise of a composition-specific Analysis question | Structural composition establishes no property law, associativity, commutativity, link equivalence, or Fresh/FS commutation |

Every view has a source-owned adequacy predicate stating that it contains every
Stage 3 fact the named Analysis or Compiler question may read. A new read either
extends the declared view through its owner or changes the question; it cannot be
recovered from ambient MLIR state, a registry, a workbench cache, or a universal
fact bundle.

## 3. Analysis entry envelope

Before evaluating a property, Stage 4A must define one closed typed request with
at least:

```text
AnalysisRequest = {
  question_kind,
  property_or_relation_index,
  exact_subject_tuple,
  direction,
  observer_set,
  result_schema,
  admitted_source_views,
  declared_read_set,
  view_adequacy_obligations,
  exact_occurrence_and_subject_maps,
  semantic_model_identity,
  theorem_or_rule_identity,
  explicit_hypotheses_and_assumptions,
  quantitative_parameters_and_bounds,
  analysis_regime,
  checker_or_derivation_basis,
  exact_dependency_closure
}
```

Fields that a particular question does not read are absent, not silently
defaulted. The question fixes whether the relation is symmetric or directed,
which observers and protected effects matter, how termination, refusal, abort,
nonproduction, and divergence are treated, and whether the result is Boolean,
field-factored, quantitative, or conditional.

The exact subject tuple is variant-specific:

- a Protocol-only question cites the exact admitted Protocol and cannot read an
  Interface or Plan;
- an Interface-sensitive question additionally cites the exact admitted
  Interface and its declared view;
- a Plan-sensitive question additionally cites the exact admitted Plan, its
  complete read set, and affirmative `CheckedPlanRealizes` whenever obligation
  coverage enters the conclusion; the full `ProverPlanId` enters the basis
  identity when any Plan field is read;
- a relation-sensitive question cites every admitted relation operand and the
  exact checked relation question/result whose fields it consumes; and
- an occurrence-sensitive question cites an exact later-owned execution or
  observation occurrence and the exact Stage 3 invocation or observation tuple
  to which it is bound; Stage 3 does not mint a runtime occurrence, and the
  question cannot generalize the later-owned occurrence without a separately
  stated model and rule.

`AnalysisRequest` is a boundary obligation, not a final durable spelling. The
Analysis owner must close canonical encoding, identity, authentication,
admission, and persistence only for the variants justified by named consumers.

## 4. Required Analysis judgment families

Stage 4A must keep these families distinct even if they reuse typed envelopes or
bound algebra:

| Family | Required exact basis | Minimum nonclaim |
|---|---|---|
| `CoreEq` / `ProtocolEq` | Admitted operands, total typed maps, exact regimes, dependency and interpretation correspondence, and all protected observations | Shared IDs, shared Core, or observational similarity under an omitted observer is insufficient |
| `TraceEq[O]` | Exact observer set `O`, trace semantics, input and occurrence maps, schedule/context, and termination/failure treatment | It says nothing about observers outside `O` or an induced distribution |
| `TraceRefines[source,target,O]` | Directed source/target models, observer set, maps, simulation rule or witness, divergence/failure policy, and declared intentional changes | It is not symmetric equality and does not transport an unrelated property |
| `DistributionEq[O]` / `DistributionClose[...]` | Exact probability model, input distribution, correlation and challenge semantics, abort/failure mass, measurable map, metric/direction, parameters, and bound | Structural randomness declarations or replay membership do not prove a distribution theorem |
| `IntentionalChange` | Admitted operands, exact typed delta, affected protected observers/effects, and unchanged-field checks | A policy accepting the change is a separate consumer decision |
| `CostRelation[model]` | Exact cost model, input/parameter domain, declared observations, environment snapshot when read, and theorem or measurement basis | It does not become a semantic equivalence or compiler-optimality result |
| Soundness, knowledge, completeness, or later property track | Exact subject, notion-specific model, assumptions, quantitative variables, theorem/rule, and checked derivation | No common envelope creates a universal `verified` capability |

Directly decidable relations may use deterministic recomputation. Semantic
equivalence, refinement, distribution, completeness, satisfaction, and
cryptographic properties require an exact theorem/model-backed basis. A search
that finds no derivation is not a negative semantic judgment unless a cited
completeness result covers the exact search space.

## 5. Relation, Fiat--Shamir, and composition seams

### 5.1 Relations

Analysis may consume a `CheckedRelationCorrespondenceJudgment` only for its
exact `CorrespondenceQuestion`; unrequested clauses remain unknown. Instance
correspondence additionally requires the affirmative structural prerequisite
whose exact question contains `PublicPorts`, the identical
`AdmittedProtocolInterface`, the identical `AdmittedRelationBinding`, the exact
`AdmittedRelationInstance`, the dependent `ProtocolPublicAssignment<P>`, exact
admitted value-bridge dependency views attenuated from the binding,
`ExactRelationValueBridgeExecutionCapabilities`, and the identical
`CorrespondenceRegime`. A negative checked result is usable only as its exact
refutation, never as affirmative authority.

`RelationSatisfies` remains a separate later-owned signature:

```text
RelationSatisfies(
  exact RelationDefinitionRef,
  AdmittedRelationInstance,
  occurrence-local PrivateWitnessAssignment,
  exact semantic model and assumptions)
  -> later-owned qualified judgment
```

Before implementing this family, Stage 4A must resolve whether Relations or
Analysis owns it. Either choice preserves one secret capability per witness
occurrence, exact definition/interface regimes, qualified outcomes, and the rule
that correspondence cannot substitute for satisfaction.

### 5.2 Fiat--Shamir

The Analysis-owned entry signature is bounded by Stage 3:

```text
FSCompile(
  source: AdmittedProtocol
    whose exact ChallengeInterpretation is FreshPublicCoins,
  target: AdmittedProtocol
    whose exact ChallengeInterpretation is
      FiatShamir(the exact TranscriptConstructionId),
  construction_relation:
    affirmative CheckedFSConstruction retaining exactly
      source, target, the admitted TranscriptConstruction,
      FSConstructionMaps, and FSConstructionRegime,
  exact semantic_model_identity,
  exact theorem_or_rule_identity,
  explicit assumptions,
  quantitative_parameters)
  -> Analysis-owned qualified judgment
```

The affirmative construction capability supplies the exact source/target,
construction, event/challenge bijections, and potential/action-occurring prefix
descriptors. The Analysis rule must state its transcript/hash model, random-
oracle or other assumptions, joint-challenge treatment, failure/abort
conditioning, observer set, and quantitative losses. `FSCompile` being
unavailable is not target malformation. It does not transport every property.

`PropertyTransport[property]` is a second operation over an exact source
property judgment, exact affirmative checked relation, property-specific rule,
substitutions, assumptions, and losses. No global `FS-valid` or generic
preservation capability may replace it.

### 5.3 Composition

Property composition begins only after independent target admission and an
affirmative `CheckedCoreComposition`. Its question cites the exact child
occurrences, target, composition spec, resolved maps, observer set, semantic
model, assumptions, child property judgments, and property-specific composition
rule. Derived/imported challenges, private-randomness substitutions, captured
failures or reaches, suffix suppression, terminal combination, and every
`IntentionalChange` are explicit premises when they affect the property.

A negative checked composition carries typed mismatches and unaffected
agreements but no resolved maps or composition-context authority. It can refute
only the exact structural question and cannot enter an affirmative property-
composition rule.

## 6. Analysis authority and qualified outcomes

Analysis must separate:

```text
question/basis authentication
  -> derivation-plan checking or direct relation checking
  -> qualified semantic result
  -> optional consumer-justified persistence
```

Only a completed result mints the exact opaque process-local judgment
capability. Owner-defined results distinguish affirmative, fact-retaining
negative, unsupported, cannot-answer, refused, malformed, and checker failure
where applicable. External theorem names, proof-assistant artifacts, test
receipts, signatures, and model IDs are inputs or Evidence; they do not by
themselves establish theorem correspondence, model adequacy, or the Analysis
conclusion.

Every external model, theorem, rule, or algorithm reference is typed by its
owner, semantic regime, content identity, exact ABI or statement, and direct
dependency closure. The operation separately receives the authenticated
preimage/view and the exact identity-matched checker, interpreter, or derivation-
validation capability it invokes. A citation, catalog entry, same digest,
loaded prover, or live host function cannot satisfy either input, and neither
input enters the conclusion under a broader identity than the checked request.

A durable result is justified only by a named independent consumer and binds the
complete subject tuple, question, regime, model, rule, assumptions, parameters,
maps, read/dependency closure, checker identity, qualified outcome, and residual
trust. Serialization never preserves the live capability.

## 7. Compiler entry contract

Compiler work follows, rather than defines, the Analysis boundary. Its minimum
pipeline is:

```text
transform-family request + admitted predecessor
  -> unauthoritative successor proposal
  -> PIR authentication and independent whole-Protocol admission
  -> exact predecessor/successor relation check
  -> constraint and objective evaluation over exact Analysis results
  -> deterministic selection over one declared complete finite domain
  -> qualified Compiler decision
```

Every Compiler request must close:

- predecessor identity and admitted view;
- transform family, transform regime, immutable provider inputs, declared read
  set, and unauthoritative plan/proposal lineage;
- candidate-domain provider and exact completeness claim;
- target authentication/admission inputs for every candidate considered;
- the exact typed predecessor/successor relation, direction, observer set, maps,
  assumptions, intentional changes, checker, and regime;
- compiler-local legality constraints;
- every consumed Analysis judgment by exact identity, subject, question,
  assumptions, and qualified outcome;
- objectives, score domains, comparison order, tie handling, refusal behavior,
  and deterministic selection rule; and
- the scope in which `NoSelection` is a successful result rather than a search
  failure.

An eligibility constraint requiring a relation or property consumes the exact
affirmative capability. A negative result may support an explicitly negative
constraint but cannot be cast to affirmative eligibility. Unsupported,
cannot-answer, refusal, malformed input, and checker failure remain distinct
from both.

Compiler selection creates neither a Protocol nor a source/target relation. It
selects among already admitted, already relation-checked candidates and proves
optimality only over the exact declared comparison domain. A provider's mutable
clone, transform annotation, successful build, score, or selection result grants
no target admission or property transport. `PropertyTransport` remains
Analysis-owned even when Compiler requires its result.

## 8. Coordination with Stage 4B

The [Stage 4B entry contract](stage-4b-entry-contract.md) shares four boundaries
with this branch:

1. Analysis and OIR use the same Stage 3 meanings for protected observations,
   event occurrence, failure, terminal, nonproduction, and transcript order.
   Neither branch may introduce a private surrogate.
2. Any Analysis question that reads Interface, Plan, OIR, target, supplier, or
   runtime facts cites that subject explicitly and declares its full read set.
   A supposedly Protocol-only result must be invariant under their substitution.
3. Compiler has no implicit dependency on projection or a realizer. Endpoint
   feasibility may enter only as an exact independently owned constraint over
   named OIR/Realization results; absence is not hidden candidate rejection.
4. `ProjectionCorrect`, `LocalOirValid`, and `RealizesOir` remain Stage 4B
   results. If an Analysis theorem uses one, it consumes that exact result as a
   premise and does not redefine it.

Before either branch closes, both reconcile observer sets, protected effects,
Protocol/Interface/Plan identity dependencies, property-transport and
projection assumptions, and every field classified as semantic by one branch
but configuration or runtime state by the other.

## 9. Prerequisites and entry gate

Research may use this contract as a boundary probe. Stage 4A must not be
activated until a separate decision confirms all of the following:

- the selected Stage 3 Protocol, canonical PIR, Interface, Plan, Relations,
  Fiat--Shamir, and composition contracts have been promoted into reviewed
  durable owners, with temporary-note absorption recorded;
- the exact identity/regime, authentication/admission, view attenuation,
  reset/replay, qualified-outcome, and persistence rules consumed here are
  stable and mutually referenced;
- Analysis and Compiler narrow-view constructors have complete read
  vocabularies and source-owned adequacy predicates;
- the initial Analysis question families, model/theorem/assumption carriers,
  checker authority, and result schemas are enumerated rather than delegated to
  an ambient registry;
- the `RelationSatisfies` ownership decision is made before that operation is
  offered;
- the Compiler candidate-domain completeness and predecessor/successor relation
  envelopes are defined independently of provider search state; and
- the shared boundaries in Section 8 have been reconciled with the current
  Stage 4B entry contract.

An activation decision must name the bounded first question family, its input
views, owners, deliverables, verification plan, and exit gate. This page is not
that decision.

## 10. Required Stage 4A outputs

The branch is locally complete only when it produces reviewed owner documents
for:

- Analysis subjects, questions, typed assumptions, models, theorem/rule
  correspondence, derivations, qualified judgments, identities, capabilities,
  replay, and persistence;
- exact `FSCompile`, property-specific `PropertyTransport`, equivalence,
  refinement, distribution, intentional-change, cost, and selected property
  tracks;
- Compiler requests, transform-family proposals, target-admission handoff,
  checked predecessor/successor relations, finite domains, constraints,
  objectives, selection, `NoSelection`, decisions, replay, and persistence; and
- the cross-branch reconciliation record required by Section 8.

## 11. Exact nonclaims

This entry contract does not establish:

- relation satisfaction, witness validity, soundness, knowledge, completeness,
  zero knowledge, Fiat--Shamir security, or any quantitative bound;
- theorem truth, model adequacy, proof-assistant correspondence, or checker
  correctness;
- property preservation by admission, FS construction, structural composition,
  transformation, adjacency, annotation, or selection;
- Compiler legality, candidate-domain completeness, optimality, backend
  feasibility, or current transform support;
- OIR projection correctness, endpoint support, realization, deployment,
  invocation, runtime availability, performance, or cost; or
- Stage 4A activation, implementation authorization, migration, compatibility,
  evidence sufficiency, or consumer reliance.
