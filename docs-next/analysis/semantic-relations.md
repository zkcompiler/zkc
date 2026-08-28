# Analysis relation-source boundary

> **Document kind:** Target semantic specification
> **Document state:** Active non-normative K3-C target
> **Target status:** Exact K3-B Relations ingress fragment
> **Provisional owner:** `analysis`
> **Authority:** This page defines a redesign target only. The Relations target
> pages are the semantic owner and source for relation meaning, correspondence,
> and satisfaction within the redesign corpus; they are not current authority.
> Current specifications under [`docs/`](../../docs/README.md) remain
> authoritative until cutover. This page establishes no relation truth or
> cryptographic property.

## 1. Scope

This page defines how Analysis selects exact K3-B relation meaning and
occurrences without creating a shadow relation or Protocol. It owns only the
Relations source-slot fragment. The cryptographic-property page owns the
complete Schnorr source profile, finite transcript-pair type, challenge model,
manifest, experiment, and property.

General Core/Protocol equality, trace refinement, intentional-change,
distribution, and cost families from the earlier Stage 4A catalog are deferred.
They may later reuse the common Analysis calculus, but they are not inferred
from this relation seam.

## 2. Ownership

Relations owns:

- `RelationDefinition`, its admitted semantic model, and definition/model
  correspondence;
- the four Interface roles: public instance, private Witness, Oracle statement,
  and phase input;
- relation instances and owner-local assignments;
- `CheckedRelationSatisfaction` and its confidential authority;
- Protocol relation bindings, Plan Witness bindings, artifact interpretation,
  grounding equations, bridge laws, bridge-use enumeration, and lossy-use
  export; and
- the meaning and polarity of every Relations checked result.

PIR owns the `InteractiveCore`, Protocol, Statement binding occurrences,
messages, challenges, checks, claims, reductions, terminals, Plans, and
execution-issued `RelationRunView`.

Analysis owns only the exact property question, experiment, theorem/rule edge,
hypotheses, quantitative interpretation, and resulting conditional judgment.

## 3. Exact relation source projection

The following exact slot-schema fragment is concatenated into a complete source
profile by a property owner. It is not a profile or manifest, carries no ID,
and cannot be admitted or consumed on its own:

```text
K3BRelationOwnerSlot(kind,coordinate_schema,field_projection,
                     purpose,adequacy_evaluator_id,binding_schema,
                     required_authority_class) =
  ConcreteOwnerReadSlotSchema(
    Relations,kind,coordinate_schema,purpose,field_projection,
    adequacy_evaluator_id,binding_schema,required_authority_class,
    common K3-C source-ingress failure partition)

K3BRelationDefinitionAdequacy,
K3BRelationModelAdequacy,
K3BRelationInterfaceAdequacy,
K3BRelationInstanceAdequacy,
K3BProtocolRelationBindingAdequacy,
K3BPlanWitnessBindingAdequacy,
K3BStatementQuestionAdequacy,
K3BClaimQuestionAdequacy,
K3BWitnessQuestionAdequacy,
K3BGroundingEquationAdequacy, and
K3BEquationGroundingQuestionAdequacy
  = pairwise-distinct exact AnalysisAdequacyEvaluatorId values in the selected
    `K3CCryptographicPropertyLanguageProfileId`; each evaluator's closed
    input schema is the complete owner body plus the typed subject coordinates
    named by its slot below, and its exact no-extra supported-input profile set
    is the cryptographic-property profile plus the exact K3-B owner profile

The bounded K3-C executable has not implemented this per-slot evaluator
catalog. Its current property and transport law-source surrogates contain two
generic evaluator-schema rows each, and its formed evaluator bodies currently
name only the owning Analysis profile in `supported_input_profile_ids`. Those
checks pressure a smaller source-ingress mechanism; they do not establish the
pairwise-distinct evaluator identities, complete owner schemas, or two-profile
sets required here. These target requirements remain implementation-
correspondence obligations rather than optional refinements.

K3BCheckedCorrespondenceBindingSchema =
  ExactCheckedResultAuthorityBinding<Relations,CheckedCorrespondence>

K3BSharedRelationSourceSlotFragment = CanonicalSeq [
  K3BRelationOwnerSlot(
    RelationDefinition,RelationDefinitionId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationDefinitionBody),SemanticMeaning,
    K3BRelationDefinitionAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,RelationDefinition>,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    RelationSemanticModel,RelationSemanticModelId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationSemanticModelBody),SemanticMeaning,
    K3BRelationModelAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,RelationSemanticModel>,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    RelationInterface,RelationInterfaceId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationInterfaceBody),SemanticMeaning,
    K3BRelationInterfaceAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,RelationInterface>,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    RelationInstance,RelationInstanceId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationInstanceBody),SemanticMeaning,
    K3BRelationInstanceAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,RelationInstance>,
    FreshSourceCapability)
]

K3BProtocolAxisRelationSourceSlotFragment(axis) = CanonicalSeq [
  K3BRelationOwnerSlot(
    ProtocolRelationBinding,ProtocolRelationBindingId selected by the subject's
      exact axis ingress,CompleteOwnerBodyProjection(ProtocolRelationBindingBody),
    SemanticMeaning,K3BProtocolRelationBindingAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,ProtocolRelationBinding>,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    PlanWitnessBinding,PlanWitnessBindingId selected by the subject's exact
      axis ingress,
    CompleteOwnerBodyProjection(PlanWitnessBindingBody),SemanticMeaning,
    K3BPlanWitnessBindingAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,PlanWitnessBinding>,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact StatementEdge question and StatementEdgeRef pair selected by the
      subject's exact axis ingress,
    CompleteOwnerBodyProjection(CorrespondenceQuestionBody),PremiseSupport,
    K3BStatementQuestionAdequacy,K3BCheckedCorrespondenceBindingSchema,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact ClaimMeaning question and ClaimMeaningRef pair selected by the
      subject's exact axis ingress,
    CompleteOwnerBodyProjection(CorrespondenceQuestionBody),PremiseSupport,
    K3BClaimQuestionAdequacy,K3BCheckedCorrespondenceBindingSchema,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact PlanWitness question and PlanWitnessEdgeRef pair selected by the
      subject's exact axis ingress,
    CompleteOwnerBodyProjection(CorrespondenceQuestionBody),PremiseSupport,
    K3BWitnessQuestionAdequacy,K3BCheckedCorrespondenceBindingSchema,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    GroundingEquation,GroundingEquationId selected by the subject's exact axis
      ingress,
    CompleteOwnerBodyProjection(GroundingEquationBody),SemanticMeaning,
    K3BGroundingEquationAdequacy,
    ExactAdmittedSubjectAuthorityBinding<Relations,GroundingEquation>,
    FreshSourceCapability),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact EquationGrounding question selected by the subject's exact axis
      ingress,
    CompleteOwnerBodyProjection(CorrespondenceQuestionBody),PremiseSupport,
    K3BEquationGroundingQuestionAdequacy,
    K3BCheckedCorrespondenceBindingSchema,FreshSourceCapability)
]
```

Every coordinate schema, owner-body projection, purpose, adequacy evaluator ID,
binding schema, authority class, and failure disposition above is part of the
corresponding fragment's canonical body. The property owner supplies the typed
subject parameter, chooses a declared Protocol axis, and concatenates the
shared fragment, exactly one axis fragment, and its non-Relations slots.
Formation rejects an axis whose `ProtocolRelationBinding.protocol_id`, Plan
Witness surface Protocol, correspondence-question operands, grounding run
slots, or owner result bindings do not name that exact Protocol. Callers cannot
replace a fragment entry with an equal-looking field list. A Fresh/Fiat--Shamir
pair therefore instantiates the axis fragment twice; equality after replacing
only `ProtocolId` is an explicit producer-checked premise and never an identity
alias or a derivation from the transcript construction. Occurrence reads and
loss-result bindings are separate family-specific support extensions, never
optional fields hidden inside either fragment.

Relations exports one tagged `CorrespondenceQuestionBody`, not four independent
variant body schemas. Each of the four slots above therefore projects that
complete tagged body. Its exact adequacy evaluator verifies the expected
variant tag and the selected `StatementEdgeRef`, `ClaimMeaningRef`,
`PlanWitnessEdgeRef`, or `GroundingEquationId` after authentication. A
variant-specific shadow body, tag-stripped payload, or structurally similar
question is malformed or refused according to the evaluator contract.

The admitted binding subjects remain structural operands. Each correspondence
requirement above names the exact K3-B `CorrespondenceQuestionId`, binding ID,
and owner reference (`StatementEdgeRef`, `ClaimMeaningRef`,
or `PlanWitnessEdgeRef`). Its concrete affirmative `CheckedCorrespondence`
result binding belongs to Analysis support, and its fresh capability is
supplied only to the checking invocation. Acceptance is different: the
manifest selects the exact PIR-owned producer closure of the static accepting
check and terminal, and the exact Relations
`GroundingEquationId` plus its `EquationGrounding` correspondence-question
coordinate. Analysis forms the universal acceptance-to-relation proposition
over those owner reads and retains it in the property hypothesis context; its
established or assumed binding belongs to support. A concrete K3-B `RunCheck` or
run-grounding result can pressure one occurrence but cannot establish that
universal premise. There is no separate Analysis-authored affirmative
"checked binding" semantic subject: the only affirmative authority is the
Relations-owned checked-result binding consumed in support. The checker derives
rather than accepts:

- the K2 binding occurrence corresponding to the relation Statement slot;
- the K2 claim coordinate corresponding to the relation instance;
- the exact Plan Witness surface occurrence corresponding to the Witness slot;
- the check, reduction, or terminal occurrence that defines acceptance for this
  property; and
- every bridge-use coordinate and selected cardinality.

The PIR portion is exactly:

```text
K3CAcceptanceTerminalLeaves(S) = {
  exact PIRStaticViewFieldCoordinate leaves in
    CoreView(S.shared_core_id,EffectView) for the selected CheckDecl algorithm,
    evaluation contract, inputs, and unique invoke, and for the selected
    TerminalDecl verdict, required checks, claim dispositions, and unique
    occurrence
}

K3CAcceptanceProducerProjection(S) =
  RequiredPIRViewReadClosure(
    CoreView(S.shared_core_id,EffectView),K3CAcceptanceTerminalLeaves(S))
```

`RequiredPIRViewReadClosure` is PIR-owned. On an `EffectView` it returns the
least closed field set containing the selected leaves and every occurrence,
value producer, guard, scope, check, type, ordering, and effect dependency that
can feed them. The Analysis manifest must select exactly that set, and the
issued `PIRStaticViewProjection` must carry the matching
`ExactPIRStaticViewAuthorityBinding<EffectView>` plus a fresh
`PIRStaticViewCapability`. Omitting one producer, adding an ambient effect, or
recomputing a shadow closure is malformed. Consequently the universal
proposition cannot quantify over a terminal while silently leaving the
computation of its verdict outside the authenticated read domain.

The deterministic correspondence question universally quantifies over exact
structurally complete transcript projections under this manifest and concludes
that the selected K2 accepting check/terminal agrees with the admitted
relation-verifier equation. It is an Analysis goal, not an owner source field;
changing the check, terminal, equation, transcript domain, or direction changes
that goal. K3-C supplies no unconditional proof of it.

The concrete `CheckBridgeUseSet` result, any occurrence-local loss-source
result, and their consumer-source joins are support or invocation inputs. They
do not enter this semantic manifest merely because their derived coordinates
or count may parameterize a later proposition.

The two admitted binding subjects and every selected affirmative
correspondence result are revalidated at consumption. Whole-Protocol Statement
coverage and whole-selected-Interface Witness coverage are separate questions
and must both be requested when the property needs them. Equal labels, values,
or IDs cannot replace an exact checked edge.

An occurrence-sensitive property adds one exact `RelationRunView` and,
separately, a live causal-generation capability when it claims causality. A
replay-qualified view supports only its declared public read coordinates. It
cannot reveal a Witness, prove strategy generation, or establish a universal
property.

## 4. Satisfaction seam

`CheckedRelationSatisfaction` remains an owner-local Relations result. Analysis
may consume it only through an exact source-manifest slot whose proposition
requires one concrete satisfaction occurrence. The invocation must receive the
matching fresh capability and complete source binding.

Analysis cannot:

- accept a caller Boolean for satisfaction;
- serialize or hash the confidential result into a portable premise;
- infer satisfaction from Protocol acceptance or the presence of a Witness;
- infer Protocol acceptance from satisfaction; or
- generalize one satisfaction occurrence to completeness, soundness, or
  knowledge.

The initial special-soundness profile needs the admitted relation predicate and
its exact occurrence maps, but no concrete satisfaction result. Its conclusion
states that an extracted value satisfies the relation under its explicit
algebraic/correspondence hypotheses.

## 5. Property-owner boundary

This page deliberately defines no `K3CSubjectTuple`, challenge-domain ID,
transcript or pair carrier, source profile, manifest, experiment, extractor,
question, goal, or property-family contract. The cryptographic-property owner
may import `K3BSharedRelationSourceSlotFragment` and one or more exact
`K3BProtocolAxisRelationSourceSlotFragment(axis)` instantiations and must then
close all of those objects in one acyclic dependency direction. In particular,
this page never depends on a cryptographic-property identity that later
consumes either fragment.

## 6. Loss-bearing bridges

The relation manifest imports a lossy bridge only through the Relations-owned
closed path:

```text
CheckedBridgeUse
  -> exact LossyUseSelection
  -> occurrence grounding and source premise
  -> qualified loss export
  -> fresh CheckLossyUseAtConsumerSource join
```

Only an overall affirmative, occurrence-complete result authorizes Analysis to
use `SelectedBridgeUseCardinality`. The wider structural cardinality is inert.
Analysis never authors the count or treats an exported canonical value as an
already sorted probability or advantage.

For `sha256-216`, the bridge declares a directional projection and a collision
relation. It does not establish collision resistance. Any quantitative price
remains conditional on the exact source premise, occurrence set, export
interpretation, theorem/rule, and parameter map.

## 7. Deferred relation families

Before activation, each deferred equality, trace, refinement, distribution, or
cost family must define its own source manifest, observer, map direction,
experiment, complete negative meaning, and quantitative semantics. No result
on one exact map refutes existence of another map, and no finite trace becomes
a distributional statement without a separate rule.
