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
                     purpose,adequacy,binding_schema) =
  ConcreteOwnerReadSlotSchema(
    Relations,kind,coordinate_schema,purpose,field_projection,adequacy,
    binding_schema,None,common K3-C source-ingress failure partition)

K3BRelationSourceSlotFragment = CanonicalSeq [
  K3BRelationOwnerSlot(
    RelationDefinition,RelationDefinitionId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationDefinitionBody),SemanticMeaning,
    exact admitted definition and selected payload semantics,
    AdmittedRelationDefinition),
  K3BRelationOwnerSlot(
    RelationSemanticModel,RelationSemanticModelId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationSemanticModelBody),SemanticMeaning,
    exact definition/model subject agreement,AdmittedRelationSemanticModel),
  K3BRelationOwnerSlot(
    RelationInterface,RelationInterfaceId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationInterfaceBody),SemanticMeaning,
    exact public/Witness role typing,AdmittedRelationInterface),
  K3BRelationOwnerSlot(
    RelationInstance,RelationInstanceId selected by the subject schema,
    CompleteOwnerBodyProjection(RelationInstanceBody),SemanticMeaning,
    exact definition, model, Interface, and parameter agreement,
    AdmittedRelationInstance),
  K3BRelationOwnerSlot(
    ProtocolRelationBinding,ProtocolRelationBindingId selected by the subject
      schema,CompleteOwnerBodyProjection(ProtocolRelationBindingBody),
    SemanticMeaning,exact Protocol/Interface role agreement,
    AdmittedProtocolRelationBinding),
  K3BRelationOwnerSlot(
    PlanWitnessBinding,PlanWitnessBindingId selected by the subject schema,
    CompleteOwnerBodyProjection(PlanWitnessBindingBody),SemanticMeaning,
    exact Plan/Interface Witness role agreement,AdmittedPlanWitnessBinding),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact StatementEdge question and StatementEdgeRef pair selected by the
      subject schema,
    CompleteOwnerBodyProjection(StatementBindingCorrespondenceQuestionBody),
    PremiseSupport,exact question variant and owner edge target,
    AdmittedCorrespondenceQuestion),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact ClaimMeaning question and ClaimMeaningRef pair selected by the subject
      schema,
    CompleteOwnerBodyProjection(ClaimCorrespondenceQuestionBody),
    PremiseSupport,exact question variant and owner claim target,
    AdmittedCorrespondenceQuestion),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact PlanWitness question and PlanWitnessEdgeRef pair selected by the
      subject schema,
    CompleteOwnerBodyProjection(WitnessCorrespondenceQuestionBody),
    PremiseSupport,exact question variant and owner Witness target,
    AdmittedCorrespondenceQuestion),
  K3BRelationOwnerSlot(
    GroundingEquation,GroundingEquationId selected by the subject schema,
    CompleteOwnerBodyProjection(GroundingEquationBody),SemanticMeaning,
    exact relation-verifier grounding equation,AdmittedGroundingEquation),
  K3BRelationOwnerSlot(
    CorrespondenceQuestion,
    exact EquationGrounding question selected by the subject schema,
    CompleteOwnerBodyProjection(EquationGroundingQuestionBody),PremiseSupport,
    exact question variant and selected GroundingEquationId,
    AdmittedCorrespondenceQuestion)
]
```

Every coordinate schema, owner-body projection, purpose, adequacy predicate,
binding schema, authority class, and failure disposition above is part of this
fragment's canonical body. The property owner supplies the typed subject
parameter and concatenates the fragment with its non-Relations slots. Formation
then instantiates every slot through the common model; callers cannot replace a
fragment entry with an equal-looking field list. Occurrence reads and loss-result
bindings are separate family-specific support extensions, never optional fields
hidden inside this fragment.

The admitted binding subjects remain structural operands. Each correspondence
requirement above names the exact K3-B `CorrespondenceQuestionId`, binding ID,
and owner reference (`StatementEdgeRef`, `ClaimMeaningRef`,
or `PlanWitnessEdgeRef`). Its concrete affirmative `CheckedCorrespondence`
result binding belongs to Analysis support, and its fresh capability is
supplied only to the checking invocation. Acceptance is different: the
manifest selects only the static K2 `CheckDecl`
algorithm/evaluation-contract/input fields, the static `TerminalDecl` verdict,
required-check, and claim-disposition fields, and the exact Relations
`GroundingEquationId` plus its `EquationGrounding` correspondence-question
coordinate. Analysis forms the universal acceptance-to-relation proposition
over those owner reads and retains it in the property hypothesis context; its
established or assumed binding belongs to support. A concrete K3-B `RunCheck` or
run-grounding result can pressure one occurrence but cannot establish that
universal premise. There is no affirmative "checked binding" wrapper. The
checker derives rather than accepts:

- the K2 binding occurrence corresponding to the relation Statement slot;
- the K2 claim coordinate corresponding to the relation instance;
- the exact Plan Witness surface occurrence corresponding to the Witness slot;
- the check, reduction, or terminal occurrence that defines acceptance for this
  property; and
- every bridge-use coordinate and selected cardinality.

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
may import `K3BRelationSourceSlotFragment` and must then close all of those
objects in one acyclic dependency direction. In particular, this page never
depends on a cryptographic-property identity that later consumes the fragment.

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
