module

public import ZkcExamples.Structured.SumcheckSourceViews
public import Zkc.Source.Structured.OpenLaws
public import ZkcExamples.Structured.SumcheckVerifierBodies
public import ZkcExamples.Structured.SumcheckMathBindings

@[expose] public section

/-! Entire-source association of the seven-input body and consuming return.
The helper/participant contracts and optional security consumers build on these laws. -/
namespace ZkcExamples.Structured.SumcheckSourceLaws
open Zkc.Source Zkc.Source.Structured SumcheckSourceBodies SumcheckSourceViews

/-- The complete suffix invokes the consuming atPrefix helper. It is not a pure permutation. -/
theorem return_uses_atPrefix :
    ProtocolOp.localCall SumcheckPendingBodies.atPrefixHelper rfl 1 "s48" ∈
      (SumcheckVerifierBodies.reduceReturn []).erase.operations := by structured_mem

/-- Whole checked-tree formation fixes the callback along with the suffix. -/
theorem reduce_checked_tree :
    reduceDefinition.raw.elaborate (dialect := protocolDialect)
      reduceSignature.inputs reduceSignature.outputs = .ok reduceBody :=
  reduceDefinition.formed

theorem run_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) runSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) runSignature context self args =
      (runBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes runSignature.inputScopes) args).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes runSignature.outputScopes) results)) :=
  unit.protocol_body_view_as runDefinition run_member runSignature run_signature
    runBody run_raw context self args

theorem reduce_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G] (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) reduceSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) reduceSignature context self args =
      (reduceBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes reduceSignature.inputScopes) args).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes reduceSignature.outputScopes) results)) :=
  unit.protocol_body_view_as reduceDefinition reduce_member reduceSignature reduce_signature
    reduceBody reduce_raw context self args

/-- Exact original multiplicities and complete trees survive dependency ordering. -/
theorem source_protocol_permutation :
    ∃ domains headers summaries formed,
      checkUnitHeaders SumcheckSourceData.snapshot = .ok (domains, headers, summaries) ∧
      SumcheckSourceData.snapshot.protocolFunctions.mapM (fun function =>
        checkProtocol SumcheckSourceData.snapshot domains summaries function headers) = .ok formed ∧
      unit.protocols.Perm formed := imported.protocolPermutation

def mapDeclaration : CollectDeclaration :=
  ⟨mapHelper.name, .privateDef, mapHelper.inputs, mapHelper.outputs,
    SumcheckMathBindings.collection.domain, SumcheckMathBindings.collection.callback, ""⟩

theorem map_retained : Definition.collect mapDeclaration ∈ SumcheckSourceData.snapshot.definitions :=
  by structured_mem

theorem map_derived : mapDefinition.raw = mapBody.erase := rfl

theorem map_root_selected : interpolateHelper ∈
    preparationHelpers .realization unit.definitions := by decide +kernel

theorem map_member : mapDefinition ∈ unit.definitions :=
  by structured_mem

/-- Transport the literal full helper ABI into this complete source's own table. -/
theorem map_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    (args : Values (assignment F G) mapHelper.inputs) :
    invoke (unit.tables F G).closed mapHelper args =
      mapBody.denote (Evaluation.meaning (observedSites F G) (unit.tables F G).closed)
        args.get :=
  unit.closed_body_view_as mapDefinition map_member mapHelper rfl
    mapBody map_raw args

theorem first_member : firstDefinition ∈ unit.definitions :=
  by structured_mem

/-- Transport the literal full helper ABI into this complete source's own table. -/
theorem first_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    (args : Values (assignment F G) firstHelper.inputs) :
    invoke (unit.tables F G).closed firstHelper args =
      firstBody.denote (Evaluation.meaning (observedSites F G) (unit.tables F G).closed)
        args.get :=
  unit.closed_body_view_as firstDefinition first_member firstHelper rfl
    firstBody first_raw args

theorem values_member : valuesDefinition ∈ unit.definitions :=
  by structured_mem

/-- Transport the literal full helper ABI into this complete source's own table. -/
theorem values_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    (args : Values (assignment F G) valuesHelper.inputs) :
    invoke (unit.tables F G).closed valuesHelper args =
      valuesBody.denote (Evaluation.meaning (observedSites F G) (unit.tables F G).closed)
        args.get :=
  unit.closed_body_view_as valuesDefinition values_member valuesHelper rfl
    valuesBody values_raw args

theorem prefix_member : prefixDefinition ∈ unit.definitions :=
  by structured_mem

/-- Transport the literal full helper ABI into this complete source's own table. -/
theorem prefix_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    (args : Values (assignment F G) prefixHelper.inputs) :
    invoke (unit.tables F G).closed prefixHelper args =
      prefixBody.denote (Evaluation.meaning (observedSites F G) (unit.tables F G).closed)
        args.get :=
  unit.closed_body_view_as prefixDefinition prefix_member prefixHelper rfl
    prefixBody prefix_raw args

theorem valuesRealization_member : valuesRealizationDefinition ∈ unit.definitions :=
  by structured_mem

/-- Transport the literal full helper ABI into this complete source's own table. -/
theorem valuesRealization_body_view {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
    [DecidableEq F] [DecidableEq G]
    (args : Values (assignment F G) valuesRealizationHelper.inputs) :
    invoke (unit.tables F G).closed valuesRealizationHelper args =
      valuesRealizationBody.denote (Evaluation.meaning (observedSites F G) (unit.tables F G).closed)
        args.get :=
  unit.closed_body_view_as valuesRealizationDefinition valuesRealization_member valuesRealizationHelper rfl
    valuesRealizationBody valuesRealization_raw args

def valuesRealizationDeclaration : RealizationDeclaration :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.inputs,
    valuesRealizationHelper.outputs, valuesHelper.name⟩

theorem valuesRealization_retained : .realization valuesRealizationDeclaration ∈
    SumcheckSourceData.snapshot.definitions := by structured_mem

theorem valuesRealization_derived :
    valuesRealizationDefinition.raw = valuesRealizationDeclaration.raw := rfl

theorem valuesRealization_root_selected : valuesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization unit.definitions :=
  by decide +kernel

end ZkcExamples.Structured.SumcheckSourceLaws
