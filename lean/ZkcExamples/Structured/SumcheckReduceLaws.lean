module

public import ZkcExamples.Structured.SumcheckReduceViews
public import Zkc.Source.Structured.OpenLaws
public import ZkcExamples.Structured.SumcheckVerifierBodies

@[expose] public section

/-! Entire-source association and the actual six-slot return permutation.
The helper/participant contracts and optional security consumers build on these laws. -/
namespace ZkcExamples.Structured.SumcheckReduceLaws
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies SumcheckReduceViews

def returnValues {Value : Ty → Type} (state : Values Value repeatState) :
    Values Value reduceSignature.outputs :=
  SumcheckVerifierBodies.reduceReturnValues state

theorem return_indices : (reduceReturn []).erase =
    .ret SumcheckVerifierBodies.reduceReturnIndices := rfl

/-- This suffix is embedded directly in the admitted literal reduceBody. -/
theorem return_equation {I : PIR.Signature} (meaning : RegionMeaning protocolDialect I)
    (state : Values meaning.Value repeatState) :
    (reduceReturn []).denote meaning state.get = .done (returnValues state) := rfl

/-- Whole checked-tree formation fixes the callback along with the suffix. -/
theorem reduce_checked_tree :
    reduceDefinition.raw.elaborate (dialect := protocolDialect)
      reduceSignature.inputs reduceSignature.outputs = .ok reduceBody :=
  reduceDefinition.formed

/-- The original complete Reduce function has this same terminal permutation. -/
theorem original_reduce_return :
    ∃ instructions, (SumcheckReduceData.snapshot.protocolFunctions[1]).body =
      .block instructions (.ret SumcheckVerifierBodies.reduceReturnIndices) := ⟨_, rfl⟩

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
      checkUnitHeaders SumcheckReduceData.snapshot = .ok (domains, headers, summaries) ∧
      SumcheckReduceData.snapshot.protocolFunctions.mapM (fun function =>
        checkProtocol SumcheckReduceData.snapshot domains summaries function headers) = .ok formed ∧
      unit.protocols.Perm formed := imported.protocolPermutation

def mapDeclaration : MapDeclaration :=
  ⟨mapHelper.name, mapHelper.inputs, mapHelper.outputs,
    MapFirstBodies.mapSpec.helperName, MapFirstBodies.mapSpec.rowwise⟩

theorem map_retained : .map mapDeclaration ∈ SumcheckReduceData.snapshot.definitions :=
  List.mem_cons_self

theorem map_derived : mapDefinition.raw = mapDeclaration.raw := rfl

theorem map_root_selected : mapDeclaration.spec.helper ∈
    preparationHelpers .map unit.definitions := imported.mapRootSelected map_retained

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

end ZkcExamples.Structured.SumcheckReduceLaws
