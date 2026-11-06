module

public import ZkcExamples.Structured.FriBoundedPositions
public import ZkcExamples.Structured.FriScalarLoop
public import Zkc.Source.Structured.PortForwarding

@[expose] public section

/-! Binding an already drawn position vector. This component checks three
logical input pairs and projects those same handles back to the caller.
The verifier forwards the geometry, coefficients, and round count. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriBinding
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews
open OracleProtocol (concrete)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions
  OracleOp.arguments OracleOp.results protocol2Signature

def context := lowDegreeContext.enter "s4" [0, 1]
abbrev initialSort := OracleLogicalSort.singleton (.table (.field extension) none)
abbrev layersSort := OracleLogicalSort.sequence (.table (.field extension) none) 3
abbrev Value (model : DomainModel) := Component (verifierValue model)

structure Committed (model : DomainModel) where
  initial : Value model initialSort.type
  layers : Value model layersSort.type
  folds : Value model layersSort.type
  shift : Value model (.field extension)
  size : Value model .index
  coefficients : Value model (.vector extension)
  rounds : Value model .index

def inputs (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions) :
    Values (Value model) protocol2Signature.inputs :=
  .cons none (.cons state.initial (.cons none (.cons state.layers (.cons none (.cons state.folds
    (.cons state.shift (.cons state.size (.cons state.coefficients (.cons state.rounds
      (.cons (concrete model .indices (xs.map Fin.val)) .nil))))))))))

/-- One component at any application prefix of this two-role installation. -/
def frame (parent : Option String) : ProtocolContext := {context with applicationPrefix := parent}

/-- Only logical field correspondence is specified. The retained declaration
supplies every flattened index, type, placement and holder/receiver split. -/
def origin : List String → Option PortForwarding.Origin
  | ["state", "positions"] => some (.input ["positions"])
  | ["state", "query_count"] => some (.parameter 0)
  | "state" :: path => some (.input ("committed" :: path))
  | _ => none

def outputPlan : PortForwarding.Plan protocol2Signature.inputs [.index] protocol2Signature.outputs :=
  (PortForwarding.compile FriSourceData.snapshot.sourceDeclarations protocol2Signature [.index] origin).get
    (by decide +kernel)

def output {model : DomainModel} (state : Committed model) (xs : FriScalarLoop.Positions) :
    Values (Value model) protocol2Signature.outputs :=
  outputPlan.apply (inputs model state xs) (.cons (concrete model .index 8) .nil)

private theorem admitted (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    FriBoundedPositions.Admitted (xs.map Fin.val) := by
  constructor
  · rw [List.length_map, count]; decide
  · simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, decide_eq_true_eq]
    rintro n j _ rfl
    exact j.isLt.trans (by decide : 32 < indexLimit)

theorem lengthStep (model : DomainModel) (parent : Option String) {site : String} (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    ((verifierAlgebra model).meaning (verifierTable model) (frame parent) 1).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper24Helper rfl 1 site)
      (.cons (concrete model .indices (xs.map Fin.val)) .nil) .nil (.done (.cons (concrete model .index 8) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper24Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .indices) (xs.map Fin.val) .nil).present) = _
  rw [OracleProtocol.owned_present, (FriBoundedPositions.lengthLaw model).invokeOn
    (helper := helper24Helper) unit.definitions unit.linked (by exact_body helper24Definition)
    (.cons (xs.map Fin.val) .nil) (admitted xs count)]
  change PIR.Process.done (I := OracleProtocol.Interface model)
    (Values.cons (concrete model .index (xs.map Fin.val).length) .nil) = _
  rw [List.length_map, count]

theorem boundsStep (model : DomainModel) (parent : Option String) {site : String} (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    ((verifierAlgebra model).meaning (verifierTable model) (frame parent) 1).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper25Helper rfl 1 site)
      (.cons (concrete model .indices (xs.map Fin.val)) (.cons (concrete model .index 32) .nil)) .nil
      (.done (.cons (concrete model .boolean true) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper25Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .indices) (xs.map Fin.val)
      (.cons (ty := .index) 32 .nil)).present) = _
  rw [OracleProtocol.owned_present, FriBoundedPositions.installed (xs.map Fin.val) 32 (admitted xs count)
    (by decide) (by intro x h; obtain ⟨j, _, rfl⟩ := List.mem_map.mp h; exact j.isLt)]
  rfl

set_option maxHeartbeats 2000000 in
/-- The process and its equation are synthesized together from the admitted
body, with only the mathematical guards supplied at their reached operands. -/
def presentation (model : DomainModel) (parent : Option String) (state : Committed model)
    (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    { process // protocol2Body.denote ((verifierAlgebra model).meaning (verifierTable model) (frame parent) 1)
        (inputs model state xs).get = process } := by
  refine ⟨?process, ?certificate⟩
  case certificate =>
    apply Region.Derivation.sound_identity
    derive_region using
      (first
       | apply lengthStep model parent xs count
       | apply boundsStep model parent xs count
       | exact OracleProtocol.equalIndex model 8
       | apply OracleProtocol.guardTrue model
       | apply RegionMeaning.OperationLaw.identity; rfl)

end ZkcExamples.Structured.FriBinding
