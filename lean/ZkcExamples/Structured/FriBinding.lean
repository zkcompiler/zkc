module

public import ZkcExamples.Structured.FriBoundedPositions
public import ZkcExamples.Structured.FriScalarLoop

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

def location (row : Nat) : OracleLocation := ⟨⟨29, []⟩, 29, [7, 1, row]⟩

def marks (model : DomainModel) : List String → PIR.Process (OracleProtocol.Interface model) Unit
  | [] => .done ()
  | name :: names => .call (.mark name (qualifyProtocolSite context.applicationPrefix name))
      fun _ ↦ marks model names

def input (model : DomainModel) (sort : OracleLogicalSort) (row : Nat) (handle : Value model sort.type) :
    PIR.Process (OracleProtocol.Interface model) (Value model sort.type) :=
  .call (.oracle ⟨.input sort 0 [1] [("rows", 32)], location row, 1, context.roles, .cons none (.cons handle .nil)⟩)
    fun out ↦ .done (out.get .here)

def project (model : DomainModel) (sort : OracleLogicalSort) (row : Nat) (handle : Value model sort.type) :
    PIR.Process (OracleProtocol.Interface model) (Values (Value model) [sort.dataType, sort.type]) :=
  .call (.oracle ⟨.components sort 0 [1], location row, 1, context.roles, .cons handle .nil⟩) .done

def program (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions) :
    PIR.Process (OracleProtocol.Interface model) (Values (Value model) protocol2Signature.outputs) := do
  marks model [""]
  let initial ← input model initialSort 0 state.initial
  marks model [""]
  let layers ← input model layersSort 1 state.layers
  marks model [""]
  let folds ← input model layersSort 2 state.folds
  marks model ["s0", "", "", "s3", "s4", "", "", "s7", "", "s9", "s11", "", "s13", "s15", "", ""]
  let a ← project model initialSort 18 initial
  marks model [""]
  let b ← project model layersSort 19 layers
  marks model [""]
  let c ← project model layersSort 20 folds
  return .cons (a.get .here) (.cons (a.get (.there .here))
    (.cons (b.get .here) (.cons (b.get (.there .here))
      (.cons (c.get .here) (.cons (c.get (.there .here))
        (.cons state.shift (.cons state.size (.cons state.coefficients
          (.cons (concrete model .indices (xs.map Fin.val)) (.cons state.rounds (.cons (concrete model .index 8) .nil)))))))))))


private theorem admitted (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    FriBoundedPositions.Admitted (xs.map Fin.val) := by
  constructor
  · rw [List.length_map, count]; decide
  · simp only [List.all_eq_true, List.mem_map, forall_exists_index, and_imp, decide_eq_true_eq]
    rintro n j _ rfl
    exact j.isLt.trans (by decide : 32 < indexLimit)

private theorem lengthStep (model : DomainModel) (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper24Helper rfl 1 "s0")
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

private theorem boundsStep (model : DomainModel) (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    ((verifierAlgebra model).meaning (verifierTable model) context 1).OperationLaw
      (fun op ↦ .call op .done) (.localCall helper25Helper rfl 1 "s9")
      (.cons (concrete model .indices (xs.map Fin.val)) (.cons (concrete model .index 32) .nil)) .nil
      (.done (.cons (concrete model .boolean true) .nil)) := by
  apply RegionMeaning.OperationLaw.identity
  change OracleProtocol.owned model 1 1 (FriIndexCollections.helpers model) helper25Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .indices) (xs.map Fin.val)
      (.cons (ty := .index) 32 .nil)).present) = _
  rw [OracleProtocol.owned_present, FriBoundedPositions.installed (xs.map Fin.val) 32 (admitted xs count)
    (by decide) (by intro x h; obtain ⟨j, _, rfl⟩ := List.mem_map.mp h; exact j.isLt)]
  rfl

set_option maxHeartbeats 1500000 in
theorem body (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions) (count : xs.length = 8) :
    protocol2Body.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) (inputs model state xs).get =
      program model state xs := by
  trans ?generated
  · derive_process using
      (first
       | apply lengthStep model xs count
       | apply boundsStep model xs count
       | exact OracleProtocol.equalIndex model 8
       | apply OracleProtocol.guardTrue model)
  · simp only [program, marks, input, project, bind, pure, PIR.Process.bind]
    rfl

theorem installed (model : DomainModel) (state : Committed model) (xs : FriScalarLoop.Positions)
    (count : xs.length = 8) :
    invokeProtocol (verifierTable model) protocol2Signature context 1 (inputs model state xs) =
      (program model state xs).bind fun values ↦
        .done (maskValues 1 (context.mapScopes protocol2Signature.outputScopes) values) :=
  (verifierAlgebra model).invokePresented unit.protocolsLinked protocol2Definition protocol2_member
    context 1 _ _ (body model state xs count)

end ZkcExamples.Structured.FriBinding
