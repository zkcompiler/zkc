import Zkc.Source.Structured.CommonCoordinateSoundness

set_option autoImplicit false
open Zkc.Source Zkc.Source.Structured CommonCoordinate NormalForm
namespace Tests.OracleCommonCoordinateLaws

private abbrev model : DomainModel := ringModel Int Int
private def inputs (value : Option Nat) : Observations model [.value .index] :=
  .cons value .nil
private def counter : Expression [.value .index] .index := .var .here

-- Missing common values and different reached counters do not discharge observations.
example : ¬ AgreeOn model (demanded counter) (inputs none) (inputs (some 0)) := by
  intro agree
  have impossible := agree .here (by simp [counter, CommonCoordinate.demanded])
  cases impossible

example : ¬ AgreeOn model (demanded counter) (inputs (some 0)) (inputs (some 1)) := by
  intro agree
  have impossible := agree .here (by simp [counter, CommonCoordinate.demanded])
  cases impossible

-- Equal counters do not assert equal enclosing counts or identical lexical origins.
example : [Boundary.iteration 0 [7, 1, 2] 0] ≠
    [Boundary.iteration 0 [7, 1, 2] 1] := by decide
example : [Boundary.application 0 [7, 1, 2]] ≠
    [Boundary.application 0 [7, 1, 3]] := by decide
example : Binding.counter 2 [(0, [7, 1, 3])] [7, 1, 1] ≠
    Binding.counter 2 [(0, [7, 1, 4])] [7, 1, 1] := by decide
example : Binding.counter 2 [] [7, 1, 1] ≠ Binding.counter 2 [] [7, 1, 2] := by decide
example : Binding.input 0 0 .index ≠ Binding.input 0 1 .index := by decide

-- A stop admits no successful continuation, independently of handlers and replies.
example {A : Type} (value : A) (reason : PIR.Stop) :
    ¬ Returned (I := OracleProtocol.Interface model) (.halt reason) value := by
  intro returned
  cases returned

-- Optional readback covers the real calculation operation, not only term evaluation.
example (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model)) :
    ProtocolCalculation.operation model (OracleProtocol.demand model) self ordinary helpers
      .indexWrappingAdd (.cons none (.cons (some (ProtocolValue.ofConcrete .index 1)) .nil)) =
      .done (.cons none .nil) :=
  scalar_operation (OracleProtocol.demand model) self ordinary helpers .indexWrappingAdd rfl _

example (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model)) :
    ProtocolCalculation.operation model (OracleProtocol.demand model) self ordinary helpers
      .indexWrappingAdd
      (.cons (some (ProtocolValue.ofConcrete .index 1)) (.cons none .nil)) =
      .done (.cons none .nil) := by
  have equation := scalar_operation (OracleProtocol.demand model) self ordinary helpers
    .indexWrappingAdd rfl
    (.cons (some (ProtocolValue.ofConcrete .index 1)) (.cons none .nil))
  simpa [Op.arguments, Op.results, scalarValues, ProtocolValue.concreteComponents, RoleFamily.sequence,
    ProtocolValue.embedComponents, Values.absent] using equation

-- Overflow agrees with the existing word semantics, rather than natural successor.
example : observe model
    (.calc .indexWrappingAdd rfl (.cons (.index (indexLimit - 1))
      (.cons (.index 1) .nil)) .here : Expression [] .index) .nil = some 0 := by
  decide

-- The source readback returns actual absence for a known source-input symbol.
example : Matches (inputSymbols.inputTerms [.index]) (inputObservations
    (.cons none .nil : Values (Component (ProtocolValue model.toCarriers)) [.index]))
    (.cons none .nil) := input_readback _

#print axioms observe_agreement
#print axioms scalar_operation
#print axioms transfer_sound
#print axioms Returned.of_run
#print axioms Prefix.readback
#print axioms selection_readback
#print axioms Plan.coordinate_known
#print axioms Plan.reached_agreement
#print axioms RootPlan.reached_agreement
#print axioms rootFrame_process
#print axioms UnitCertificate.covers
#print axioms rolePairs_complete
#print axioms Selection.demanded_requirement
#print axioms certify
#print axioms Imported.oracleSubject
#print axioms OracleSubject.coordinateAuthority

end Tests.OracleCommonCoordinateLaws
