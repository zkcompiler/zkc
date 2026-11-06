module

public import ZkcExamples.Structured.FriApplications
public import Zkc.Source.Structured.OracleReferenceLaws

@[expose] public section

/-! The two retained collection helpers used by scalar FRI. A position list is
represented by actual unsigned indices throughout. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriIndexCollections
open Zkc.Source Zkc.Source.Structured
open FriSourceBodies FriSourceViews
attribute [local implicit_reducible] Numerical.arguments Numerical.results Op.arguments Op.results Op.regions

def emptyLaw (model : DomainModel) : ReferenceLaw model helper22Helper.inputs helper22Helper.outputs where
  body := helper22Body
  Requires _ _ := True
  reference | .nil => .returned (.cons [] .nil)
  valid _ | .nil, _ => by derive_process

theorem checkedAppend (model : FieldModel) (xs : List Nat) (i : Nat)
    (all : xs.all (· < indexLimit) = true) (capacity : xs.length + 1 < indexLimit)
    (coordinate : i < indexLimit) :
    Numerical.checkedEvaluateOn model "" "" .indicesAppend (.cons xs (.cons i .nil)) =
      .returned (.cons (xs ++ [i]) .nil) := by
  have length : xs.length < indexLimit := by omega
  have ingress : Numerical.checkValues model
      (.cons xs (.cons i .nil) : Values model.Value [.indices, .index]) = .ok () := by
    change (do
      (do Numerical.size xs.length; Numerical.require (xs.all (· < indexLimit) = true))
      Numerical.require (i < indexLimit)
      pure ()) = (Except.ok () : Numerical.Result Unit)
    simp [Numerical.size, Numerical.require,
      length, all, coordinate, bind, Except.bind, pure, Except.pure]
  simp [Numerical.checkedEvaluateOn, ingress, Numerical.evaluateOn, Numerical.finish,
    Numerical.size, capacity, bind, Except.bind, pure, Except.pure]

def appendLaw (model : DomainModel) : ReferenceLaw model helper23Helper.inputs helper23Helper.outputs where
  body := helper23Body
  Requires _
    | .cons xs (.cons i .nil) => xs.all (· < indexLimit) = true ∧ xs.length + 1 < indexLimit ∧ i < indexLimit
  reference | .cons xs (.cons i .nil) => .returned (.cons (xs ++ [i]) .nil)
  valid table
    | .cons xs (.cons i .nil), ⟨all, capacity, coordinate⟩ => by
      have step : (Evaluation.meaningOn model SiteObservations.closed table).OperationLaw
          (fun op ↦ .call op .done) (.exec (.numerical .indicesAppend "" ""))
          (.cons xs (.cons i .nil)) .nil (.done (.cons (xs ++ [i]) .nil)) := by
        apply RegionMeaning.OperationLaw.identity
        change primitiveOutcome (I := closedInterface) (Numerical.checkedEvaluateOn
          {model.toFieldModel with inverse := fun _ ↦ none} "" "" .indicesAppend (.cons xs (.cons i .nil))) = _
        rw [checkedAppend _ xs i all capacity coordinate]
        rfl
      derive_process using (exact step)

abbrev helpers (model : DomainModel) {I : PIR.Signature} :=
  unit.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩

theorem empty (model : DomainModel) (self : Nat) :
    OracleProtocol.owned model self self (helpers model) helper22Helper .nil =
      .done (.cons (some (ProtocolValue.ofConcrete .indices [])) .nil) := by
  rw [show (Values.nil : Values (Component (ProtocolValue model.toCarriers)) []) =
    ProtocolValue.embedComponents (Values.nil (Value := model.Value)).present from rfl,
    OracleProtocol.owned_present, (emptyLaw model).invokeOn unit.definitions unit.linked
      (by exact_body helper22Definition) .nil trivial]
  rfl

theorem append (model : DomainModel) (self : Nat) (xs : List Nat) (i : Nat)
    (all : xs.all (· < indexLimit) = true) (capacity : xs.length + 1 < indexLimit)
    (coordinate : i < indexLimit) :
    OracleProtocol.owned model self self (helpers model) helper23Helper
      (.cons (some (ProtocolValue.ofConcrete .indices xs))
        (.cons (some (ProtocolValue.ofConcrete .index i)) .nil)) =
      .done (.cons (some (ProtocolValue.ofConcrete .indices (xs ++ [i]))) .nil) := by
  change OracleProtocol.owned model self self (helpers model) helper23Helper
    (ProtocolValue.embedComponents (Values.cons (Value := model.Value) (ty := .indices) xs
      (.cons (ty := .index) i .nil)).present) = _
  rw [OracleProtocol.owned_present, (appendLaw model).invokeOn (helper := helper23Helper) unit.definitions unit.linked
    (by exact_body helper23Definition) (.cons xs (.cons i .nil)) ⟨all, capacity, coordinate⟩]
  rfl

end ZkcExamples.Structured.FriIndexCollections
