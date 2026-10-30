module

public import Zkc.Source.Structured.DomainLinking
public import Zkc.Source.Participant
public import Zkc.Semantics.OperationSupport
public import ZkcSecurity.ProgramLogic.Transcript.CostComposition

@[expose] public section

/-! Closed nominal helper work cannot make a query in the surrounding source
interface. It may still stop. This cost fact asserts no successful execution. -/
set_option autoImplicit false
namespace ZkcSecurity.Obligations.SourcePure
open Zkc.Source Zkc.Source.Structured Zkc.Transcript ZkcSecurity.FiatShamir
variable {I : PIR.Signature} {E P A : Type} {Raw : E → Type}
  (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)

theorem closed_cost (process : Closed A) (history : List E) :
    Typed.ChargedCostBound absorb charge (process.interpret closedLift) history 0 := by
  cases process with
  | done => trivial
  | halt => trivial
  | call impossible => exact nomatch impossible

theorem owned_cost (model : DomainModel) (definitions : List CheckedDefinition)
    (helper : Helper) (owner self : Nat)
    (arguments : Values (Component model.Value) helper.inputs) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (Participant.owned self owner
        (invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[],[]⟩).closed helper)
        arguments) history 0 := by
  unfold Participant.owned
  split
  · cases RoleFamily.sequence arguments with
    | none => trivial
    | some values =>
      apply (CostComposition.map_iff _ _ _).mpr
      rw [Evaluation.closed_invoke_componentTablesOn]
      exact closed_cost absorb charge _ history
  · trivial

/-- Optional Math calls also preserve the closed interface. This covers absent
arguments without inventing a successful helper result. -/
theorem components_cost (model : DomainModel) (definitions : List CheckedDefinition)
    (helper : Helper) (arguments : Values (Component model.Value) helper.inputs) (history : List E) :
    Typed.ChargedCostBound absorb charge
      (invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[],[]⟩).components
        helper arguments) history 0 := by
  have interpreted := (Evaluation.ComponentTablesOn.fold_interpret (model := model)
    (closedLift (I := I)) (SiteObservations.silent_interpret _)
    (Evaluation.ComponentTablesOn.Interprets.empty _) definitions).components helper arguments
  rw [← interpreted]
  exact closed_cost absorb charge _ history

omit absorb charge in
theorem owned_support (model : DomainModel) (definitions : List CheckedDefinition)
    (helper : Helper) (owner self : Nat) (allowed : I.Op → Prop)
    (arguments : Values (Component model.Value) helper.inputs) :
    PIR.OperationSupport allowed
      (Participant.owned self owner
        (invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[],[]⟩).closed helper)
        arguments) := by
  unfold Participant.owned
  split
  · cases RoleFamily.sequence arguments with
    | none => trivial
    | some values =>
      change PIR.OperationSupport allowed ((invoke _ helper values).bind _)
      refine PIR.OperationSupport.bind ?_ _ ?_
      · rw [Evaluation.closed_invoke_componentTablesOn]
        exact PIR.OperationSupport.closed allowed _ _ (fun impossible => nomatch impossible)
      · intro; trivial
  · trivial

omit absorb charge in
theorem components_support (model : DomainModel) (definitions : List CheckedDefinition)
    (helper : Helper) (allowed : I.Op → Prop)
    (arguments : Values (Component model.Value) helper.inputs) :
    PIR.OperationSupport allowed
      (invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[],[]⟩).components
        helper arguments) := by
  have interpreted := (Evaluation.ComponentTablesOn.fold_interpret (model := model)
    (closedLift (I := I)) (SiteObservations.silent_interpret _)
    (Evaluation.ComponentTablesOn.Interprets.empty _) definitions).components helper arguments
  rw [← interpreted]
  exact PIR.OperationSupport.closed allowed _ _ (fun impossible => nomatch impossible)
end ZkcSecurity.Obligations.SourcePure
