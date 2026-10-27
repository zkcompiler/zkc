module

public import Zkc.Construction.OriginalSimulation
public meta import Lean.Meta.Tactic.Simp

@[expose] public section
/-! Local simplifier congruences for structural certificate search. Only the
reached head is normalized; each reply continuation is checked by the call rule. -/
set_option autoImplicit false
namespace Zkc.Construction.Original
variable {I : PIR.Signature} {A B : Type}

theorem callHead (operation : I.Op) (next : I.Reply operation → PIR.Process I A) :
    PIR.Process.call operation next = PIR.Process.call operation next := rfl

theorem bindHead (left right : PIR.Process I A) (same : left = right)
    (next : A → PIR.Process I B) : left.bind next = right.bind next := by cases same; rfl

theorem interpretIf {J : PIR.Signature} (operations : PIR.OperationInterpretation I J)
    (condition : Prop) [Decidable condition] (left right : PIR.Process I A) :
    (if condition then left else right).interpret operations =
      if condition then left.interpret operations else right.interpret operations := by
  split <;> rfl

variable {carriers : Zkc.Source.Structured.Carriers}

theorem foldIf (routing : Routing) (condition : Prop) [Decidable condition]
    (left right : PIR.Process (Zkc.Source.Structured.Occurrence.signature carriers) A)
    (state : State carriers) :
    fold routing (if condition then left else right) state =
      if condition then fold routing left state else fold routing right state := by
  split <;> rfl

theorem foldActionCall (routing : Routing)
    (operation : (Zkc.Source.Structured.participantInterfaceOn carriers).Op)
    (next : (Zkc.Source.Structured.participantInterfaceOn carriers).Reply operation →
      PIR.Process (Zkc.Source.Structured.participantInterfaceOn carriers) A)
    (state : State carriers) :
    fold routing ((PIR.Process.call operation next).interpret Zkc.Source.Structured.Occurrence.actions) state =
      (operations routing (.action operation) state).bind fun (reply, final) =>
        fold routing ((next reply).interpret Zkc.Source.Structured.Occurrence.actions) final := by
  simp only [PIR.Process.interpret, fold_bind, Zkc.Source.Structured.Occurrence.actions]
  rw [fold_action]

theorem foldActionDone (routing : Routing) (value : A) (state : State carriers) :
    fold routing ((PIR.Process.done value : PIR.Process
      (Zkc.Source.Structured.participantInterfaceOn carriers) A).interpret
        Zkc.Source.Structured.Occurrence.actions) state = .done (value, state) := rfl

theorem foldActionHalt (routing : Routing) (reason : PIR.Stop) (state : State carriers) :
    fold routing ((PIR.Process.halt reason : PIR.Process
      (Zkc.Source.Structured.participantInterfaceOn carriers) A).interpret
        Zkc.Source.Structured.Occurrence.actions) state = .halt reason := rfl

end Zkc.Construction.Original

public meta section
namespace Zkc.Construction.Original
open Lean Meta Simp

/-- Do not normalize an unreached reply continuation. The simulation call
constructor introduces its reply before the next normalization pass. -/
simproc_decl stopAtCall (PIR.Process.call _ _) := fun expression =>
  return .done { expr := expression }

end Zkc.Construction.Original
