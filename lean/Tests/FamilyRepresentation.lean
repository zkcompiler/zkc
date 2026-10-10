import Zkc.Realization.Family

set_option autoImplicit false
namespace Tests.FamilyRepresentation
open PIR
open Zkc.Source

namespace EntryPhase

abbrev effects : Signature := ⟨Unit, fun _ => Unit⟩
def interaction : Interaction effects :=
  ⟨Unit, Bool, fun _ => (), fun phase _ => phase = false, fun _ _ _ => true⟩
def member (_ : Unit) (_ : Unit) : Proc effects Unit := .call () fun _ => .done ()
def contract (_ : Unit) (_ : Unit) : EndpointContract interaction Unit :=
  ⟨false, 1, fun _ phase => phase = true⟩
def allowed (_ : Unit) (_ : Unit) : Prop := True
def ingress (phase : Bool) (_ : Unit) (_ : Bool) :
    Execution Bool Bool (Sigma (fun _ : Unit => Unit)) :=
  ⟨.returned ⟨(), ()⟩, phase, [phase]⟩
def handler : Handler effects Bool Bool := fun _ phase =>
  if phase then ⟨.stopped .refused, phase, []⟩ else ⟨.returned (), true, []⟩

theorem admitted : Family.Admitted interaction member contract allowed where
  conforms _ _ _ := ⟨rfl, fun _ => trivial⟩
  bounded _ _ _ := fun _ => trivial
  returned _ _ _ := fun _ => rfl

theorem selects (phase : Bool) :
    Family.Selects (ingress phase) (fun _ _ => True) allowed := fun _ _ _ _ _ => trivial

/-- Valid inputs and member admission do not establish compatibility with the
actual phase after ingress. Here the very first operation is disabled. -/
example : ¬ Conforms interaction (member () ()) (ingress true () false).state := by
  intro h
  have bad : true = false := h.1
  contradiction
example : (Family.run (ingress true) member handler () false).outcome = .stopped .refused := rfl

example : Conforms interaction (member () ()) (ingress false () true).state :=
  (admitted.selected_at interaction member contract allowed (ingress false)
    (fun _ _ => True) (selects false) () true ⟨(), ()⟩ trivial rfl id rfl).1
example : (Family.run (ingress false) member handler () true).outcome = .returned () := rfl

def ready (_ : Sigma (fun _ : Unit => Unit)) (phase : Bool) : Prop := phase = false
theorem established : Family.SelectsReady (ingress false) (fun _ _ => True) ready :=
  fun _ _ _ _ _ => rfl

/-- Readiness is established for the whole ingress domain, rather than supplied
as an independently chosen phase for each member. -/
example (state : Bool) : Conforms interaction (member () ()) (ingress false () state).state :=
  (admitted.selected_ready interaction member contract allowed (ingress false)
    (fun _ _ => True) ready established id (fun _ _ _ => trivial)
    (fun _ _ h => h.symm) () state ⟨(), ()⟩ trivial rfl).2.1

example : ¬ Family.SelectsReady (ingress true) (fun _ _ => True) ready := by
  intro h
  have impossible : true = false := h () false ⟨(), ()⟩ trivial rfl
  contradiction

end EntryPhase

namespace StoredInput

abbrev effects : Signature := ⟨Unit, fun _ => Nat⟩
def ingress (raw state : Nat) : Execution Nat Nat (Sigma (fun _ : Nat => Unit)) :=
  ⟨.returned ⟨raw, ()⟩, state + 1, [9]⟩
def otherIngress (raw : Nat) (state : Nat × Nat) :
    Execution (Nat × Nat) Nat (Sigma (fun _ : Unit => Unit)) :=
  ⟨.returned ⟨(), ()⟩, (state.1 + 1, raw), [9]⟩
def member (count : Nat) (_ : Unit) : Proc effects Nat := .done count
def other (_ : Unit) (_ : Unit) : Proc effects Nat := .call () Proc.done
def left : Handler effects Nat Nat := fun _ s => ⟨.returned s, s, []⟩
def right : Handler effects (Nat × Nat) Nat := fun _ t => ⟨.returned t.2, t, []⟩
def states (s : Nat) (t : Nat × Nat) : Prop := s = t.1
def inputs (bound : Sigma (fun _ : Nat => Unit)) (_ : Nat)
    (_ : Sigma (fun _ : Unit => Unit)) (t : Nat × Nat) : Prop := bound.1 = t.2

/-- The native family obtains its logical input through actual ingress state,
not a common configuration value supplied outside the execution. -/
theorem represented (raw state : Nat) :
    Execution.Relates states (fun a _ b _ => a = b) List.singleton List.singleton
      (Family.run ingress member left raw state)
      (Family.run otherIngress other right raw (state, 0)) := by
  apply Zkc.Realization.Family.run_relates ingress otherIngress member other left right
    states inputs (fun a _ b _ => a = b) List.singleton List.singleton
    raw state raw (state, 0)
  · exact ⟨rfl, rfl, rfl⟩
  · intro bound s otherBound t hs hv
    exact ⟨hv, hs, rfl⟩

/-- Dropping ingress's effects changes the complete execution even when the
selected source member and its successful return value remain the same. -/
example : (Family.run ingress member left 3 0).outcome = ((member 3 ()).run left 0).outcome := rfl
example : (Family.run ingress member left 3 0).state ≠ ((member 3 ()).run left 0).state := by decide
example : (Family.run ingress member left 3 0).events ≠ ((member 3 ()).run left 0).events := by decide

end StoredInput

namespace DependentInputs

abbrev effects : Signature := ⟨Nat, fun _ => Nat⟩
abbrev Inputs (count : Nat) := Fin count → Nat
def ingress (raw : List Nat) (state : Nat) : Execution Nat Nat (Sigma Inputs) :=
  if raw.length ≤ 3 then
    ⟨.returned ⟨raw.length, fun i => raw[i]⟩, state + 1, [raw.length]⟩
  else ⟨.stopped .refused, state + 1, [raw.length]⟩
def member (count : Nat) (inputs : Inputs count) : Proc effects Nat :=
  .call count fun bias => .done ((List.ofFn inputs).foldl (· + ·) bias)
def handler : Handler effects Nat Nat := fun count state =>
  ⟨.returned state, state + count, [count]⟩
def run (raw : List Nat) := Family.run ingress member handler raw 10

/-- Configuration selects the input type; actual input values, residual state
and ingress observations all reach the member. -/
example : (run [3, 7]).outcome = .returned 21 := by decide
example : (run [3, 8]).outcome = .returned 22 := by decide
example : (run [3, 7]).state = 13 := rfl
example : (run [3, 7]).events = [2, 2] := rfl
example : (run []).outcome = .returned 11 := rfl
example : (run [1, 2, 3, 4]).outcome = .stopped .refused := rfl
example : (run [1, 2, 3, 4]).state = 11 := rfl
example : (run [1, 2, 3, 4]).events = [4] := rfl

end DependentInputs
end Tests.FamilyRepresentation
