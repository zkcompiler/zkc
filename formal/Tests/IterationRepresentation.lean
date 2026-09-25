import Zkc.Realization.Iteration

set_option autoImplicit false
namespace Tests.IterationRepresentation
open PIR
open Zkc.Realization.Iteration

abbrev logical : Signature := ⟨Unit, fun _ => Unit⟩
abbrev native : Signature := ⟨Unit, fun _ => Nat⟩

def body (remaining : Nat) : Proc logical (Nat ⊕ Nat) :=
  .call () fun _ => if remaining = 0 then .done (.inr 0) else .done (.inl (remaining - 1))

/-- The represented controller carries no count value: its count is in the
actual handler state, and the reply reports the value before decrement. -/
def other (_ : Unit) : Proc native (Unit ⊕ Unit) :=
  .call () fun remaining =>
    if remaining = 0 then .done (.inr ()) else .done (.inl ())

def left : Handler logical Nat Nat := fun _ s => ⟨.returned (), s + 1, [s]⟩
def right : Handler native (Nat × Nat) Nat := fun _ t =>
  ⟨.returned t.2, (t.1 + 1, t.2 - 1), [t.1]⟩
def states (s : Nat) (t : Nat × Nat) : Prop := s = t.1
def counts (c : Nat) (_ : Nat) (_ : Unit) (t : Nat × Nat) : Prop := c = t.2

theorem step (c s : Nat) (d : Unit) (t : Nat × Nat)
    (initial : states s t) (seed : counts c s d t) :
    Execution.Relates states (ResultRel counts counts) List.singleton List.singleton
      ((body c).run left s) ((other d).run right t) := by
  rcases t with ⟨calls, remaining⟩
  change s = calls at initial
  change c = remaining at seed
  subst s
  subst c
  cases d
  by_cases h : remaining = 0 <;>
    simp only [body, other, Proc.run, left, right, Execution.follow, h, ↓reduceIte]
  · subst remaining
    exact ⟨rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl⟩

/-- This is transport at every horizon, with different continuation and
return types and a genuinely post-state-dependent representation relation. -/
theorem represented (fuel remaining : Nat) :
    Execution.Relates states (ResultRel counts counts) List.singleton List.singleton
      (Iteration.evaluate body left fuel remaining 0)
      (Iteration.evaluate other right fuel () (0, remaining)) :=
  evaluate_relates body other left right states counts counts _ _ step
    fuel remaining 0 () (0, remaining) rfl rfl

example (fuel remaining : Nat) :
    Execution.Relates states counts List.singleton List.singleton
      (Iteration.close (Iteration.evaluate body left fuel remaining 0))
      (Iteration.close (Iteration.evaluate other right fuel () (0, remaining))) :=
  close_relates states counts counts _ _ _ _ (represented fuel remaining)

/-- Equal public counters do not justify an incorrect interpretation of the
hidden remaining count. Such a relation already fails on one pending step. -/
example : ¬ Execution.Relates states
    (ResultRel (fun c (_ : Nat) (_ : Unit) t => c = t.1) counts)
    List.singleton List.singleton
    (Iteration.evaluate body left 1 3 0)
    (Iteration.evaluate other right 1 () (0, 3)) := by
  intro h
  have bad : (2 : Nat) = 1 := h.outcome
  contradiction

end Tests.IterationRepresentation
