import Zkc.Semantics.Iteration

set_option autoImplicit false
namespace Tests.IterationBounds
open PIR

abbrev effects : Signature := ⟨Unit, fun _ => Unit⟩
def interaction : Interaction effects :=
  ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩

def spend : Nat → Nat → Proc effects (Nat ⊕ Unit)
  | 0, next => .done (.inl next)
  | count + 1, next => .call () fun _ => spend count next
def body (count : Nat) := spend count (count / 2)
def invariant (ceiling count : Nat) (_ : Unit) : Prop := count ≤ ceiling

theorem spend_within (bound count next : Nat) :
    Within bound (spend count next) ↔ count ≤ bound := by
  induction bound generalizing count with
  | zero => cases count <;> simp [spend, Within]
  | succ bound ih =>
    cases count <;> simp [spend, Within, ih]

theorem spend_returns (ceiling count next : Nat) (legal : next ≤ ceiling)
    (phase : interaction.Phase) :
    Boundary.Returns interaction (fun answer phase =>
      match answer with | .inl c => invariant ceiling c phase | .inr _ => True)
      (spend count next) phase := by
  induction count generalizing phase with
  | zero => exact legal
  | succ count ih => exact fun _ => ih ()

/-- A single bound covers every continuation admitted by the invariant,
including all typed replies. It need not cover arbitrary Nat seeds. -/
theorem admitted_prefix (ceiling fuel seed : Nat) (legal : seed ≤ ceiling) :
    Within (fuel * ceiling) (Iteration.approximate body fuel seed) := by
  apply Iteration.within_approximate_of_invariant body interaction
    (invariant ceiling) (fun _ _ => True) ceiling (phase := ())
  · intro count phase h
    exact (spend_within ceiling count (count / 2)).mpr h
  · intro count phase h
    apply Boundary.returns_mono interaction _ _ _ phase
      (spend_returns ceiling count (count / 2) (Nat.le_trans (Nat.div_le_self _ _) h) phase)
    intro answer last legal
    cases answer <;> exact legal
  · exact legal

example : ¬ ∃ bound, ∀ seed, Within bound (body seed) := by
  rintro ⟨bound, all⟩
  have impossible := (spend_within bound (bound + 1) ((bound + 1) / 2)).mp (all (bound + 1))
  omega

namespace HostileReply

abbrev effects : Signature := ⟨Unit, fun _ => Nat⟩
def interaction : Interaction effects :=
  ⟨Unit, Unit, fun _ => (), fun _ _ => True, fun _ _ _ => ()⟩
def ticks : Nat → Proc effects Unit
  | 0 => .done ()
  | n + 1 => .call () fun _ => ticks n
def body (count : Nat) : Proc effects (Nat ⊕ Unit) :=
  (ticks count).bind fun _ => .call () fun next => .done (.inl next)
def guarded (ceiling count : Nat) : Proc effects (Nat ⊕ Unit) :=
  (ticks count).bind fun _ => .call () fun next =>
    if next ≤ ceiling then .done (.inl next) else .halt .reject

theorem ticks_bound (count : Nat) : Within count (ticks count) := by
  induction count with
  | zero => trivial
  | succ count ih => exact fun _ => ih

theorem ticks_returns (count : Nat) (post : Unit → interaction.Phase → Prop)
    (holds : post () ()) : Boundary.Returns interaction post (ticks count) () := by
  induction count with
  | zero => exact holds
  | succ count ih => exact fun _ => ih

/-- A single honest execution is tiny; arbitrary typed replies can request
arbitrarily long work on the second step. -/
def honest : Handler effects Nat Nat := fun _ state => ⟨.returned 0, state + 1, [0]⟩
example : (Iteration.evaluate body honest 2 0 0).events = [0, 0] := rfl

theorem ticks_prefix_too_long (bound : Nat) (tail : Unit → Proc effects (Nat ⊕ Unit)) :
    ¬ Within bound ((ticks (bound + 1)).bind tail) := by
  induction bound with
  | zero => exact id
  | succ bound ih => exact fun h => ih (h 0)

example : ¬ ∃ bound, Within bound (Iteration.approximate body 2 0) := by
  rintro ⟨bound, h⟩
  cases bound with
  | zero => exact h
  | succ bound =>
    have next := h (bound + 1)
    change Within bound ((body (bound + 1)).bind _) at next
    rw [body, Proc.bind_assoc] at next
    exact ticks_prefix_too_long bound _ next

def post (ceiling : Nat) : Nat ⊕ Unit → interaction.Phase → Prop
  | .inl next, _ => next ≤ ceiling
  | .inr _, _ => True

example (ceiling : Nat) : ¬ Boundary.Returns interaction (post ceiling) (body 0) () := by
  intro h
  have impossible : ceiling + 1 ≤ ceiling := h (ceiling + 1)
  omega

theorem guarded_returns (ceiling count : Nat) :
    Boundary.Returns interaction (post ceiling) (guarded ceiling count) () := by
  apply Boundary.returns_bind interaction (ticks count) _ (fun _ _ => True)
    (post ceiling) () (ticks_returns count _ trivial)
  intro value phase _
  cases value
  cases phase
  intro next
  dsimp
  split
  next valid => exact valid
  next invalid => trivial

theorem guarded_bound (ceiling fuel seed : Nat) (legal : seed ≤ ceiling) :
    Within (fuel * (ceiling + 1)) (Iteration.approximate (guarded ceiling) fuel seed) := by
  apply Iteration.within_approximate_of_invariant (guarded ceiling) interaction
    (fun count _ => count ≤ ceiling) (fun _ _ => True) (ceiling + 1) (phase := ())
  · intro count phase valid
    apply Boundary.within_mono _ (count + 1) (ceiling + 1) (by omega)
    exact Boundary.within_bind (ticks count) _ count 1 (ticks_bound count)
      (fun _ next => by dsimp; split <;> trivial)
  · intro count phase _
    cases phase
    apply Boundary.returns_mono interaction _ _ _ () (guarded_returns ceiling count)
    intro answer phase valid
    cases answer <;> exact valid
  · exact legal

end HostileReply

namespace PhaseReentry

def interaction : Interaction effects :=
  ⟨Unit, Bool, fun _ => (), fun phase _ => phase = false, fun _ _ _ => true⟩
def body (_ : Unit) : Proc effects (Unit ⊕ Unit) := .call () fun _ => .done (.inl ())
example : Conforms interaction (body ()) false := ⟨rfl, fun _ => trivial⟩
example : ¬ Conforms interaction (Iteration.approximate body 2 ()) false := by
  intro h
  have impossible : true = false := (h.2 ()).1
  contradiction

end PhaseReentry
end Tests.IterationBounds
