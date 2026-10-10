import Zkc.Probability.Iteration
import Zkc.Semantics.Iteration
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace Tests.IterationProbability
open Zkc.Probability.Iteration PIR

def record (_ : Unit) (coin : Bool) : Execution Nat Nat Bool :=
  if coin then ⟨.stopped .reject, 2, [8]⟩ else ⟨.returned true, 1, [7]⟩
def view (_ : Unit) (result : Execution Nat Nat Bool) : Bool :=
  match result.outcome with | .stopped _ => true | .returned _ => false

example : transitionMass (fun (_ : Unit) => 1) (fun _ (_ : Bool) => 1/2)
    record view true = 1/2 := by norm_num [transitionMass, record, view, Fintype.univ_bool]
example : transitionMass (fun (_ : Unit) => 1) (fun _ (_ : Bool) => 1/2)
    record view false = 1/2 := by norm_num [transitionMass, record, view, Fintype.univ_bool]

namespace PersistentCoin

abbrev effects : Signature := ⟨Unit, fun _ => Bool⟩
def handler : Handler effects (Bool × Nat) Bool := fun _ state =>
  ⟨.returned state.1, (state.1, state.2 + 1), [state.1]⟩
def body (_ : Unit) : Proc effects (Unit ⊕ Unit) :=
  .call () fun retry => .done (if retry then .inl () else .inr ())
def execute (fuel : Nat) (coin : Bool) :=
  PIR.Iteration.evaluate body handler fuel () (coin, 0)
def pending (result : Execution (Bool × Nat) Bool (Unit ⊕ Unit)) : Bool :=
  match result.outcome with | .returned (.inl _) => true | _ => false
def pendingMass (fuel : Nat) : ℚ := ∑ coin : Bool, if pending (execute fuel coin) then 1/2 else 0

theorem retrying (fuel count : Nat) :
    (PIR.Iteration.evaluate body handler fuel () (true, count)).outcome = .returned (.inl ()) := by
  induction fuel generalizing count with
  | zero => rfl
  | succ fuel ih => simpa [PIR.Iteration.evaluate, PIR.Iteration.approximate,
      body, Proc.bind, Proc.run, handler, Execution.follow] using ih (count + 1)

theorem accepted (fuel count : Nat) :
    (PIR.Iteration.evaluate body handler (fuel + 1) () (false, count)).outcome = .returned (.inr ()) := by
  simp [PIR.Iteration.evaluate, PIR.Iteration.approximate, body,
    Proc.bind, Proc.run, handler, Execution.follow]

/-- The same hidden fair bit is retained through every actual body execution.
Every positive-horizon pending mass is 1/2, not a power of its marginal. -/
theorem persistent_mass (fuel : Nat) : pendingMass (fuel + 1) = 1/2 := by
  simp [pendingMass, Fintype.univ_bool, pending, execute, retrying, accepted]
example : pendingMass 5 > (1/2 : ℚ)^5 := by
  rw [show 5 = 4 + 1 from rfl, persistent_mass]
  norm_num
example : ¬ pendingMass 2 ≤ (1/2 : ℚ) * pendingMass 1 := by
  rw [show 2 = 1 + 1 from rfl, persistent_mass, show 1 = 0 + 1 from rfl, persistent_mass]
  norm_num

/-- Forgetting the coin produces the same current Unit view in both worlds,
but it cannot determine the next pending distribution for both point masses. -/
def nextMass (coin : Bool) : Bool → ℚ := transitionMass
  (fun x : Bool => if x = coin then 1 else 0) (fun _ (_ : Unit) => 1)
  (fun x _ => execute 1 x) (fun _ => pending)
example : ¬ ∃ kernel : Unit → Bool → ℚ, ∀ coin, kernel () true = nextMass coin true := by
  rintro ⟨kernel, law⟩
  have h : nextMass false true = nextMass true true := (law false).symm.trans (law true)
  simp [nextMass, transitionMass, Fintype.univ_bool, execute, pending, retrying, accepted] at h

end PersistentCoin

/-- Canonical F3 representatives acting on an order-two group are not a
field-module action. Cofactor/subgroup evidence cannot be inferred from an API. -/
example : (((2 + 1) % 3) * 1) % 2 ≠ ((2 * 1) % 2 + (1 * 1) % 2) % 2 := by decide

/-- Storage size is not ordered-axis meaning: 2x+y and x+2y differ. -/
example : 2 * 2 + 3 ≠ 2 + 2 * 3 := by decide

end Tests.IterationProbability
