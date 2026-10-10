import Zkc.Probability.Observation
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Fintype.Prod


set_option autoImplicit false
namespace Zkc.Probability.AdaptiveTape

def Tape (F : Type) : Nat → Type
  | 0 => Unit
  | n+1 => F × Tape F n

instance {F : Type} [Fintype F] (n : Nat) : Fintype (Tape F n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI : Fintype (Tape F n) := ih
    exact inferInstanceAs (Fintype (F × Tape F n))

instance {F : Type} [DecidableEq F] (n : Nat) : DecidableEq (Tape F n) := by
  induction n with
  | zero => exact inferInstanceAs (DecidableEq Unit)
  | succ n ih =>
    letI : DecidableEq (Tape F n) := ih
    exact inferInstanceAs (DecidableEq (F × Tape F n))

/-- The tail transformation may depend on the transformed head. -/
def skew {X Y : Type} (head : X ≃ X) (tail : X → Y ≃ Y) : X × Y ≃ X × Y where
  toFun r := (head r.1,tail (head r.1) r.2)
  invFun r := (head.symm r.1,(tail r.1).symm r.2)
  left_inv r := by simp
  right_inv r := by simp

def run {F H : Type} (step : H → F → H) : (n : Nat) → H → Tape F n → H
  | 0,h,_ => h
  | n+1,h,r => run step n (step h r.1) r.2

/-- A finite triangular coupling. No future coin can enter `change h`. -/
def coins {F H : Type} (right : H → F → H) (change : H → F ≃ F) :
    (n : Nat) → H → Tape F n ≃ Tape F n
  | 0,_ => Equiv.refl Unit
  | n+1,h => skew (change h) (fun z => coins right change n (right h z))

theorem adaptive_coupling {F H : Type} (left right : H → F → H)
    (change : H → F ≃ F) (law : ∀ h r, left h r = right h (change h r))
    (n : Nat) (h : H) (r : Tape F n) :
    run left n h r = run right n h (coins right change n h r) := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    change run left n (left h r.1) r.2 =
      run right n (right h (change h r.1))
        (coins right change n (right h (change h r.1)) r.2)
    rw [law h r.1]
    exact ih _ _

theorem adaptive_mass {F H : Type} [Fintype F] [DecidableEq H]
    (left right : H → F → H) (change : H → F ≃ F)
    (law : ∀ h r, left h r = right h (change h r))
    (n : Nat) (h out : H) :
    (Fintype.card {r : Tape F n // run left n h r = out} : ℚ) / Fintype.card (Tape F n) =
    (Fintype.card {r : Tape F n // run right n h r = out} : ℚ) / Fintype.card (Tape F n) := by
  rw [Fintype.card_congr (Zkc.Probability.Observation.fiberEquiv (coins right change n h)
    (run left n h) (run right n h) (adaptive_coupling left right change law n h) out)]

theorem run_congr {F H : Type} (left right : H → F → H)
    (law : ∀ h r, left h r = right h r) (n : Nat) (h : H) (r : Tape F n) :
    run left n h r = run right n h r := by
  have eq : left = right := funext (fun h => funext (law h))
  rw [eq]

end Zkc.Probability.AdaptiveTape
