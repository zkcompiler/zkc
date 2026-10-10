import Mathlib.Algebra.BigOperators.Fin

/-! Summation over an ordered Boolean cube, independent of a polynomial
representation or protocol execution. The first coordinate is split first. -/

set_option autoImplicit false

namespace Zkc.Polynomial

variable {F : Type}

def cubeSum [Zero F] [One F] [Add F] : (n : Nat) → ((Fin n → F) → F) → F
  | 0, f => f Fin.elim0
  | n + 1, f =>
      cubeSum n (fun tail => f (Fin.cons 0 tail)) +
      cubeSum n (fun tail => f (Fin.cons 1 tail))

variable [CommSemiring F]

theorem cubeSum_add (n : Nat) (f g : (Fin n → F) → F) :
    cubeSum n (fun point => f point + g point) = cubeSum n f + cubeSum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cubeSum, ih]; ac_rfl

theorem cubeSum_scale (n : Nat) (c : F) (f : (Fin n → F) → F) :
    cubeSum n (fun point => c * f point) = c * cubeSum n f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [cubeSum, ih, mul_add]

end Zkc.Polynomial
