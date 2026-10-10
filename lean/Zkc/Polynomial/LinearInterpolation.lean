import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false

namespace Zkc.Polynomial.LinearInterpolation
open scoped BigOperators

-- Honest Plan refinement only; this is deliberately not LegalMessage.
def foldAt {F : Type} [CommRing F] {n : Nat}
    (r : F) (lo hi : Fin n → F) (i : Fin n) := (1-r)*lo i + r*hi i

theorem honest_endpoint_interpretation {F : Type} [CommRing F] {n : Nat}
    (lo hi : Fin n → F) (a b r : F)
    (ha : a = ∑ i, lo i) (hb : b = ∑ i, hi i) :
    (1-r)*a+r*b = ∑ i, foldAt r lo hi i := by
  rw [ha, hb]
  simp only [foldAt, Finset.sum_add_distrib, ← Finset.mul_sum]

end Zkc.Polynomial.LinearInterpolation
