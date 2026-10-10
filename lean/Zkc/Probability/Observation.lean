import Mathlib.Logic.Equiv.Defs

/-! Observation fibers under an explicit change of sample representation.

An equivalence preserving the chosen observation induces an equivalence of its
fibers. A probability argument additionally supplies its sampling law; this
construction alone assumes neither uniformity nor finite sample spaces.
-/

set_option autoImplicit false

namespace Zkc.Probability.Observation

universe u v w

def fiberEquiv {A : Type u} {B : Type v} {O : Type w}
    (e : A ≃ B) (f : A → O) (g : B → O) (agrees : ∀ a, f a = g (e a))
    (observed : O) : {a : A // f a = observed} ≃ {b : B // g b = observed} where
  toFun a := ⟨e a, by rw [← agrees]; exact a.property⟩
  invFun b := ⟨e.symm b, by rw [agrees, e.apply_symm_apply]; exact b.property⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv b := by apply Subtype.ext; simp

end Zkc.Probability.Observation
