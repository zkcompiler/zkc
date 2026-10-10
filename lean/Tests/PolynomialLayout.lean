import Zkc.Polynomial.Layout
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Tests.PolynomialLayout

open Zkc.Polynomial

def values : Fin (2 ^ 2) → ZMod 5 := fun i => i.val
def point : Fin 2 → ZMod 5 := ![0, 1]

/-- Omitting bit reversal changes the original subject at the same point. -/
theorem omitted_permutation_changes_value :
    Multilinear.extension 2 (Multilinear.ofVector values) point = 1 ∧
    Multilinear.extension 2 (Layout.ofLowStorage values) point = 2 := by
  decide +kernel

theorem permuted_storage_keeps_point :
    Multilinear.extension 2 (Layout.ofLowStorage (Layout.toLowStorage values)) point = 1 := by
  rw [Layout.extension_eq]
  decide +kernel

/-- Reversing the query after converting storage applies a second, wrong change. -/
theorem reversing_point_changes_value :
    Multilinear.extension 2 (Layout.ofLowStorage (Layout.toLowStorage values)) (point ∘ Fin.rev) = 2 := by
  rw [Layout.extension_eq]
  decide +kernel

def linearTable : Multilinear.Table (ZMod 5) 1 := Multilinear.ofVector (fun i => i.val)

/-- Multiplying Boolean values before extension loses the degree-two product. -/
theorem collapsing_product_changes_nonboolean_value :
    (Multilinear.productCoefficients 1 linearTable linearTable).eval (fun _ => 2) = 4 ∧
    Multilinear.extension 1 (fun bits => linearTable bits * linearTable bits) (fun _ => 2) = 2 := by
  decide +kernel

theorem zero_arity_storage (values : Fin (2 ^ 0) → ZMod 5) :
    Layout.toLowStorage values = values := by
  funext i
  exact congrArg values (@Subsingleton.elim (Fin 1) inferInstance _ _)

end Tests.PolynomialLayout
