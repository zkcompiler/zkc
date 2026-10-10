import Zkc.Algebra.LinearCombination
import Zkc.Protocols.InnerProduct.Folding
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Tests.LinearCombination

open Zkc.Algebra
open scoped Matrix

private def matrix : Matrix (Fin 2) (Fin 2) (ZMod 101) :=
  fun i j => if i = 0 then (if j = 0 then 1 else 2) else (if j = 0 then 3 else 4)
private def weights : Fin 2 → ZMod 101 := fun i => if i = 0 then 5 else 7
private def scalars : Fin 2 → ZMod 101 := fun i => if i = 0 then 11 else 13
private def points : Fin 2 → ZMod 101 × ZMod 101 :=
  fun i => if i = 0 then (11, 17) else (13, 19)

example : linearCombination weights (fun i => linearCombination (matrix i) scalars) =
    linearCombination (weights ᵥ* matrix) scalars :=
  linearCombination_rows matrix weights scalars

example : linearCombination weights (fun i => linearCombination (matrix i) points) =
    linearCombination (weights ᵥ* matrix) points :=
  linearCombination_rows matrix weights points

-- A nonsymmetric map distinguishes pullback from another forward application.
example : linearCombination weights (fun i => linearCombination (matrix i) scalars) ≠
    linearCombination (matrix *ᵥ weights) scalars := by native_decide

example : linearCombination weights (fun i => linearCombination (matrix i) points) ≠
    linearCombination (matrix *ᵥ weights) points := by native_decide

-- Zero challenges cannot be admitted by the folding theorem.
example :
    ((0 : ZMod 101) * 1 + (0 : ZMod 101)⁻¹ * 3) *
      ((0 : ZMod 101)⁻¹ * 2 + (0 : ZMod 101) * 4) ≠
    (1 : ZMod 101) * 2 + (3 : ZMod 101) * 4 := by native_decide

end Tests.LinearCombination
