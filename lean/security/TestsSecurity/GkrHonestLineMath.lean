import Zkc.Polynomial.Multilinear.LineCoefficients

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace TestsSecurity.GkrHonestLine
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows LineCoefficients
open _root_.Polynomial

def cubeValues : List ℚ := [1, 2, 3, 8]

def cubeTable : Table ℚ 2 := ofVector (fun i => cubeValues[i.val]'(by
  simp [cubeValues]))

theorem decoded : ofList? 2 cubeValues = some cubeTable := rfl

/-- Both coordinates vary. The independent line polynomial has degree two. -/
theorem quadratic_line :
    linePolynomial 2 cubeTable (coordinates 2 [0, 0]) (coordinates 2 [1, 1]) =
      C 1 + C 3 * X + C 4 * X ^ 2 := by
  simp [linePolynomial, cubeTable, cubeValues, ofVector, half, index, coordinates, Polynomial.C_ofNat]
  ring

/-- Non-Boolean start and finish exercise both interpolation and slope. -/
theorem translated_line :
    linePolynomial 2 cubeTable (coordinates 2 [2, 3]) (coordinates 2 [5, 7]) =
      C 32 + C 78 * X + C 48 * X ^ 2 := by
  simp [linePolynomial, cubeTable, cubeValues, ofVector, half, index, coordinates, Polynomial.C_ofNat]
  ring

/-- A row boundary resets the previous row's final coefficient. -/
theorem row_boundary : shiftAux 3 0 (0 : ℚ) [2, 4, 0, 7, 9, 0] = [0, 2, 4, 0, 7, 9] := by
  norm_num [shiftAux]
end TestsSecurity.GkrHonestLine
