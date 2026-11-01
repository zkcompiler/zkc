import ZkcSecurityExamples.Gkr.HonestLineSource
import TestsSecurity.GkrHonestLineMath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace TestsSecurity.GkrHonestLine
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open ZkcExamples.Structured.PrimitiveLibrary
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows LineCoefficients
open ZkcSecurity.Realizations.Gkr
open _root_.Polynomial

theorem actual_quadratic :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [0, 0] (.cons [1, 1] (.cons 2 .nil)))) =
        .done (.cons [1, 3, 4] .nil) := by
  rw [HonestLine.coefficients_correspond 2 cubeValues [0, 0] [1, 1] cubeTable decoded
    rfl rfl (by norm_num [indexLimit]), quadratic_line]
  norm_num [row, List.range_succ, coeff_add, coeff_mul_X, coeff_X_pow, coeff_one]

/-- Changing the highest coefficient changes the actual returned packet. -/
theorem changed_highest :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [0, 0] (.cons [1, 1] (.cons 2 .nil)))) ≠
        .done (.cons [1, 3, 5] .nil) := by
  rw [actual_quadratic]
  intro wrong
  have coefficients := congrArg (fun xs => xs.get .here) (PIR.Process.done.inj wrong)
  norm_num [Values.get] at coefficients

theorem actual_translated :
    invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
      GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [2, 3] (.cons [5, 7] (.cons 2 .nil)))) =
        .done (.cons [32, 78, 48] .nil) := by
  rw [HonestLine.coefficients_plain 2 cubeValues [2, 3] [5, 7] cubeTable decoded
    rfl rfl (by norm_num [indexLimit]), translated_line]
  norm_num [row, List.range_succ, coeff_add, coeff_mul_X, coeff_X_pow]

/-- The width-zero loop really performs no contraction. -/
theorem actual_scalar :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons [7] (.cons [] (.cons [] (.cons 0 .nil)))) = .done (.cons [7] .nil) := by
  rw [HonestLine.line_coefficients (F := ℚ) [7] [] [] 0 rfl
    (by norm_num [indexLimit]) (by norm_num [indexLimit]) (by norm_num [indexLimit])]
  simp [row_constant]

/-- A checked map refuses unequal rows before invoking any scalar callback. -/
theorem unequal_slope_rows :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.scopedHelper70Helper
      (.cons [1, 2] (.cons [3] (.cons 4 .nil))) = .halt .refused := by
  rw [HonestLine.scopedHelper70_association.invoke GkrSourceViews.unit.linked]
  named_equation HonestLine.Goals.Slopes over ℚ ℚ
  have stopped : Evaluation.denoteCollect (helpers (F := ℚ) (G := ℚ)) HonestLine.slopeCollection
      (.cons ([1, 2] : List ℚ) (.cons [3] (.cons 4 .nil))) = .halt .refused :=
    Evaluation.denoteCollect_admission_stop (carriers := uniformCarriers ℚ ℚ)
      (helpers (F := ℚ) (G := ℚ)) HonestLine.slopeCollection
      ((.cons [1, 2] (.cons [3] .nil)) :
        Values (assignment ℚ ℚ) [.vector "bls12-381.fr", .vector "bls12-381.fr"])
      (.cons (4 : ℚ) .nil) .refused
      (by rfl)
  rw [stopped]
  rfl

/-- Every field point is covered by the full actual helper specification. -/
theorem actual_all_points :
    ∃ coefficients : List ℚ,
      invoke (plainHelpers (F := ℚ) (G := ℚ) GkrSourceViews.unit).closed
        GkrSourceBodies.helper69Helper
        (.cons cubeValues (.cons [2, 3] (.cons [5, 7] (.cons 2 .nil)))) =
          .done (.cons coefficients .nil) ∧
      coefficients.length = 3 ∧
      coefficientPolynomial coefficients =
        linePolynomial 2 cubeTable (coordinates 2 [2, 3]) (coordinates 2 [5, 7]) ∧
      ∀ t : ℚ, powerSum coefficients t =
        extension 2 cubeTable (linePoint (coordinates 2 [2, 3]) (coordinates 2 [5, 7]) t) :=
  HonestLine.actual_line_polynomial 2 cubeValues [2, 3] [5, 7] cubeTable decoded rfl rfl
    (by norm_num [indexLimit])

#print axioms HonestLine.constant_rows
#print axioms HonestLine.shift_rows
#print axioms HonestLine.loop_invariant
#print axioms HonestLine.coefficients_correspond
#print axioms HonestLine.coefficients_plain
#print axioms HonestLine.actual_line_polynomial
#print axioms CoefficientRows.coefficientPolynomial_row
#print axioms LineCoefficients.stage_degree
#print axioms LineCoefficients.slope_top_zero
#print axioms LineCoefficients.stage_complete
#print axioms actual_quadratic
#print axioms changed_highest
#print axioms unequal_slope_rows

end TestsSecurity.GkrHonestLine
