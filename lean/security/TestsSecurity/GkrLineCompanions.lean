import ZkcSecurityExamples.Gkr.HonestLineSource
import TestsSecurity.GkrHonestLineMath

/-! Focused source association, complete output and refusal controls for the
line companion closure. No canonical GKR root or full build is required. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
noncomputable section
namespace TestsSecurity.GkrLineCompanions
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows LineCoefficients
open ZkcSecurity.Realizations.Gkr.HonestLine
open TestsSecurity.GkrHonestLine
open _root_.Polynomial

private abbrev model := ringModel ℚ ℚ

/-- The complete selected source callback advances its cursor and preserves
all captures, including coordinates beyond the current position. -/
theorem complete_callback :
    Goals.Step.body.denote (Evaluation.meaningOn model SiteObservations.closed (helpers (F := ℚ) (G := ℚ)))
      (Goals.Step.Inputs.pack
        { iteration := 0, values := [1, 0, 3, 0], position := 0,
          start := [0, 7], finish := [1, 11], count := 2 }).get =
      .done (Goals.Step.encode model
        { values := [1, 2], position := 1, start := [0, 7], finish := [1, 11], count := 2 }) := by
  have actual := loop_step (F := ℚ) (G := ℚ) 0 [1, 0, 3, 0] [0, 7] [1, 11] 0 2 2
    rfl (by decide) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide)
  norm_num [step, linePoints, shiftAux] at actual ⊢
  exact actual

private def changedCallback : Region dialect Goals.Step.Inputs.types
    (Goals.LineState.types ++ Goals.LineCaptures.types) := .stop .abort

theorem changed_callback_rejected : changedCallback ≠ Goals.Step.body := by
  intro same
  have changed := complete_callback
  rw [← same] at changed
  cases changed

/-- An unchanged source name and ABI cannot associate an altered implementation. -/
private def changedLine : CheckedDefinition :=
  ⟨GkrSourceBodies.helper69Helper.name, GkrSourceBodies.helper69Helper.kind,
    GkrSourceBodies.helper69Helper.inputs, GkrSourceBodies.helper69Helper.outputs,
    (.stop .abort : Region dialect _ _).erase, .stop .abort,
    (Region.stop .abort : Region dialect _ _).elaborate_erase⟩

theorem changed_line_not_associated :
    ¬ BodyIn [changedLine] GkrSourceBodies.helper69Helper Goals.Line.body := by
  rintro ⟨selected, member, signature, same⟩
  simp only [List.mem_singleton] at member
  subst selected
  cases same

/-- The source-selected callback association is checked independently of its math. -/
example : HelperCallbacks.Selected GkrSourceBodies.helper69Body none Goals.lineCallback_selection :=
  Goals.lineCallback_association

/-- Every returned coordinate matters, even when the coefficient list is right. -/
theorem wrong_cursor_rejected :
    Goals.Step.body.denote (Evaluation.meaningOn model SiteObservations.closed (helpers (F := ℚ) (G := ℚ)))
      (Goals.Step.Inputs.pack
        { iteration := 0, values := [1, 0, 3, 0], position := 0,
          start := [0, 7], finish := [1, 11], count := 2 }).get ≠
      .done (Goals.Step.encode model
        { values := [1, 2], position := 0, start := [0, 7], finish := [1, 11], count := 2 }) := by
  rw [complete_callback]
  intro wrong
  have impossible : (1 : Nat) = 0 :=
    congrArg (fun result => (Goals.Step.decode model result).position) (PIR.Process.done.inj wrong)
  omega

/-- The finite shift law retains the complete previous-value/cursor state. -/
example : invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.scopedHelper86Helper
    (Goals.ShiftDomain.pack ⟨[2, 4, 0, 7, 9, 0]⟩ |>.append
      ((Goals.ShiftState.pack ⟨[13], 17, 0⟩).append (Goals.ShiftCaptures.pack ⟨3⟩))) =
      .done (Goals.ShiftState.pack ⟨[13, 0, 2, 4, 0, 7, 9], 0, 6⟩) := by
  have actual := shift_fold (F := ℚ) (G := ℚ) [2, 4, 0, 7, 9, 0] [13] 17 0 3
    (by decide +kernel) (by decide +kernel) (by decide)
  norm_num [shiftAux] at actual ⊢
  exact actual

/-- Strict zip refusal occurs before the scalar callback, for any table. -/
example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.Slopes.body.denote (Evaluation.meaningOn model SiteObservations.closed table)
      (Goals.Slopes.Inputs.pack { left := [1, 2], right := [3], delta := 4 }).get =
      .halt .refused := by
  simp only [Goals.Slopes.Inputs.pack]
  rw [Goals.Slopes.equation model]
  rfl

/-- The full generated shift-step equation retains division-by-zero refusal. -/
example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.ShiftStep.run model table [] 7 0 11 0 = .halt .refused := by rfl

/-- Reached increment overflow is refused; it is not an exhausted domain. -/
example (table : Evaluation.MeaningsOn model.toCarriers closedInterface) :
    Goals.ShiftStep.run model table [] 7 (indexLimit - 1) 11 2 = .halt .refused := by rfl

private def stoppingZero (reason : PIR.Stop) :
    Evaluation.MeaningsOn model.toCarriers closedInterface :=
  [⟨GkrSourceBodies.scopedHelper74Helper, fun _ => .halt reason⟩]

/-- Every dependency stop reason survives the reached row-boundary callback. -/
example (reason : PIR.Stop) :
    Goals.ShiftStep.run model (stoppingZero reason) [] 7 0 11 3 = .halt reason := by rfl

theorem actual_quadratic :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [0, 0] (.cons [1, 1] (.cons 2 .nil)))) =
        .done (.cons [1, 3, 4] .nil) := by
  rw [coefficients_correspond 2 cubeValues [0, 0] [1, 1] cubeTable decoded
    rfl rfl (by norm_num [indexLimit]), quadratic_line]
  norm_num [row, List.range_succ, coeff_add, coeff_mul_X, coeff_X_pow, coeff_one]

theorem wrong_highest_rejected :
    invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
      (.cons cubeValues (.cons [0, 0] (.cons [1, 1] (.cons 2 .nil)))) ≠
        .done (.cons [1, 3, 5] .nil) := by
  rw [actual_quadratic]
  intro wrong
  have impossible : ([1, 3, 4] : List ℚ) = [1, 3, 5] :=
    congrArg (fun result => (Goals.Line.decode model result).coefficients) (PIR.Process.done.inj wrong)
  norm_num at impossible

/-- Empty counted contraction retains the scalar coefficient. -/
example : invoke (helpers (F := ℚ) (G := ℚ)) GkrSourceBodies.helper69Helper
    (.cons [7] (.cons [] (.cons [] (.cons 0 .nil)))) = .done (.cons [7] .nil) := by
  rw [line_coefficients (F := ℚ) [7] [] [] 0 rfl (by decide +kernel)
    (by decide +kernel) (by decide +kernel)]
  simp [row_constant]

#print axioms Goals.Step.equation
#print axioms Goals.lineCallback_association
#print axioms Companion.installScalars
#print axioms Companion.shift_fold
#print axioms loop_invariant
#print axioms coefficients_correspond
#print axioms actual_line_polynomial
#print axioms complete_callback
#print axioms changed_callback_rejected
#print axioms changed_line_not_associated
#print axioms wrong_cursor_rejected
#print axioms wrong_highest_rejected
end TestsSecurity.GkrLineCompanions
