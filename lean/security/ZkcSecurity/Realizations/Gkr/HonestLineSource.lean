module

public import ZkcSecurity.Realizations.Gkr.HonestLine
public import ZkcSecurity.Realizations.Gkr.HonestHelpersSource

@[expose] public section

/-! Exact transport to the helper table used by the source normal forms. -/

namespace ZkcSecurity.Realizations.Gkr.HonestLine
open Zkc Source Structured
open ZkcExamples.Structured GkrSourceLaws SumcheckVerifierHelpers
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The actual source participant uses this exact closed helper table. -/
theorem coefficients_plain (width : Nat) (values start finish : List F)
    (table : Table F width) (decoded : ofList? width values = some table)
    (startSize : start.length = width) (finishSize : finish.length = width)
    (capacity : 2 ^ width * (width + 1) < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
      GkrSourceBodies.helper69Helper
      (.cons values (.cons start (.cons finish (.cons width .nil)))) =
      .done (.cons (row (width + 1)
        (linePolynomial width table (coordinates width start) (coordinates width finish))) .nil) := by
  rw [closed_invoke_plain]
  change (invoke (helpers (G := G)) GkrSourceBodies.helper69Helper _).interpret _ = _
  rw [coefficients_correspond width values start finish table decoded startSize finishSize capacity]
  rfl

/-- A complete reusable result for the actual helper: exact output, exact
length, polynomial equality and evaluation at every field point. -/
theorem actual_line_polynomial (width : Nat) (values start finish : List F)
    (table : Table F width) (decoded : ofList? width values = some table)
    (startSize : start.length = width) (finishSize : finish.length = width)
    (capacity : 2 ^ width * (width + 1) < indexLimit) :
    ∃ coefficients : List F,
      invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
        GkrSourceBodies.helper69Helper
        (.cons values (.cons start (.cons finish (.cons width .nil)))) =
          .done (.cons coefficients .nil) ∧
      coefficients.length = width + 1 ∧
      coefficientPolynomial coefficients =
        linePolynomial width table (coordinates width start) (coordinates width finish) ∧
      ∀ t : F, powerSum coefficients t =
        extension width table (linePoint (coordinates width start) (coordinates width finish) t) := by
  refine ⟨row (width + 1)
    (linePolynomial width table (coordinates width start) (coordinates width finish)),
    coefficients_plain width values start finish table decoded startSize finishSize capacity,
    row_length _ _, polynomial_correspond width table start finish, ?_⟩
  intro t
  rw [← coefficientPolynomial_eval, polynomial_correspond, linePolynomial_eval]

/-- The current source component table observes the complete coefficient row. -/
theorem coefficients_component (width : Nat) (values start finish : List F)
    (table : Table F width) (decoded : ofList? width values = some table)
    (startSize : start.length = width) (finishSize : finish.length = width)
    (capacity : 2 ^ width * (width + 1) < indexLimit) :
    invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
      GkrSourceBodies.helper69Helper
      (.cons (some values) (.cons (some start) (.cons (some finish) (.cons (some width) .nil)))) =
      .done (.cons (some (row (width + 1)
        (linePolynomial width table (coordinates width start) (coordinates width finish)))) .nil) := by
  change invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).components
    GkrSourceBodies.helper69Helper
    (Values.cons values (.cons start (.cons finish (.cons width .nil)))).present = _
  rw [HonestHelpers.component_present GkrSourceBodies.helper69Helper
    (.cons values (.cons start (.cons finish (.cons width .nil)))),
    coefficients_plain width values start finish table decoded startSize finishSize capacity]
  rfl

end ZkcSecurity.Realizations.Gkr.HonestLine
