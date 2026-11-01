module

public import ZkcSecurityExamples.Gkr.HonestLine
public import ZkcSecurityExamples.Gkr.HonestHelpersSource

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
      (Goals.Line.Inputs.pack (Value := assignment F G) { values, start, finish, width }) =
      .done (Goals.Line.encode (ringModel F G) ⟨row (width + 1)
        (linePolynomial width table (coordinates width start) (coordinates width finish))⟩) := by
  exact closed_invoke_returned GkrSourceViews.unit _ _ _
    (coefficients_correspond width values start finish table decoded startSize finishSize capacity)

/-- A complete reusable result for the actual helper: exact output, exact
length, polynomial equality and evaluation at every field point. -/
theorem actual_line_polynomial (width : Nat) (values start finish : List F)
    (table : Table F width) (decoded : ofList? width values = some table)
    (startSize : start.length = width) (finishSize : finish.length = width)
    (capacity : 2 ^ width * (width + 1) < indexLimit) :
    ∃ coefficients : List F,
      invoke (plainHelpers (F := F) (G := G) GkrSourceViews.unit).closed
        GkrSourceBodies.helper69Helper
        (Goals.Line.Inputs.pack (Value := assignment F G) { values, start, finish, width }) =
          .done (Goals.Line.encode (ringModel F G) ⟨coefficients⟩) ∧
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
      (Goals.Line.Inputs.pack (Value := Component (assignment F G)) { values := some values, start := some start, finish := some finish, width := some width }) =
      .done (Goals.Line.encode (ringModel F G) ⟨row (width + 1)
        (linePolynomial width table (coordinates width start) (coordinates width finish))⟩).present := by
  exact component_invoke_returned GkrSourceViews.unit _ _ _
    (coefficients_correspond width values start finish table decoded startSize finishSize capacity)

end ZkcSecurity.Realizations.Gkr.HonestLine
