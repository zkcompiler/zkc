module

public import Zkc.Source.Structured.NumericalEvaluation
public import Mathlib.Algebra.Polynomial.CoeffList

@[expose] public section

/-! Algebraic meaning of the computable coefficient operations. The mathlib
polynomial is used in proofs; evaluation never invokes its noncomputable
coefficient-list constructor or assumes an FFT implementation correct. -/

namespace Zkc.Source.Structured.Numerical
variable {F : Type} [CommRing F] [DecidableEq F]

theorem evaluate_normalize (cs : List F) (x : F) :
    evaluate (normalizeCoefficients 0 cs) x = evaluate cs x := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    simp only [normalizeCoefficients]
    split
    · rename_i h
      have tail : evaluate cs x = 0 := by rw [← ih, h.1]; rfl
      change 0 = a + x * evaluate cs x
      rw [h.2, tail]
      simp
    · simpa only [evaluate, List.foldr_cons] using congrArg (fun y ↦ a + x * y) ih

omit [DecidableEq F] in
theorem evaluate_eq_polynomial (cs : List F) (x : F) :
    evaluate cs x = (Polynomial.ofCoeffList cs).eval x := by
  induction cs with
  | nil => simp [evaluate]
  | cons a cs ih =>
    simp only [evaluate, List.foldr_cons, Polynomial.ofCoeffList_cons,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] at *
    rw [ih]

theorem normalize_polynomial (cs : List F) :
    Polynomial.ofCoeffList (normalizeCoefficients 0 cs) = Polynomial.ofCoeffList cs := by
  induction cs with
  | nil => rfl
  | cons a cs ih =>
    simp only [normalizeCoefficients]
    split
    · rename_i h
      have tail : Polynomial.ofCoeffList cs = 0 := by rw [← ih, h.1]; simp
      simp [Polynomial.ofCoeffList_cons, h.2, tail]
    · simp only [Polynomial.ofCoeffList_cons, ih]

omit [DecidableEq F] in
theorem evaluate_add (as bs : List F) (x : F) :
    evaluate (add as bs) x = evaluate as x + evaluate bs x := by
  induction as generalizing bs with
  | nil => simp [add, evaluate]
  | cons a as ih =>
    cases bs with
    | nil => simp [add, evaluate]
    | cons b bs =>
      simp only [add, evaluate, List.foldr_cons] at *
      rw [ih]
      ring

omit [DecidableEq F] in
theorem evaluate_scale (a : F) (cs : List F) (x : F) :
    evaluate (cs.map (a * ·)) x = a * evaluate cs x := by
  induction cs with
  | nil => simp [evaluate]
  | cons b cs ih =>
    simp only [List.map_cons, evaluate, List.foldr_cons] at *
    rw [ih]
    ring

omit [DecidableEq F] in
theorem evaluate_multiply (as bs : List F) (x : F) :
    evaluate (multiply as bs) x = evaluate as x * evaluate bs x := by
  induction as with
  | nil => simp [multiply, evaluate]
  | cons a as ih =>
    rw [multiply, evaluate_add, evaluate_scale]
    simp only [evaluate, List.foldr_cons] at *
    rw [ih]
    ring

/-- Canonicalization preserves all evaluations, including the zero polynomial. -/
theorem ofCoefficients_evaluate (cs : List F) (x : F) :
    evaluate (PolynomialValue.ofCoefficients 0 cs).coefficients x = evaluate cs x :=
  evaluate_normalize cs x

end Zkc.Source.Structured.Numerical
