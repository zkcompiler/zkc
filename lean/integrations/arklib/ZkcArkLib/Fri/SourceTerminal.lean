module

public import ZkcArkLib.Fri.Correspondence
public import Zkc.Source.Structured.NumericalLaws
public import Mathlib.Algebra.Polynomial.Degree.Operations

/-!
# Actual source coefficients at the exact terminal length

The current source checks exactly `2^t` transmitted coefficients. These theorems
use that equality, interpret the actual normalized source value, and place its
word in ArkLib's Reed–Solomon code. They do not identify complete verifier bodies.
-/

@[expose] public section

namespace ZkcSecurity.ArkLib.Fri.SourceTerminal

open Zkc.Source.Structured

variable {F : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Identify the historical coefficient interpretation with Mathlib's existing constructor. -/
theorem toPolynomial_eq (cs : List F) : toPolynomial cs = Polynomial.ofCoeffList cs := by
  induction cs with
  | nil => simp [toPolynomial]
  | cons a cs ih => simp [toPolynomial, Polynomial.ofCoeffList_cons, ih]

/-- The actual source Horner evaluator has the polynomial meaning used by the correspondence. -/
theorem evaluate_eq (cs : List F) (x : F) :
    Numerical.evaluate (PolynomialValue.ofCoefficients 0 cs).coefficients x =
      (toPolynomial cs).eval x := by
  rw [Numerical.ofCoefficients_evaluate, Numerical.evaluate_eq_polynomial, toPolynomial_eq]

/-- Exact transmitted length puts the actual normalized terminal evaluations in the code. -/
theorem exact_length_in_code {m : Nat} (domain : Domain.SmoothCosetFftDomain m F)
    (cs : List F) (t : Nat) (exactLength : cs.length = 2 ^ t) :
    (fun i ↦ Numerical.evaluate (PolynomialValue.ofCoefficients 0 cs).coefficients (domain i)) ∈
      ReedSolomon.code (domain : Fin (2 ^ m) ↪ F) (2 ^ t) := by
  have degree : (Polynomial.ofCoeffList cs).degree < (2 ^ t : Nat) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro index outside
    rw [Polynomial.coeff_ofCoeffList, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by rw [exactLength]; exact_mod_cast outside)]
    rfl
  have code := ReedSolomon.evalOnPoints_mem_code_of_degree_lt
    (α := (domain : Fin (2 ^ m) ↪ F)) degree
  convert code using 1
  funext i
  rw [Numerical.ofCoefficients_evaluate, Numerical.evaluate_eq_polynomial]
  rfl

end ZkcSecurity.ArkLib.Fri.SourceTerminal
