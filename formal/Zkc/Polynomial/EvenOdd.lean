import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Ring

/-! Even/odd coefficient decomposition and the algebraic FRI fold. These laws
concern polynomials only; they establish no proximity or protocol security claim. -/

set_option autoImplicit false

noncomputable section

namespace Zkc.Polynomial.EvenOdd

open _root_.Polynomial

section CommSemiring

variable {F : Type*} [CommSemiring F]

/-- Coefficients of even powers, with their exponents halved. -/
def even (p : F[X]) : F[X] := contract 2 p

/-- Coefficients of odd powers, with one removed before halving the exponents. -/
def odd (p : F[X]) : F[X] := contract 2 p.divX

/-- The polynomial produced by one algebraic folding step. -/
def fold (p : F[X]) (beta : F) : F[X] := even p + C beta * odd p

@[simp] theorem coeff_even (p : F[X]) (n : ℕ) :
    (even p).coeff n = p.coeff (n * 2) :=
  coeff_contract (by decide) p n

@[simp] theorem coeff_odd (p : F[X]) (n : ℕ) :
    (odd p).coeff n = p.coeff (n * 2 + 1) := by
  simp [odd, coeff_contract (by decide : 2 ≠ 0)]

@[simp] theorem coeff_fold (p : F[X]) (beta : F) (n : ℕ) :
    (fold p beta).coeff n = p.coeff (n * 2) + beta * p.coeff (n * 2 + 1) := by
  simp [fold]

@[simp] theorem even_zero : even (0 : F[X]) = 0 := by ext; simp

@[simp] theorem odd_zero : odd (0 : F[X]) = 0 := by ext; simp

@[simp] theorem even_C (a : F) : even (C a) = C a := contract_C _ _

@[simp] theorem odd_C (a : F) : odd (C a) = 0 := by ext; simp

@[simp] theorem fold_zero (beta : F) : fold (0 : F[X]) beta = 0 := by simp [fold]

@[simp] theorem fold_C (a beta : F) : fold (C a) beta = C a := by simp [fold]

@[simp] theorem fold_zero_challenge (p : F[X]) : fold p 0 = even p := by simp [fold]

/-- Reconstruction is a polynomial identity, including in characteristic two. -/
theorem reconstruction (p : F[X]) :
    p = (even p).comp (X ^ 2) + X * (odd p).comp (X ^ 2) := by
  change p = expand F 2 (even p) + X * expand F 2 (odd p)
  ext n
  cases n with
  | zero => simp [coeff_expand (by decide : 0 < 2)]
  | succ n =>
    rw [coeff_add, coeff_X_mul, coeff_expand (by decide : 0 < 2),
      coeff_expand (by decide : 0 < 2), coeff_even, coeff_odd]
    by_cases h : 2 ∣ n
    · have h' : ¬ 2 ∣ n + 1 := by omega
      rw [if_neg h', if_pos h, zero_add, Nat.div_mul_cancel h]
    · have h' : 2 ∣ n + 1 := by omega
      rw [if_pos h', if_neg h, add_zero, Nat.div_mul_cancel h']

theorem natDegree_even_le (p : F[X]) : (even p).natDegree ≤ p.natDegree / 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_even]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem natDegree_odd_le (p : F[X]) : (odd p).natDegree ≤ p.natDegree / 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_odd]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- A fold has at most half the original natural degree, also for the zero polynomial. -/
theorem natDegree_fold_le (p : F[X]) (beta : F) :
    (fold p beta).natDegree ≤ p.natDegree / 2 :=
  natDegree_add_le_of_degree_le (natDegree_even_le p)
    ((natDegree_C_mul_le beta (odd p)).trans (natDegree_odd_le p))

theorem eval_reconstruction (p : F[X]) (x : F) :
    p.eval x = (even p).eval (x ^ 2) + x * (odd p).eval (x ^ 2) := by
  have h := congrArg (eval x) (reconstruction p)
  simpa only [eval_add, eval_mul, eval_comp, eval_pow, eval_X] using h

@[simp] theorem eval_fold (p : F[X]) (beta y : F) :
    (fold p beta).eval y = (even p).eval y + beta * (odd p).eval y := by
  simp [fold]

end CommSemiring

section Field

variable {F : Type*} [Field F]

/-- Recover the even part from antipodal evaluations when two is invertible. -/
theorem eval_even_sq (p : F[X]) (x : F) (h2 : (2 : F) ≠ 0) :
    (even p).eval (x ^ 2) = (p.eval x + p.eval (-x)) / 2 := by
  apply (eq_div_iff h2).2
  rw [eval_reconstruction p x, eval_reconstruction p (-x), neg_sq]
  ring

/-- Recover the odd part; the evaluation point must additionally be nonzero. -/
theorem eval_odd_sq (p : F[X]) (x : F) (h2 : (2 : F) ≠ 0) (hx : x ≠ 0) :
    (odd p).eval (x ^ 2) = (p.eval x - p.eval (-x)) / (2 * x) := by
  apply (eq_div_iff (mul_ne_zero h2 hx)).2
  rw [eval_reconstruction p x, eval_reconstruction p (-x), neg_sq]
  ring

/-- The algebraic FRI evaluation formula, with both denominator conditions explicit. -/
theorem eval_fold_sq (p : F[X]) (beta x : F) (h2 : (2 : F) ≠ 0) (hx : x ≠ 0) :
    (fold p beta).eval (x ^ 2) =
      (p.eval x + p.eval (-x)) / 2 + beta * (p.eval x - p.eval (-x)) / (2 * x) := by
  rw [eval_fold, eval_even_sq p x h2, eval_odd_sq p x h2 hx, mul_div_assoc]

end Field

end Zkc.Polynomial.EvenOdd
