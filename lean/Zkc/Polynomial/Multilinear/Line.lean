module

public import Zkc.Polynomial.Multilinear.Restriction
public import Zkc.Polynomial.Coordinates
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-! The restriction of a table's extension to a line.

`linePoint start finish t` is the point `start + (finish - start) t` on the line
through `start` (at `t = 0`) and `finish` (at `t = 1`). Along that line the
extension of a table over `n` coordinates is a polynomial of degree at most `n`
in `t` (`linePolynomial`). A different polynomial of degree at most `n` agrees
with it at no more than `n` values of `t` (`agreements_card_le`): this is the
Schwartz–Zippel step of the two-to-one reduction.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear
open _root_.Polynomial

variable {F : Type} [CommRing F] {n : Nat}

/-- The point `start + (finish - start) t`, coordinate by coordinate. -/
def linePoint (start finish : Fin n → F) (t : F) : Fin n → F :=
  fun i => start i + (finish i - start i) * t

theorem linePoint_zero (start finish : Fin n → F) : linePoint start finish 0 = start := by
  funext i
  simp [linePoint]

theorem linePoint_one (start finish : Fin n → F) : linePoint start finish 1 = finish := by
  funext i
  simp [linePoint]

/-- The extension of a table along the line, as a polynomial in `t`. -/
noncomputable def linePolynomial : (n : Nat) → Table F n → (Fin n → F) → (Fin n → F) → F[X]
  | 0, table, _, _ => C (table Fin.elim0)
  | n + 1, table, start, finish =>
      (1 - (C (start 0) + C (finish 0 - start 0) * X)) *
          linePolynomial n (half table false) (start ∘ Fin.succ) (finish ∘ Fin.succ) +
        (C (start 0) + C (finish 0 - start 0) * X) *
          linePolynomial n (half table true) (start ∘ Fin.succ) (finish ∘ Fin.succ)

theorem linePolynomial_eval (table : Table F n) (start finish : Fin n → F) (t : F) :
    (linePolynomial n table start finish).eval t = extension n table (linePoint start finish t) := by
  induction n with
  | zero => exact eval_C
  | succ n ih =>
      simp only [linePolynomial, eval_add, eval_mul, eval_sub, eval_one, eval_C, eval_X, ih]
      rfl

theorem linePolynomial_natDegree (table : Table F n) (start finish : Fin n → F) :
    (linePolynomial n table start finish).natDegree ≤ n := by
  induction n with
  | zero => simp [linePolynomial]
  | succ n ih =>
      have coordinate : (C (start 0) + C (finish 0 - start 0) * X : F[X]).natDegree ≤ 1 :=
        (natDegree_add_le _ _).trans (max_le (by simp)
          (natDegree_mul_le.trans (by rw [natDegree_C, zero_add]; exact natDegree_X_le)))
      have complement : (1 - (C (start 0) + C (finish 0 - start 0) * X) : F[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le (by simp) coordinate)
      unfold linePolynomial
      refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine natDegree_mul_le.trans ?_
        have tail := ih (half table false) (start ∘ Fin.succ) (finish ∘ Fin.succ)
        omega
      · refine natDegree_mul_le.trans ?_
        have tail := ih (half table true) (start ∘ Fin.succ) (finish ∘ Fin.succ)
        omega

theorem linePolynomial_zero (table : Table F n) (start finish : Fin n → F) :
    (linePolynomial n table start finish).eval 0 = extension n table start := by
  rw [linePolynomial_eval, linePoint_zero]

theorem linePolynomial_one (table : Table F n) (start finish : Fin n → F) :
    (linePolynomial n table start finish).eval 1 = extension n table finish := by
  rw [linePolynomial_eval, linePoint_one]

/-- A polynomial of degree at most `n` other than the line restriction agrees
with the extension along the line at no more than `n` points. -/
theorem agreements_card_le [IsDomain F] [Fintype F] [DecidableEq F] (table : Table F n)
    (start finish : Fin n → F) (polynomial : F[X]) (degree : polynomial.natDegree ≤ n)
    (different : polynomial ≠ linePolynomial n table start finish) :
    (Finset.univ.filter fun t =>
      polynomial.eval t = extension n table (linePoint start finish t)).card ≤ n := by
  set difference := polynomial - linePolynomial n table start finish
  have nonzero : difference ≠ 0 := sub_ne_zero.mpr different
  have small : difference.natDegree ≤ n :=
    (natDegree_sub_le _ _).trans (max_le degree (linePolynomial_natDegree table start finish))
  refine le_trans ?_ (le_trans (card_roots' difference) small)
  refine le_trans ?_ (Multiset.toFinset_card_le difference.roots)
  apply Finset.card_le_card
  intro t member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  rw [Multiset.mem_toFinset, mem_roots nonzero, IsRoot.def, eval_sub, linePolynomial_eval, member,
    sub_self]

end Zkc.Polynomial.Multilinear

namespace Zkc.Polynomial.Multilinear
open _root_.Polynomial

variable {F : Type} [CommRing F]

/-- The polynomial with the given coefficients, constant term first. -/
noncomputable def coefficientPolynomial : List F → F[X]
  | [] => 0
  | coefficient :: rest => C coefficient + X * coefficientPolynomial rest

theorem coefficientPolynomial_natDegree (coefficients : List F) :
    (coefficientPolynomial coefficients).natDegree ≤ coefficients.length - 1 := by
  induction coefficients with
  | nil => simp [coefficientPolynomial]
  | cons coefficient rest ih =>
      unfold coefficientPolynomial
      refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      cases rest with
      | nil => simp [coefficientPolynomial]
      | cons next tail =>
          refine natDegree_mul_le.trans ?_
          have degree := natDegree_X_le (R := F)
          simp only [List.length_cons] at ih ⊢
          omega

theorem coefficientPolynomial_eval_zero (coefficients : List F) :
    (coefficientPolynomial coefficients).eval 0 = coefficients.headD 0 := by
  cases coefficients with
  | nil => simp [coefficientPolynomial]
  | cons coefficient rest => simp [coefficientPolynomial]

theorem coefficientPolynomial_eval_one (coefficients : List F) :
    (coefficientPolynomial coefficients).eval 1 = coefficients.sum := by
  induction coefficients with
  | nil => simp [coefficientPolynomial]
  | cons coefficient rest ih => simp [coefficientPolynomial, ih]

end Zkc.Polynomial.Multilinear

namespace Zkc.Polynomial.Multilinear
open _root_.Polynomial

variable {F : Type} [CommRing F]

/-- A polynomial evaluated from its coefficients, constant term first. -/
def powerSum : List F → F → F
  | [], _ => 0
  | coefficient :: rest, t => coefficient + t * powerSum rest t

theorem coefficientPolynomial_eval (coefficients : List F) (t : F) :
    (coefficientPolynomial coefficients).eval t = powerSum coefficients t := by
  induction coefficients with
  | nil => simp [coefficientPolynomial, powerSum]
  | cons coefficient rest ih => simp [coefficientPolynomial, powerSum, ih]

/-- The points `start + (finish - start) t` of the line through two lists of
coordinates. -/
def linePoints (start finish : List F) (t : F) : List F :=
  List.zipWith (fun low high => low + (high - low) * t) start finish

theorem linePoints_length (start finish : List F) (t : F) :
    (linePoints start finish t).length = min start.length finish.length := by
  simp [linePoints]

theorem coordinates_linePoints {n : Nat} (start finish : List F) (t : F)
    (startSize : start.length = n) (finishSize : finish.length = n) :
    coordinates n (linePoints start finish t) =
      linePoint (coordinates n start) (coordinates n finish) t := by
  funext i
  have startBound : i.val < start.length := startSize ▸ i.isLt
  have finishBound : i.val < finish.length := finishSize ▸ i.isLt
  simp [coordinates, linePoints, linePoint, startBound, finishBound]

/-- An affine function `(1 - r) low + r high` with a nonzero coefficient pair
vanishes at no more than one point. -/
theorem affine_zeros_card_le [IsDomain F] [Fintype F] [DecidableEq F] (low high : F)
    (nonzero : ¬ (low = 0 ∧ high = 0)) :
    (Finset.univ.filter fun r => (1 - r) * low + r * high = 0).card ≤ 1 := by
  set affine : F[X] := C low + C (high - low) * X
  have affine_eval (r : F) : affine.eval r = (1 - r) * low + r * high := by
    simp only [affine, eval_add, eval_mul, eval_C, eval_X]
    ring
  have affine_nonzero : affine ≠ 0 := by
    intro zero
    apply nonzero
    have atZero := congrArg (eval 0) zero
    have atOne := congrArg (eval 1) zero
    simp only [affine_eval, eval_zero, sub_zero, one_mul, zero_mul, add_zero, sub_self,
      zero_add] at atZero atOne
    exact ⟨atZero, atOne⟩
  have degree : affine.natDegree ≤ 1 :=
    (natDegree_add_le _ _).trans (max_le (by simp)
      (natDegree_mul_le.trans (by rw [natDegree_C, zero_add]; exact natDegree_X_le)))
  refine le_trans ?_ (le_trans (card_roots' affine) degree)
  refine le_trans ?_ (Multiset.toFinset_card_le affine.roots)
  apply Finset.card_le_card
  intro r member
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at member
  rw [Multiset.mem_toFinset, mem_roots affine_nonzero, IsRoot.def, affine_eval, member]

end Zkc.Polynomial.Multilinear
