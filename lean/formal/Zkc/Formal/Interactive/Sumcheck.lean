module

public import Zkc.Formal.Interactive.Uniform
public import Zkc.Formal.Interactive.Iteration
public import Zkc.Formal.Interactive.ConstructiveAlgebra

@[expose] public section

namespace Zkc.Formal.Interactive.Sumcheck

/-- Charge for a degree bound over a nonempty finite challenge alphabet. -/
def roundCost {F : Type} (degree : Nat) (points : List F) : Mass :=
  (degree : Mass) / (points.length : Mass)

open Core

/-- Verifier order at a reduction round. The output retains the challenge at which
the residual claim is made. The message and draw can themselves be interactive processes. -/
def verifierRound {S : Sig} {H F M : Type} [DecidableEq F]
    (receive : Process S H M) (draw : M → Process S H F) (reject : H)
    (boundary : M → F) (evaluate : M → F → F) (claim : F) : Process S H (F × F) :=
  receive.bind fun m =>
    if boundary m = claim then (draw m).map fun r => (r, evaluate m r)
    else .halt reject

/-- At each state reached after receipt of the message, the conditional draw may abort.
Every event nevertheless has probability bounded by its uniform mass. -/
def Fresh {S : Sig} {σ H F : Type} (K : Experiment S σ) (points : List F)
    (positive : 0 < points.length) (draw : Process S H F) (s : σ) : Prop :=
  ∀ event : F → Bool, K.probability draw s (fun r _ => event r) ≤
    (FiniteLaw.uniform points positive).expect (fun r => if event r then 1 else 0)

/-- Only positive-weight, boundary-passing messages incur a challenge obligation. -/
theorem verifierRound_le {S : Sig} {σ H F M : Type} [DecidableEq F]
    (K : Experiment S σ) (s : σ) (points : List F) (positive : 0 < points.length)
    (receive : Process S H M) (draw : M → Process S H F) (reject : H)
    (boundary : M → F) (evaluate : M → F → F) (truth : F → F) (claim : F) (degree : Nat)
    (fresh : ∀ m t, K.Reaches receive s m t → boundary m = claim → Fresh K points positive (draw m) t)
    (roots : ∀ m, boundary m = claim → points.countP (fun r => decide (evaluate m r = truth r)) ≤ degree) :
    K.probability (verifierRound receive draw reject boundary evaluate claim) s
      (fun result _ => decide (result.2 = truth result.1)) ≤ roundCost degree points := by
  have sign : 0 ≤ (points.length : Mass)⁻¹ := Mass.le_of_lt (Mass.inv_pos.mpr (Mass.natCast_pos.mpr positive))
  have nonneg : 0 ≤ roundCost degree points := Mass.mul_nonneg Mass.natCast_nonneg sign
  simp only [verifierRound, Experiment.probability, Experiment.expect_bind]
  apply Mass.le_trans (K.expect_mono receive s _ _ ?_) (K.expect_constant_le receive s nonneg)
  intro m t reached
  split
  next passed =>
    have drawBound := fresh m t reached passed (fun r => decide (evaluate m r = truth r))
    rw [FiniteLaw.uniform_event] at drawBound
    have cardBound := Mass.mul_le_mul_of_nonneg_right (Mass.natCast_le_natCast.mpr (roots m passed)) sign
    simp only [Process.map_eq_bind, Experiment.expect_bind, Experiment.expect]
    exact Mass.le_trans drawBound cardBound
  next => exact nonneg

/-- The degree-one evaluation in the source Pairs instance. -/
def line {F : Type} [Lean.Grind.CommRing F] (m : F × F) (r : F) : F :=
  (1-r)*m.1 + r*m.2

open Lean.Grind

theorem line_normalForm {F : Type} [CommRing F] (m : F × F) (r : F) :
    line m r = m.1 + r * (m.2 - m.1) := by
  rw [line, Algebra.sub_mul, Semiring.one_mul, Algebra.mul_sub, Ring.sub_eq_add_neg,
    Ring.sub_eq_add_neg, Semiring.add_assoc, Semiring.add_comm (-(r * m.1))]

theorem line_unique_collision {F : Type} [Field F] (a b : F × F) (r s : F)
    (wrong : a.1 + a.2 ≠ b.1 + b.2) (hr : line a r = line b r) (hs : line a s = line b s) :
    r = s := by
  rw [line_normalForm, line_normalForm] at hr hs
  -- At a shared point, equal slopes would force both endpoints to agree.
  have apart : (a.2 - a.1) - (b.2 - b.1) ≠ 0 := by
    intro zero
    have slopes := AddCommGroup.sub_eq_zero_iff.mp zero
    rw [slopes] at hr
    have first : a.1 = b.1 := (AddCommGroup.add_left_inj _).mp hr
    rw [first] at slopes
    have second := congrArg (· + b.1) slopes
    simp only [AddCommGroup.sub_add_cancel] at second
    exact wrong (by rw [first, second])
  have diff := Algebra.affine_slope_products hr hs
  have zero : (r-s)*((a.2-a.1)-(b.2-b.1)) = 0 := by
    rw [Algebra.mul_sub, diff, AddCommGroup.sub_self]
  apply AddCommGroup.sub_eq_zero_iff.mp
  apply Algebra.cancel_left apart
  rw [CommSemiring.mul_comm _ (r-s), zero, Semiring.mul_zero]

theorem count_unique {α : Type} (xs : List α) (distinct : xs.Nodup) (p : α → Bool)
    (unique : ∀ x y, p x → p y → x = y) : xs.countP p ≤ 1 := by
  rw [List.countP_eq_length_filter]
  cases filtered : xs.filter p with
  | nil => simp
  | cons x tail =>
    cases tail with
    | nil => simp
    | cons y ys =>
      have nd := distinct.filter p
      rw [filtered] at nd
      have hit (z : α) (mem : z ∈ x :: y :: ys) : p z := by
        rw [← filtered] at mem
        exact (List.mem_filter.mp mem).2
      have same := unique x y (hit x (.head _)) (hit y (.tail _ (.head _)))
      exact False.elim ((List.nodup_cons.mp nd).1 (same ▸ List.Mem.head _))

theorem pairsRound {S : Sig} {σ H F : Type} [Lean.Grind.Field F] [DecidableEq F]
    (K : Experiment S σ) (s : σ) (points : List F) (distinct : points.Nodup)
    (positive : 0 < points.length) (receive : Process S H (F × F))
    (draw : F × F → Process S H F) (reject : H) (honest : F × F) (claim : F)
    (wrong : claim ≠ honest.1 + honest.2)
    (fresh : ∀ m t, K.Reaches receive s m t → m.1 + m.2 = claim → Fresh K points positive (draw m) t) :
    K.probability (verifierRound receive draw reject (fun m => m.1 + m.2) line claim) s
      (fun result _ => decide (result.2 = line honest result.1)) ≤ roundCost 1 points := by
  apply verifierRound_le K s points positive _ _ _ _ _ _ _ _ fresh
  intro msg passed
  apply count_unique points distinct
  intro r s hr hs
  exact line_unique_collision msg honest r s (passed ▸ wrong) (of_decide_eq_true hr) (of_decide_eq_true hs)

end Zkc.Formal.Interactive.Sumcheck
