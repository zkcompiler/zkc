module

public import ZkcFormal.Interactive.Reduction

@[expose] public section
namespace ZkcFormal.Interactive.Sumcheck
open Zkc.Core

structure Quadratic (F : Type) where
  constant : F
  linear : F
  square : F

namespace Quadratic
open Lean.Grind
variable {F : Type} [Lean.Grind.Field F]

def eval (q : Quadratic F) (x : F) : F := q.constant + x*(q.linear + x*q.square)
def boundary (q : Quadratic F) : F := q.eval 0 + q.eval 1

private theorem eval_difference (q : Quadratic F) (r s : F) :
    q.eval r - q.eval s = (r-s)*(q.linear + (r+s)*q.square) := by
  calc
    q.eval r - q.eval s = (r*q.linear - s*q.linear) + (r*r*q.square - s*s*q.square) := by
      rw [eval, eval, Algebra.add_sub_add_left, Semiring.left_distrib, Semiring.left_distrib,
        Algebra.add_sub_add, ← Semiring.mul_assoc, ← Semiring.mul_assoc]
    _ = (r-s)*q.linear + ((r-s)*(r+s))*q.square := by
      rw [Algebra.difference_of_squares, Algebra.sub_mul, Algebra.sub_mul]
    _ = _ := by rw [Semiring.mul_assoc, ← Semiring.left_distrib]

private theorem slope {a b : Quadratic F} {r s : F} (apart : r ≠ s)
    (first : a.eval r = b.eval r) (second : a.eval s = b.eval s) :
    a.linear + (r+s)*a.square = b.linear + (r+s)*b.square := by
  apply Algebra.cancel_left (fun h => apart (AddCommGroup.sub_eq_zero_iff.mp h))
  rw [← eval_difference, ← eval_difference, first, second]

/-- Three distinct agreements force equality of the two Boolean boundary sums. -/
theorem boundary_of_three {a b : Quadratic F} {r s u : F} (rs : r ≠ s) (su : s ≠ u) (ru : r ≠ u)
    (hr : a.eval r = b.eval r) (hs : a.eval s = b.eval s) (hu : a.eval u = b.eval u) :
    a.boundary = b.boundary := by
  have first := slope rs hr hs
  have second := slope su hs hu
  have coeff := Algebra.affine_slope_products first second
  rw [Semiring.add_comm r s, Algebra.add_sub_add_left] at coeff
  have square := Algebra.cancel_left (fun h => ru (AddCommGroup.sub_eq_zero_iff.mp h)) coeff
  rw [square] at first
  have linear := (AddCommGroup.add_left_inj _).mp first
  unfold eval at hr
  rw [square, linear] at hr
  have constant := (AddCommGroup.add_left_inj _).mp hr
  simp only [boundary, eval, constant, linear, square]

theorem collisions [DecidableEq F] (a b : Quadratic F) (wrong : a.boundary ≠ b.boundary)
    (points : List F) (distinct : points.Nodup) :
    points.countP (fun r => decide (a.eval r = b.eval r)) ≤ 2 := by
  let p := fun r => decide (a.eval r = b.eval r)
  change points.countP p ≤ 2
  rw [List.countP_eq_length_filter]
  cases filtered : points.filter p with
  | nil => simp
  | cons r tail =>
    cases tail with
    | nil => simp
    | cons s tail =>
      cases tail with
      | nil => simp
      | cons u rest =>
        have nd := distinct.filter p
        rw [filtered] at nd
        have rs := (List.nodup_cons.mp nd).1
        have su := (List.nodup_cons.mp (List.nodup_cons.mp nd).2).1
        have atRoot : ∀ x ∈ r::s::u::rest, a.eval x = b.eval x := by
          intro x hx
          rw [← filtered] at hx
          exact of_decide_eq_true (List.mem_filter.mp hx).2
        exact False.elim (wrong (boundary_of_three (fun e => rs (by simp [e]))
          (fun e => su (by simp [e])) (fun e => rs (by simp [e]))
          (atRoot r (by simp)) (atRoot s (by simp)) (atRoot u (by simp))))

end Quadratic
/-- The public residual and the message each denote a quadratic for the current
coordinate. Their Boolean boundary and point evaluations are the instance obligations. -/
theorem Verifier.reduce_quadratic {S : Sig} {H F Msg σ : Type} [Lean.Grind.Field F] [DecidableEq F]
    (v : Verifier (S := S) H F Msg) (q : Claims F) (offered : Msg → Quadratic F)
    (honest : ∀ n, q.State (n+1) → Quadratic F)
    (messageBoundary : ∀ m, v.boundary m = (offered m).boundary)
    (messageEvaluation : ∀ m r, v.evaluate m r = (offered m).eval r)
    (sum : ∀ n x, q.value (n+1) x = (honest n x).boundary)
    (restricted : ∀ n x r, q.value n (q.restrict n x r) = (honest n x).eval r)
    (K : Experiment S σ) (points : List F) (distinct : points.Nodup) (positive : 0 < points.length)
    (fresh : v.publicCoins K points positive) (n : Nat) (x : q.State n) (history : List F)
    (claim : F) (s : σ) (wrong : claim ≠ q.value n x) :
    K.probability (v.reduce n history claim) s (fun (rs,value) _ => decide (q.evaluate n x rs = some value)) ≤
      (n : Mass) * roundCost 2 points := by
  apply v.reduce_sound q K points positive 2 _ fresh n x history claim s wrong
  intro remaining publicState claimed m bad passes
  simp only [messageEvaluation, restricted]
  apply Quadratic.collisions _ _ _ points distinct
  rwa [← messageBoundary,passes,← sum]

end ZkcFormal.Interactive.Sumcheck
