module

public import Mathlib.Algebra.Polynomial.Roots
public import ZkcFormal.Interactive.Quadratic
import Mathlib.Tactic.ComputeDegree

@[expose] public section
namespace ZkcFormal.Written.PolynomialBounds
open Polynomial Interactive.Sumcheck

/-- Two different polynomials of degree at most `d` agree at no more than `d` points of a list
without repetition. -/
theorem agreements_le {F : Type} [Field F] [DecidableEq F] (p q : F[X]) (d : Nat)
    (hp : p.natDegree ≤ d) (hq : q.natDegree ≤ d) (apart : p ≠ q)
    (points : List F) (distinct : points.Nodup) :
    points.countP (fun r => decide (p.eval r = q.eval r)) ≤ d := by
  have nz : p - q ≠ 0 := sub_ne_zero.mpr apart
  rw [List.countP_eq_length_filter]
  have inside : (points.filter fun r => decide (p.eval r = q.eval r)).toFinset ⊆
      (p - q).roots.toFinset := by
    intro x hx
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq] at hx
    simp [mem_roots nz, hx.2]
  calc (points.filter fun r => decide (p.eval r = q.eval r)).length
      = (points.filter fun r => decide (p.eval r = q.eval r)).toFinset.card :=
        (List.toFinset_card_of_nodup (distinct.filter _)).symm
    _ ≤ (p - q).roots.toFinset.card := Finset.card_le_card inside
    _ ≤ Multiset.card (p - q).roots := Multiset.toFinset_card_le _
    _ ≤ (p - q).natDegree := card_roots' _
    _ ≤ d := (natDegree_sub_le p q).trans (max_le hp hq)

variable {F : Type} [Field F] [DecidableEq F]

/-- Transport the library root count through the representation of a protocol message. -/
theorem ofEncoding {A : Type} (encode : A → F[X]) (boundary : A → F) (evaluate : A → F → F)
    (d : Nat) (degree : ∀ a, (encode a).natDegree ≤ d)
    (atPoint : ∀ a r, (encode a).eval r = evaluate a r)
    (determines : ∀ a b, encode a = encode b → boundary a = boundary b) :
    CollisionBound boundary evaluate d := by
  intro a b wrong points distinct
  simpa only [atPoint] using agreements_le (encode a) (encode b) d (degree a) (degree b)
    (fun eq => wrong (determines a b eq)) points distinct

noncomputable def linear (a : F × F) : F[X] := C a.1 + X * C (a.2 - a.1)

theorem pairs : CollisionBound (fun a : F × F => a.1 + a.2) line 1 := by
  apply ofEncoding linear
  · intro a
    unfold linear
    compute_degree
  · intro a r
    simp [linear, line_normalForm]
  · intro a b eq
    have zero := congrArg (Polynomial.eval 0) eq
    have one := congrArg (Polynomial.eval 1) eq
    simp [linear] at zero one
    grind

noncomputable def quadratic (a : Quadratic F) : F[X] := C a.constant + X * (C a.linear + X * C a.square)

theorem gates : CollisionBound (Quadratic.boundary (F := F)) Quadratic.eval 2 := by
  apply ofEncoding quadratic
  · intro a
    unfold quadratic
    compute_degree
  · intro a r
    simp only [quadratic, Quadratic.eval, eval_add, eval_mul, eval_C, eval_X]
  · intro a b eq
    have zero := congrArg (Polynomial.eval 0) eq
    have one := congrArg (Polynomial.eval 1) eq
    simpa [quadratic, Quadratic.boundary, Quadratic.eval] using congrArg₂ (· + ·) zero one

end ZkcFormal.Written.PolynomialBounds
