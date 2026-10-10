import Zkc.Polynomial.BooleanCube
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Tactic.Ring

/-! Executable Boolean tables and cubic round messages for a virtual product.

This example keeps three multilinear factors instead of materializing their
product. Tables are a small reference representation, not a native layout API.
The first coordinate is always restricted first. No interpolation division or
lower bound on the characteristic is required.
-/

set_option autoImplicit false

namespace Examples.OpeningReduction

open Zkc.Polynomial

inductive Table (F : Type) : Nat → Type where
  | scalar : F → Table F 0
  | node {n : Nat} : Table F n → Table F n → Table F (n + 1)
  deriving Repr

namespace Table
variable {F : Type} [CommRing F]

def eval : {n : Nat} → Table F n → (Fin n → F) → F
  | 0, .scalar x, _ => x
  | _ + 1, .node lo hi, p =>
      (1 - p 0) * eval lo (p ∘ Fin.succ) + p 0 * eval hi (p ∘ Fin.succ)

def combine (r : F) : {n : Nat} → Table F n → Table F n → Table F n
  | 0, .scalar x, .scalar y => .scalar ((1 - r) * x + r * y)
  | _ + 1, .node a b, .node c d => .node (combine r a c) (combine r b d)

theorem eval_combine (r : F) {n : Nat} (lo hi : Table F n) (p : Fin n → F) :
    (combine r lo hi).eval p = (1 - r) * lo.eval p + r * hi.eval p := by
  induction lo with
  | scalar x => cases hi; rfl
  | node a b ia ib =>
      cases hi
      simp only [combine, eval, ia, ib]
      ring

def restrict {n : Nat} (p : Table F (n + 1)) (r : F) : Table F n :=
  match p with | .node lo hi => combine r lo hi

theorem eval_restrict {n : Nat} (p : Table F (n + 1)) (r : F) (tail : Fin n → F) :
    (p.restrict r).eval tail = p.eval (Fin.cons r tail) := by
  cases p
  simp [restrict, eval_combine, eval, Function.comp_def]

def scale (r : F) : {n : Nat} → Table F n → Table F n
  | 0, .scalar x => .scalar (r * x)
  | _ + 1, .node lo hi => .node (scale r lo) (scale r hi)

theorem eval_scale (r : F) {n : Nat} (t : Table F n) (p : Fin n → F) :
    (scale r t).eval p = r * t.eval p := by
  induction t with
  | scalar x => rfl
  | node lo hi il ih => simp only [scale, eval, il, ih]; ring

def add : {n : Nat} → Table F n → Table F n → Table F n
  | 0, .scalar x, .scalar y => .scalar (x + y)
  | _ + 1, .node a b, .node c d => .node (add a c) (add b d)

theorem eval_add {n : Nat} (a b : Table F n) (p : Fin n → F) :
    (a.add b).eval p = a.eval p + b.eval p := by
  induction a with
  | scalar x => cases b; rfl
  | node lo hi il ih => cases b; simp only [add, eval, il, ih]; ring

end Table

structure Message (F : Type) where
  constant : F
  linear : F
  quadratic : F
  cubic : F
  deriving Repr, DecidableEq

namespace Message
variable {F : Type} [CommRing F]

def eval (m : Message F) (r : F) : F :=
  m.constant + m.linear * r + m.quadratic * r ^ 2 + m.cubic * r ^ 3

def boundary (m : Message F) : F := m.eval 0 + m.eval 1

def add (a b : Message F) : Message F :=
  ⟨a.constant + b.constant, a.linear + b.linear,
    a.quadratic + b.quadratic, a.cubic + b.cubic⟩

theorem eval_add (a b : Message F) (r : F) :
    (a.add b).eval r = a.eval r + b.eval r := by simp only [add, eval]; ring

def sum : (n : Nat) → ((Fin n → F) → Message F) → Message F
  | 0, f => f Fin.elim0
  | n + 1, f => (sum n (fun p => f (Fin.cons 0 p))).add (sum n (fun p => f (Fin.cons 1 p)))

theorem eval_sum (n : Nat) (f : (Fin n → F) → Message F) (r : F) :
    (sum n f).eval r = cubeSum n (fun p => (f p).eval r) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, cubeSum, eval_add, ih]

/-- Multiply three affine expressions without division. -/
def product (a da b db c dc : F) : Message F :=
  ⟨a*b*c, da*b*c + a*db*c + a*b*dc,
    da*db*c + da*b*dc + a*db*dc, da*db*dc⟩

theorem eval_product (a da b db c dc r : F) :
    (product a da b db c dc).eval r = (a + r*da) * (b + r*db) * (c + r*dc) := by
  simp only [product, eval]
  ring

noncomputable def polynomial (m : Message F) : Polynomial F :=
  Polynomial.C m.constant + Polynomial.C m.linear * Polynomial.X +
    Polynomial.C m.quadratic * Polynomial.X ^ 2 + Polynomial.C m.cubic * Polynomial.X ^ 3

theorem polynomial_eval (m : Message F) (r : F) : m.polynomial.eval r = m.eval r := by
  simp [polynomial, eval]

theorem polynomial_degree (m : Message F) : m.polynomial.natDegree ≤ 3 := by
  apply Polynomial.natDegree_add_le_of_degree_le
  · apply Polynomial.natDegree_add_le_of_degree_le
    · apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_le.trans (by omega))
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · exact Polynomial.natDegree_C_mul_X_pow_le _ _

theorem collision_card [IsDomain F] [Fintype F] [DecidableEq F]
    (a b : Message F) (different : a.boundary ≠ b.boundary) :
    (Finset.univ.filter fun r => a.eval r = b.eval r).card ≤ 3 := by
  have ne : a.polynomial ≠ b.polynomial := by
    intro same
    apply different
    have h0 := congrArg (fun p : Polynomial F => p.eval 0) same
    have h1 := congrArg (fun p : Polynomial F => p.eval 1) same
    simpa only [polynomial_eval, boundary] using congrArg₂ (· + ·) h0 h1
  have nz : a.polynomial - b.polynomial ≠ 0 := sub_ne_zero.mpr ne
  have roots : (Finset.univ.filter fun r => a.eval r = b.eval r).val ⊆
      (a.polynomial - b.polynomial).roots := by
    intro r hr
    apply (Polynomial.mem_roots nz).mpr
    simpa only [Polynomial.IsRoot, Polynomial.eval_sub, polynomial_eval, sub_eq_zero] using
      (Finset.mem_filter.mp hr).2
  exact (Polynomial.card_le_degree_of_subset_roots roots).trans
    ((Polynomial.natDegree_sub_le _ _).trans (max_le (polynomial_degree _) (polynomial_degree _)))

end Message

structure Factors (F : Type) (n : Nat) where
  first : Table F n
  second : Table F n
  third : Table F n
  deriving Repr

namespace Factors
variable {F : Type} [CommRing F] {n : Nat}

def eval (p : Factors F n) (point : Fin n → F) : F :=
  p.first.eval point * p.second.eval point * p.third.eval point

def booleanSum (p : Factors F n) : F := cubeSum n p.eval

def restrict (p : Factors F (n + 1)) (r : F) : Factors F n :=
  ⟨p.first.restrict r, p.second.restrict r, p.third.restrict r⟩

theorem eval_restrict (p : Factors F (n + 1)) (r : F) (tail : Fin n → F) :
    (p.restrict r).eval tail = p.eval (Fin.cons r tail) := by
  simp only [restrict, eval, Table.eval_restrict]

def round (p : Factors F (n + 1)) : Message F :=
  Message.sum n fun tail =>
    let a := p.first.eval (Fin.cons 0 tail)
    let b := p.second.eval (Fin.cons 0 tail)
    let c := p.third.eval (Fin.cons 0 tail)
    Message.product a (p.first.eval (Fin.cons 1 tail) - a)
      b (p.second.eval (Fin.cons 1 tail) - b) c (p.third.eval (Fin.cons 1 tail) - c)

theorem round_eval (p : Factors F (n + 1)) (r : F) :
    p.round.eval r = (p.restrict r).booleanSum := by
  rw [round, Message.eval_sum]
  unfold booleanSum
  congr 1
  funext tail
  rw [Message.eval_product, eval_restrict]
  rcases p with ⟨a, b, c⟩
  cases a; cases b; cases c
  simp only [eval, Table.eval, Fin.cons_zero, Fin.cons_succ, Function.comp_def]
  ring

theorem round_boundary (p : Factors F (n + 1)) : p.round.boundary = p.booleanSum := by
  simp only [Message.boundary, round_eval, booleanSum, cubeSum]
  congr 1 <;> congr 1 <;> funext tail <;> exact eval_restrict p _ tail

end Factors
end Examples.OpeningReduction
