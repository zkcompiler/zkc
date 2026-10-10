import Zkc.Polynomial.Quadratic

/-! Boolean value tables, with the first coordinate split first. The weighted
quadratic is a logical reference for a virtual expression, not a verifier input
or a prescribed implementation layout. -/

set_option autoImplicit false

namespace Composition

inductive Table (F : Type) : Nat → Type where
  | leaf : F → Table F 0
  | fork {n : Nat} : Table F n → Table F n → Table F (n + 1)
  deriving Repr

namespace Table

open Zkc.Polynomial

variable {F : Type} [CommRing F] {n : Nat}

def eval : {n : Nat} → Table F n → (Fin n → F) → F
  | 0, .leaf value, _ => value
  | _ + 1, .fork lo hi, point =>
      (1 - point 0) * lo.eval (point ∘ Fin.succ) + point 0 * hi.eval (point ∘ Fin.succ)

def eqWeight : (n : Nat) → (Fin n → F) → (Fin n → F) → F
  | 0, _, _ => 1
  | n + 1, point, query =>
      ((1 - point 0) * (1 - query 0) + point 0 * query 0) *
        eqWeight n (point ∘ Fin.succ) (query ∘ Fin.succ)

/-- Materialize `eq(point, x) * table(x)` only for the semantic proof and
honest reference prover. Each coordinate has degree at most two. -/
def weighted : {n : Nat} → Table F n → (Fin n → F) → Quadratic F n
  | 0, .leaf value, _ => .constant value
  | _ + 1, .fork lo hi, point =>
      let a := lo.weighted (point ∘ Fin.succ)
      let b := hi.weighted (point ∘ Fin.succ)
      let delta := Quadratic.add b (Quadratic.scale (-1) a)
      .node (Quadratic.scale (1 - point 0) a)
        (Quadratic.add (Quadratic.scale (1 - point 0) delta)
          (Quadratic.scale (2 * point 0 - 1) a))
        (Quadratic.scale (2 * point 0 - 1) delta)

theorem weighted_eval (table : Table F n) (point query : Fin n → F) :
    (table.weighted point).eval query = eqWeight n point query * table.eval query := by
  induction table with
  | leaf value => simp [weighted, Quadratic.eval, eqWeight, eval]
  | fork lo hi ilo ihi =>
      simp only [weighted, Quadratic.eval, Quadratic.eval_add, Quadratic.eval_scale,
        ilo, ihi, eqWeight, eval]
      ring

/-- Multilinear interpolation at an arbitrary field point, not only a Boolean
point. This is the bridge from evaluation claims to a sumcheck statement. -/
theorem weighted_sum (table : Table F n) (point : Fin n → F) :
    (table.weighted point).booleanSum = table.eval point := by
  induction table with
  | leaf value => rfl
  | fork lo hi ilo ihi =>
      rw [weighted, Quadratic.booleanSum_split]
      simp only [Quadratic.booleanSum_restrict, Quadratic.booleanSum_add,
        Quadratic.booleanSum_scale, ilo, ihi, eval]
      ring

theorem eval_fork_zero (lo hi : Table F n) (tail : Fin n → F) :
    (fork lo hi).eval (Fin.cons 0 tail) = lo.eval tail := by
  simp [eval, Function.comp_def]

theorem eval_fork_one (lo hi : Table F n) (tail : Fin n → F) :
    (fork lo hi).eval (Fin.cons 1 tail) = hi.eval tail := by
  simp [eval, Function.comp_def]

end Table
end Composition
