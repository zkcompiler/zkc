import Zkc.Relation.AIR
import Zkc.Algebra.MultisetFingerprint

/-! An accumulator for the product fingerprint of one column in the finite,
noncyclic AIR relation. The challenge and terminal are statement values.
The AIR relation records neither that the value column was committed before the
challenge was sampled nor how the auxiliary column was committed and checked;
those are premises of the argument that uses this relation. -/

set_option autoImplicit false

namespace Zkc.Relation.AIR.ProductConnection

open Polynomial Zkc.Algebra.MultisetFingerprint

variable {F : Type} [CommRing F] {p c : Nat}

def difference (left right : Expr F p c) : Expr F p c :=
  .add left (.mul (.constant (-1)) right)

/-- On the first row `accumulator = z - value`; on each transition
`accumulator' = accumulator * (z - value')`; on the last row
`accumulator = terminal`. No constraint divides. -/
def constraints (challenge terminal : Fin p) (value accumulator : Fin c) :
    List (Constraint F p c) :=
  [⟨.first, difference (.read 0 accumulator)
      (difference (.publicInput challenge) (.read 0 value))⟩,
   ⟨.transition 1, difference (.read 1 accumulator)
      (.mul (.read 0 accumulator) (difference (.publicInput challenge) (.read 1 value)))⟩,
   ⟨.last, difference (.read 0 accumulator) (.publicInput terminal)⟩]

@[simp] theorem eval_difference (left right : Expr F p c) (statement : Fin p → F)
    (read : Nat × Fin c → F) :
    (difference left right).eval statement read =
      left.eval statement read - right.eval statement read := by
  simp [difference, Expr.eval, sub_eq_add_neg]

@[simp] theorem maxOffset_difference (left right : Expr F p c) :
    (difference left right).maxOffset = max left.maxOffset right.maxOffset := by
  simp [difference, Expr.maxOffset]

/-- The actual trace column, read by natural row index. -/
def column {n : Nat} (trace : Fin n → Fin c → F) (index : Fin c) (row : Nat) : F :=
  if h : row < n then trace ⟨row, h⟩ index else 0

theorem traceRead_eq_column {n : Nat} (trace : Fin n → Fin c → F) (row : Fin n)
    (read : Nat × Fin c) :
    Expr.traceRead trace row read = column trace read.2 (row.val + read.1) := rfl

theorem prod_column {n : Nat} (trace : Fin n → Fin c → F) (index : Fin c) (z : F) :
    ∏ row ∈ Finset.range n, (z - column trace index row) =
      ∏ row : Fin n, (z - trace row index) := by
  rw [← Fin.prod_univ_eq_prod_range]
  exact Finset.prod_congr rfl fun row _ => by simp [column]

/-- Every satisfying trace, with arbitrary auxiliary values, exposes the
fingerprint evaluation of its value column as the terminal. -/
theorem terminal_eq_eval (challenge terminal : Fin p) (value accumulator : Fin c)
    (height : Nat) (statement : Fin p → F) (trace : Fin (height + 1) → Fin c → F)
    (holds : (family (constraints challenge terminal value accumulator) height).holds
      statement trace) :
    statement terminal =
      (ofMultiset (rowValues Finset.univ fun row => trace row value)).eval
        (statement challenge) := by
  have first := holds _ List.mem_cons_self ⟨0, Nat.succ_pos _⟩ rfl
  have transition := holds _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have last := holds _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    (Fin.last height) last_active
  simp [Expr.evaluateAt, Expr.maxOffset, Expr.eval, traceRead_eq_column, sub_eq_zero]
    at first last
  have step : ∀ i < height, column trace accumulator (i + 1) =
      column trace accumulator i * (statement challenge - column trace value (i + 1)) := by
    intro i bound
    have atRow := transition ⟨i, by omega⟩ (show i + 1 < height + 1 by omega)
    simpa [Expr.evaluateAt, Expr.maxOffset, Expr.eval, traceRead_eq_column, sub_eq_zero,
      show i + 1 ≤ height by omega] using atRow
  have unrolled := recurrence_eq_prefix_prod _ _ height step height le_rfl
  rw [eval_ofMultiset_rowValues, ← prod_column, Finset.prod_range_succ', ← last, unrolled,
    first, mul_comm]

/-- An honest accumulator satisfies the constraints for every statement whose
terminal is the fingerprint evaluation. -/
theorem holds_of_prefix (challenge terminal : Fin p) (value accumulator : Fin c)
    (height : Nat) (statement : Fin p → F) (trace : Fin (height + 1) → Fin c → F)
    (honest : ∀ row ≤ height, column trace accumulator row =
      ∏ i ∈ Finset.range (row + 1), (statement challenge - column trace value i))
    (published : statement terminal =
      (ofMultiset (rowValues Finset.univ fun row => trace row value)).eval
        (statement challenge)) :
    (family (constraints challenge terminal value accumulator) height).holds
      statement trace := by
  intro constraint member
  simp only [constraints, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> intro row active <;> simp only [Scope.Active] at active
  · have atFirst := honest 0 (Nat.zero_le _)
    simp [Expr.evaluateAt, Expr.maxOffset, Expr.eval, traceRead_eq_column, active, atFirst]
  · have next := honest (row.val + 1) (by omega)
    rw [Finset.prod_range_succ, ← honest row.val (by omega)] at next
    simp [Expr.evaluateAt, Expr.maxOffset, Expr.eval, traceRead_eq_column, next,
      show row.val + 1 ≤ height by omega]
  · rw [eval_ofMultiset_rowValues, ← prod_column, ← honest height le_rfl] at published
    simp [Expr.evaluateAt, Expr.maxOffset, Expr.eval, traceRead_eq_column, published,
      show row.val = height by omega]

/-- The exact connection between two accumulator AIRs sharing a challenge and a
terminal. Either the original value multisets are equal, or the challenge is a
root of a nonzero polynomial determined by the value columns alone. -/
theorem connected_or_root [IsDomain F] {p' c' : Nat}
    (leftChallenge leftTerminal : Fin p) (leftValue leftAccumulator : Fin c)
    (rightChallenge rightTerminal : Fin p') (rightValue rightAccumulator : Fin c')
    {leftHeight rightHeight : Nat}
    (leftStatement : Fin p → F) (rightStatement : Fin p' → F)
    (leftTrace : Fin (leftHeight + 1) → Fin c → F)
    (rightTrace : Fin (rightHeight + 1) → Fin c' → F)
    (leftHolds : (family (constraints leftChallenge leftTerminal leftValue leftAccumulator)
      leftHeight).holds leftStatement leftTrace)
    (rightHolds : (family (constraints rightChallenge rightTerminal rightValue
      rightAccumulator) rightHeight).holds rightStatement rightTrace)
    (sameChallenge : leftStatement leftChallenge = rightStatement rightChallenge)
    (sameTerminal : leftStatement leftTerminal = rightStatement rightTerminal) :
    rowValues Finset.univ (fun row => leftTrace row leftValue) =
        rowValues Finset.univ (fun row => rightTrace row rightValue) ∨
      (ofMultiset (rowValues Finset.univ fun row => leftTrace row leftValue) -
        ofMultiset (rowValues Finset.univ fun row => rightTrace row rightValue)) ≠ 0 ∧
      (ofMultiset (rowValues Finset.univ fun row => leftTrace row leftValue) -
        ofMultiset (rowValues Finset.univ fun row => rightTrace row rightValue)).IsRoot
          (leftStatement leftChallenge) := by
  by_cases same : rowValues Finset.univ (fun row => leftTrace row leftValue) =
      rowValues Finset.univ (fun row => rightTrace row rightValue)
  · exact Or.inl same
  refine Or.inr ⟨ofMultiset_sub_ne_zero same, ?_⟩
  rw [IsRoot, eval_sub, sub_eq_zero,
    ← terminal_eq_eval _ _ _ _ _ _ _ leftHolds, sameTerminal, sameChallenge,
    ← terminal_eq_eval _ _ _ _ _ _ _ rightHolds]

end Zkc.Relation.AIR.ProductConnection
