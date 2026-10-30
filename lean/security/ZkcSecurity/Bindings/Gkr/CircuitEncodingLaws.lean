module

public import ZkcSecurity.Bindings.Gkr.LayoutReadback
public import Zkc.Protocols.Gkr.Source.BlockLaws
public import ZkcSecurity.Bindings.Gkr.Circuit

@[expose] public section

/-! General encoding laws for the independent circuit mathematics. The first
coordinate is the most significant bit; selecting a prefix leaves the entire
suffix cube, in its original order. -/

namespace ZkcSecurity.Realizations.Gkr.HonestCircuit
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured.GkrSourceLaws
open ZkcSecurity.Examples.Components

variable {F : Type}

/-- Concatenated Boolean points have row-major flat indices. -/
theorem index_point (m n : Nat) (fixed : Fin m → Bool) (tail : Fin n → Bool) :
    (index (n + m) (Quadratic.point m fixed tail)).val =
      (index m fixed).val * 2 ^ n + (index n tail).val := by
  induction m with
  | zero => simp [Quadratic.point, index]
  | succ m ih =>
    simp only [Quadratic.point, index, Fin.cons_zero]
    simp only [Function.comp_def, Fin.cons_succ] at ih ⊢
    change (if fixed 0 then 2 ^ (n + m) else 0) +
      (index (n + m) (Quadratic.point m (fixed ∘ Fin.succ) tail)).val =
        ((if fixed 0 then 2 ^ m else 0) + (index m (fixed ∘ Fin.succ)).val) * 2 ^ n +
          (index n tail).val
    rw [ih, Nat.pow_add]
    cases first : fixed 0 <;> simp only [first, Bool.false_eq_true, ite_true, ite_false,
      zero_add, zero_mul]
    ring

/-- Any full prefix block of an encoded table is the encoded suffix table. -/
theorem block_encode (m n : Nat) (table : Table F (n + m))
    (position : Fin (2 ^ m)) :
    block (GkrRoundsLayout.encode table) position.val (2 ^ n) =
      GkrRoundsLayout.encode (fun tail => table (Quadratic.point m (vertex m position) tail)) := by
  have inside : (position.val + 1) * 2 ^ n ≤ (GkrRoundsLayout.encode table).length := by
    simp only [GkrRoundsLayout.encode, List.length_ofFn, Nat.pow_add]
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left (2 ^ n) position.isLt
  apply List.ext_getElem
  · rw [block_length _ _ _ inside]
    simp [GkrRoundsLayout.encode]
  · intro i hi hj
    have ib : i < 2 ^ n := by simpa [GkrRoundsLayout.encode] using hj
    simp only [block, List.getElem_take, List.getElem_drop, GkrRoundsLayout.encode,
      List.getElem_ofFn]
    congr 1
    apply (Equiv.mk (index (n + m)) (vertex (n + m)) (vertex_index _) (index_vertex _)).injective
    apply Fin.ext
    change (index (n + m) _).val = (index (n + m) _).val
    simp only [index_vertex, index_point]

variable [Field F]

/-- Summing an encoded Boolean table gives its independent cube sum. -/
theorem sum_encode {n : Nat} (table : Table F n) :
    (GkrRoundsLayout.encode table).sum = booleanSum table :=
  (booleanSum_ofList? _ _ (GkrRoundsLayout.decode_encode table)).symm

/-- The scalar gate formula agrees with the circuit's independent gate table. -/
theorem gate_formula {width : Nat} (add mul : Table F (width + width))
    (below : Table F width) (pair : Fin (width + width) → Bool) :
    Zkc.Protocols.AlgebraicRounds.Gate.value (add pair) (mul pair)
      (GkrRoundsLayout.replicate width width below pair)
      (GkrRoundsLayout.tile width width below pair) =
        Zkc.Protocols.Gkr.gates add mul below pair := by
  simp only [GkrRoundsLayout.replicate, GkrRoundsLayout.tile, Circuit.layout_front,
    Circuit.layout_back, Zkc.Protocols.AlgebraicRounds.Gate.value,
    Zkc.Protocols.Gkr.gates, Zkc.Protocols.Gkr.sumTable, Zkc.Protocols.Gkr.productTable]
  ring

end ZkcSecurity.Realizations.Gkr.HonestCircuit
