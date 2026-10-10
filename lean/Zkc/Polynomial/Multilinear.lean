import Zkc.Polynomial.Quadratic

/-! Ordered Boolean-table semantics and its degree-two coefficient realization.

The first coordinate is the most significant table-index bit. A table denotes
its multilinear extension before any product is formed. Products retain both
factor occurrences, including two occurrences of the same table. The dense
coefficient conversion is a reference proof bridge, not a native storage plan.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear

abbrev Table (F : Type) (n : Nat) := (Fin n → Bool) → F

/-- Ordered binary indexing: the first coordinate selects the low/high half. -/
def index : (n : Nat) → (Fin n → Bool) → Fin (2 ^ n)
  | 0, _ => ⟨0, by decide⟩
  | n + 1, bits =>
      let tail := index n (bits ∘ Fin.succ)
      ⟨(if bits 0 then 2 ^ n else 0) + tail.val, by
        have bound := tail.isLt
        rw [Nat.pow_succ]
        split <;> omega⟩

/-- Every flat input position has exactly one ordered Boolean coordinate. -/
def vertex : (n : Nat) → Fin (2 ^ n) → Fin n → Bool
  | 0, _ => Fin.elim0
  | n + 1, position =>
      if low : position.val < 2 ^ n then
        Fin.cons false (vertex n ⟨position.val, low⟩)
      else Fin.cons true (vertex n ⟨position.val - 2 ^ n, by
        have bound := position.isLt
        simp only [Nat.pow_succ] at bound
        omega⟩)

theorem index_vertex (n : Nat) (position : Fin (2 ^ n)) :
    index n (vertex n position) = position := by
  induction n with
  | zero => exact Fin.eq_zero position |>.symm
  | succ n ih =>
      apply Fin.ext
      simp only [vertex]
      split
      · simp [index, Function.comp_def, ih]
      · rename_i high
        simp only [index, Fin.cons_zero, ↓reduceIte]
        have tail := congrArg Fin.val (ih ⟨position.val - 2 ^ n, by
          have bound := position.isLt
          simp only [Nat.pow_succ] at bound
          omega⟩)
        simp [Function.comp_def, tail, Nat.add_sub_of_le (by omega : 2 ^ n ≤ position.val)]

theorem vertex_index (n : Nat) (bits : Fin n → Bool) :
    vertex n (index n bits) = bits := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      have tailBound := (index n (bits ∘ Fin.succ)).isLt
      cases first : bits 0 with
      | false =>
          simp only [index, first, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, vertex,
            tailBound, ih]
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact first.symm
          · rfl
      | true =>
          have high : ¬ 2 ^ n + (index n (bits ∘ Fin.succ)).val < 2 ^ n := by omega
          simp only [index, first, ↓reduceIte, vertex, high, Nat.add_sub_cancel_left, ih]
          funext i
          refine Fin.cases ?_ (fun j => ?_) i
          · exact first.symm
          · rfl

def ofVector {F : Type} {n : Nat} (values : Fin (2 ^ n) → F) : Table F n :=
  fun bits => values (index n bits)

theorem ofVector_vertex {F : Type} {n : Nat} (values : Fin (2 ^ n) → F)
    (position : Fin (2 ^ n)) : ofVector values (vertex n position) = values position := by
  simp [ofVector, index_vertex]

variable {F : Type} [CommRing F]

def extension : (n : Nat) → Table F n → (Fin n → F) → F
  | 0, table, _ => table Fin.elim0
  | n + 1, table, point =>
      (1 - point 0) * extension n (fun tail => table (Fin.cons false tail)) (point ∘ Fin.succ) +
      point 0 * extension n (fun tail => table (Fin.cons true tail)) (point ∘ Fin.succ)

def booleanPoint {n : Nat} (bits : Fin n → Bool) : Fin n → F :=
  fun i => if bits i then 1 else 0

theorem extension_boolean (n : Nat) (table : Table F n) (bits : Fin n → Bool) :
    extension n table (booleanPoint bits) = table bits := by
  induction n with
  | zero =>
      change table Fin.elim0 = table bits
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      have tail : booleanPoint (F := F) bits ∘ Fin.succ = booleanPoint (bits ∘ Fin.succ) := rfl
      simp only [extension, tail, ih, booleanPoint]
      cases first : bits 0 <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_zero, one_mul,
        zero_mul, add_zero, sub_self, zero_add]
      all_goals
        congr 1
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact first.symm
        · rfl

theorem extension_sub (n : Nat) (left right : Table F n) (point : Fin n → F) :
    extension n (fun bits => left bits - right bits) point =
      extension n left point - extension n right point := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [extension, ih]; ring

theorem extension_one (n : Nat) (point : Fin n → F) :
    extension n (fun _ => (1 : F)) point = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [extension, ih]; ring

/-- Convert one table extension to the existing coefficient object. -/
def coefficients : (n : Nat) → Table F n → Quadratic F n
  | 0, table => .constant (table Fin.elim0)
  | n + 1, table =>
      let low := coefficients n (fun tail => table (Fin.cons false tail))
      let high := coefficients n (fun tail => table (Fin.cons true tail))
      .node low (Quadratic.add high (low.scale (-1))) (low.scale 0)

theorem coefficients_eval (n : Nat) (table : Table F n) (point : Fin n → F) :
    (coefficients n table).eval point = extension n table point := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coefficients, Quadratic.eval, Quadratic.eval_add, Quadratic.eval_scale, ih, extension]
      ring

/-- Multiply extensions, rather than extending the pointwise product table. -/
def productCoefficients : (n : Nat) → Table F n → Table F n → Quadratic F n
  | 0, left, right => .constant (left Fin.elim0 * right Fin.elim0)
  | n + 1, left, right =>
      let a := fun tail => left (Fin.cons false tail)
      let da := fun tail => left (Fin.cons true tail) - left (Fin.cons false tail)
      let b := fun tail => right (Fin.cons false tail)
      let db := fun tail => right (Fin.cons true tail) - right (Fin.cons false tail)
      .node (productCoefficients n a b)
        (Quadratic.add (productCoefficients n a db) (productCoefficients n da b))
        (productCoefficients n da db)

theorem productCoefficients_eval (n : Nat) (left right : Table F n) (point : Fin n → F) :
    (productCoefficients n left right).eval point = extension n left point * extension n right point := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [productCoefficients, Quadratic.eval, Quadratic.eval_add, ih, extension_sub, extension]
      ring

end Zkc.Polynomial.Multilinear
