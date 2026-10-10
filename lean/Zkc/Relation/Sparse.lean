import Zkc.Algebra.LinearCombination
import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.OfFn

/-! Sparse linear maps. Only denotation uses a dense mathematical matrix.
Executable products visit each stored row and entry once. Contraction returns
sparse terms, allowing repeated columns; evaluating this view needs no dense
transpose or matrix. Array-backed vectors provide constant-time row access.
-/

set_option autoImplicit false

namespace Zkc.Relation.Sparse

open scoped BigOperators Matrix

abbrev Row (F : Type) (n : Nat) := List (Fin n × F)

variable {F : Type} [CommRing F] {m n : Nat}

def eval (row : Row F n) (z : Fin n → F) : F :=
  (row.map fun entry => entry.2 * z entry.1).sum

def coefficient (row : Row F n) (j : Fin n) : F :=
  eval row (fun k => if k = j then 1 else 0)

theorem eval_nil (z : Fin n → F) : eval [] z = 0 := rfl

theorem eval_cons (entry : Fin n × F) (row : Row F n) (z : Fin n → F) :
    eval (entry :: row) z = entry.2 * z entry.1 + eval row z := rfl

theorem eval_append (left right : Row F n) (z : Fin n → F) :
    eval (left ++ right) z = eval left z + eval right z := by
  simp [eval]

theorem eval_perm {left right : Row F n} (perm : left.Perm right) (z : Fin n → F) :
    eval left z = eval right z := List.Perm.sum_eq (perm.map _)

theorem eval_merge (j : Fin n) (a b : F) (row : Row F n) (z : Fin n → F) :
    eval ((j, a) :: (j, b) :: row) z = eval ((j, a + b) :: row) z := by
  simp only [eval_cons, add_mul, add_assoc]

theorem eval_zero_entry (j : Fin n) (row : Row F n) (z : Fin n → F) :
    eval ((j, 0) :: row) z = eval row z := by simp [eval_cons]

def eraseZeros [DecidableEq F] (row : Row F n) : Row F n :=
  row.filter (fun entry => entry.2 ≠ 0)

theorem eval_eraseZeros [DecidableEq F] (row : Row F n) (z : Fin n → F) :
    eval (eraseZeros row) z = eval row z := by
  induction row with
  | nil => rfl
  | cons entry row ih =>
      by_cases h : entry.2 = 0 <;> simp [eraseZeros, eval_cons, h, ← ih]

def scale (weight : F) (row : Row F n) : Row F n :=
  row.map fun entry => (entry.1, weight * entry.2)

theorem eval_scale (weight : F) (row : Row F n) (z : Fin n → F) :
    eval (scale weight row) z = weight * eval row z := by
  simp [eval, scale, List.map_map, Function.comp_def, mul_assoc, List.sum_map_mul_left]

def rename {k : Nat} (f : Fin n → Fin k) (row : Row F n) : Row F k :=
  row.map fun entry => (f entry.1, entry.2)

theorem eval_rename {k : Nat} (f : Fin n → Fin k) (row : Row F n) (z : Fin k → F) :
    eval (rename f row) z = eval row (z ∘ f) := by
  simp [eval, rename, List.map_map, Function.comp_def]

theorem eval_eq_sum (row : Row F n) (z : Fin n → F) :
    eval row z = ∑ j, coefficient row j * z j := by
  induction row with
  | nil => simp [eval, coefficient]
  | cons entry row ih =>
      unfold coefficient at ih
      simp only [eval_cons, coefficient, add_mul, Finset.sum_add_distrib]
      rw [← ih]
      congr 1
      simp [mul_ite]

theorem eval_linearCombination (row : Row F n) (z : Fin n → F) :
    eval row z = Zkc.Algebra.linearCombination (coefficient row) z :=
  eval_eq_sum row z

structure Matrix (F : Type) (m n : Nat) where
  rows : Vector (Row F n) m

namespace Matrix

def denote (matrix : Matrix F m n) : _root_.Matrix (Fin m) (Fin n) F :=
  fun i j => coefficient matrix.rows[i] j

def mul (matrix : Matrix F m n) (z : Fin n → F) : Vector F m :=
  Vector.ofFn fun i => eval matrix.rows[i] z

theorem mul_denote (matrix : Matrix F m n) (z : Fin n → F) (i : Fin m) :
    (matrix.mul z)[i] = (matrix.denote *ᵥ z) i := by
  simp [mul, denote, _root_.Matrix.mulVec, dotProduct, eval_eq_sum]

/-- This is a sparse linear form in the columns, not a dense coefficient array.
Construction is linear in the number of rows plus stored entries. -/
def contract (matrix : Matrix F m n) (weights : Fin m → F) : Row F n :=
  (List.ofFn fun i => scale (weights i) matrix.rows[i]).flatten

private theorem eval_flatten (rows : List (Row F n)) (z : Fin n → F) :
    eval rows.flatten z = (rows.map (eval · z)).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [eval_append, ih]

theorem eval_contract (matrix : Matrix F m n) (weights : Fin m → F) (z : Fin n → F) :
    eval (matrix.contract weights) z = ∑ i, weights i * eval matrix.rows[i] z := by
  simp [contract, eval_flatten, List.map_ofFn, Function.comp_def, eval_scale, Fin.sum_ofFn]

/-- The sparse contraction is precisely the existing finite matrix pullback. -/
theorem contract_linearCombination (matrix : Matrix F m n)
    (weights : Fin m → F) (z : Fin n → F) :
    eval (matrix.contract weights) z =
      Zkc.Algebra.linearCombination (weights ᵥ* matrix.denote) z := by
  rw [eval_contract, ← Zkc.Algebra.linearCombination_rows]
  simp only [Zkc.Algebra.linearCombination, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [eval_eq_sum]
  rfl

/-- A weighted row/column view: supplying polynomial basis weights specializes
this to a matrix point evaluation. No dense matrix is executed here. -/
def bilinear (matrix : Matrix F m n) (rows : Fin m → F) (columns : Fin n → F) : F :=
  eval (matrix.contract rows) columns

theorem bilinear_denote (matrix : Matrix F m n) (rows : Fin m → F) (columns : Fin n → F) :
    matrix.bilinear rows columns = ∑ i, ∑ j, rows i * matrix.denote i j * columns j := by
  unfold bilinear
  rw [eval_contract]
  simp only [eval_eq_sum, Finset.mul_sum, mul_assoc, denote]

def renameColumns {k : Nat} (f : Fin n → Fin k) (matrix : Matrix F m n) : Matrix F m k :=
  ⟨matrix.rows.map (rename f)⟩

theorem mul_renameColumns {k : Nat} (f : Fin n → Fin k) (matrix : Matrix F m n)
    (z : Fin k → F) (i : Fin m) :
    ((matrix.renameColumns f).mul z)[i] = (matrix.mul (z ∘ f))[i] := by
  simp [mul, renameColumns, eval_rename]

end Matrix
end Zkc.Relation.Sparse
