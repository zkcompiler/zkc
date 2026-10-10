import Zkc.Relation.RankOne

/-! Zero row/column extension for multilinear consumers. Added columns do not
constrain the extra assignment cells; restriction recovers every original
assignment, not merely the result of an honest zero-padding procedure. -/

set_option autoImplicit false

namespace Zkc.Relation

variable {F : Type} [CommRing F] {m n : Nat}

namespace Sparse.Matrix

def pad (matrix : Matrix F m n) (extraRows extraColumns : Nat) :
    Matrix F (m + extraRows) (n + extraColumns) :=
  ⟨Vector.ofFn fun i => if h : i.val < m then
    rename (Fin.castAdd extraColumns) matrix.rows[(⟨i.val, h⟩ : Fin m)] else []⟩

theorem eval_pad_old (matrix : Matrix F m n) (extraRows extraColumns : Nat)
    (z : Fin (n + extraColumns) → F) (i : Fin m) :
    eval (matrix.pad extraRows extraColumns).rows[i.castAdd extraRows] z =
      eval matrix.rows[i] (z ∘ Fin.castAdd extraColumns) := by
  simp [pad, eval_rename]

theorem eval_pad_new (matrix : Matrix F m n) (extraRows extraColumns : Nat)
    (z : Fin (n + extraColumns) → F) (i : Fin (m + extraRows))
    (h : m ≤ i.val) :
    eval (matrix.pad extraRows extraColumns).rows[i] z = 0 := by
  simp [pad, Nat.not_lt.mpr h, eval_nil]

end Sparse.Matrix

namespace RankOne.System

/-- Append arbitrary A rows with zero B and C. These rows record values in an
interpolant without imposing an additional equation on the assignment. -/
def appendTrivialRows {k : Nat} (system : System F m n)
    (extra : Sparse.Matrix F k n) : System F (m + k) n :=
  ⟨⟨Vector.ofFn fun i => if h : i.val < m then system.A.rows[(⟨i.val, h⟩ : Fin m)]
      else extra.rows[(⟨i.val - m, by omega⟩ : Fin k)]⟩,
   ⟨Vector.ofFn fun i => if h : i.val < m then system.B.rows[(⟨i.val, h⟩ : Fin m)]
      else []⟩,
   ⟨Vector.ofFn fun i => if h : i.val < m then system.C.rows[(⟨i.val, h⟩ : Fin m)]
      else []⟩⟩

/-- In particular, appended ONE/public rows with B=C=0 preserve every satisfying
assignment; they do not themselves establish ONE or public-input binding. -/
theorem satisfies_appendTrivialRows {k : Nat} (system : System F m n)
    (extra : Sparse.Matrix F k n) (z : Fin n → F) :
    (system.appendTrivialRows extra).Satisfies z ↔ system.Satisfies z := by
  constructor
  · intro h i
    simpa [appendTrivialRows] using h (i.castAdd k)
  · intro h i
    by_cases old : i.val < m
    · simpa [appendTrivialRows, old] using h ⟨i.val, old⟩
    · simp [appendTrivialRows, old, Sparse.eval_nil]

def pad (system : System F m n) (extraRows extraColumns : Nat) :
    System F (m + extraRows) (n + extraColumns) :=
  ⟨system.A.pad extraRows extraColumns, system.B.pad extraRows extraColumns,
    system.C.pad extraRows extraColumns⟩

/-- Padding preserves satisfaction for every target assignment, including
arbitrary values in the newly unused columns. -/
theorem satisfies_pad (system : System F m n) (extraRows extraColumns : Nat)
    (z : Fin (n + extraColumns) → F) :
    (system.pad extraRows extraColumns).Satisfies z ↔
      system.Satisfies (z ∘ Fin.castAdd extraColumns) := by
  constructor
  · intro h i
    simpa only [pad, Sparse.Matrix.eval_pad_old] using h (i.castAdd extraRows)
  · intro h i
    by_cases old : i.val < m
    · have index : (⟨i.val, old⟩ : Fin m).castAdd extraRows = i := Fin.ext rfl
      rw [← index]
      simpa only [pad, Sparse.Matrix.eval_pad_old] using h ⟨i.val, old⟩
    · have fresh := Nat.le_of_not_gt old
      simp only [pad, Sparse.Matrix.eval_pad_new _ _ _ _ i fresh, mul_zero]

end RankOne.System

/-- Appended assignment cells are zero in the executable consumer. -/
def zeroExtend (extraColumns : Nat) (z : Fin n → F) : Fin (n + extraColumns) → F :=
  fun i => if h : i.val < n then z ⟨i.val, h⟩ else 0

theorem zeroExtend_restrict (extraColumns : Nat) (z : Fin n → F) :
    zeroExtend extraColumns z ∘ Fin.castAdd extraColumns = z := by
  funext i
  simp [zeroExtend]

theorem satisfies_zeroExtend (system : RankOne.System F m n)
    (extraRows extraColumns : Nat) (z : Fin n → F) :
    (system.pad extraRows extraColumns).Satisfies (zeroExtend extraColumns z) ↔
      system.Satisfies z := by
  rw [RankOne.System.satisfies_pad, zeroExtend_restrict]

/-- ONE and public coordinates retain their exact old positions. This does not
assign an extra public meaning to unused padding coordinates. -/
theorem bound_zeroExtend {p w : Nat} (layout : RankOne.Layout p w n)
    (statement : Fin p → F) (extraColumns : Nat) (z : Fin n → F) :
    RankOne.Bound layout statement (zeroExtend extraColumns z ∘ Fin.castAdd extraColumns) ↔
      RankOne.Bound layout statement z := by
  rw [zeroExtend_restrict]

end Zkc.Relation
