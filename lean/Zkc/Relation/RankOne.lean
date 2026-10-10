import Zkc.Relation.Encoding
import Zkc.Relation.Sparse

/-! Ordinary sparse R1CS with a separately fixed public/ONE layout. Homogeneous
row equations do not bind the statement. The bound family admits arbitrary
assignments and the embedding theorem accounts for every one of them.
-/

set_option autoImplicit false

namespace Zkc.Relation.RankOne

inductive Slot (publicCount witnessCount : Nat) where
  | one
  | publicInput (index : Fin publicCount)
  | witness (index : Fin witnessCount)
  deriving DecidableEq

/-- A bijection fixes every slot, including private and auxiliary coordinates.
It permits arbitrary physical ordering but no aliases or unclassified slots. -/
abbrev Layout (publicCount witnessCount columns : Nat) := Slot publicCount witnessCount ≃ Fin columns

variable {F : Type} [CommRing F] {p w m n : Nat}

def embed (layout : Layout p w n) (statement : Fin p → F) (witness : Fin w → F) : Fin n → F :=
  fun i => match layout.symm i with
    | .one => 1
    | .publicInput j => statement j
    | .witness j => witness j

def extract (layout : Layout p w n) (z : Fin n → F) : Fin w → F :=
  fun j => z (layout (.witness j))

def Bound (layout : Layout p w n) (statement : Fin p → F) (z : Fin n → F) : Prop :=
  z (layout .one) = 1 ∧ ∀ j, z (layout (.publicInput j)) = statement j

theorem embed_one (layout : Layout p w n) (statement : Fin p → F) (witness : Fin w → F) :
    embed layout statement witness (layout .one) = 1 := by simp [embed]

theorem embed_public (layout : Layout p w n) (statement : Fin p → F)
    (witness : Fin w → F) (j : Fin p) :
    embed layout statement witness (layout (.publicInput j)) = statement j := by simp [embed]

theorem extract_embed (layout : Layout p w n) (statement : Fin p → F) (witness : Fin w → F) :
    extract layout (embed layout statement witness) = witness := by
  funext j
  simp [extract, embed]

theorem embed_reorder (layout : Layout p w n) (permutation : Fin n ≃ Fin n)
    (statement : Fin p → F) (witness : Fin w → F) :
    embed (layout.trans permutation) statement witness ∘ permutation =
      embed layout statement witness := by
  funext i
  simp [embed]

theorem embed_bound (layout : Layout p w n) (statement : Fin p → F) (witness : Fin w → F) :
    Bound layout statement (embed layout statement witness) := by
  simp [Bound, embed]

/-- This reconstructs any bound assignment, not just an honest generator's output. -/
theorem embed_extract (layout : Layout p w n) (statement : Fin p → F)
    (z : Fin n → F) (bound : Bound layout statement z) :
    embed layout statement (extract layout z) = z := by
  funext i
  obtain ⟨slot, rfl⟩ := layout.surjective i
  cases slot with
  | one => simpa [embed] using bound.1.symm
  | publicInput j => simpa [embed] using (bound.2 j).symm
  | witness j => simp [embed, extract]

theorem bound_iff (layout : Layout p w n) (statement : Fin p → F) (z : Fin n → F) :
    Bound layout statement z ↔ ∃ witness, embed layout statement witness = z := by
  constructor
  · intro bound
    exact ⟨extract layout z, embed_extract layout statement z bound⟩
  · rintro ⟨witness, rfl⟩
    exact embed_bound layout statement witness

structure System (F : Type) (rows columns : Nat) where
  A : Sparse.Matrix F rows columns
  B : Sparse.Matrix F rows columns
  C : Sparse.Matrix F rows columns

namespace System

def Satisfies (system : System F m n) (z : Fin n → F) : Prop :=
  ∀ i : Fin m, Sparse.eval system.A.rows[i] z * Sparse.eval system.B.rows[i] z =
    Sparse.eval system.C.rows[i] z

def family (system : System F m n) (layout : Layout p w n) : PIR.Relation.Family where
  Statement := Fin p → F
  Witness := Fin w → F
  holds statement witness := system.Satisfies (embed layout statement witness)

def boundFamily (system : System F m n) (layout : Layout p w n) : PIR.Relation.Family where
  Statement := Fin p → F
  Witness := Fin n → F
  holds statement z := Bound layout statement z ∧ system.Satisfies z

def encoding (system : System F m n) (layout : Layout p w n) :
    Encoding (system.family layout) (system.boundFamily layout) where
  statementMap := id
  corresponds statement witness z := embed layout statement witness = z
  complete statement witness h := ⟨embed layout statement witness,
    ⟨embed_bound layout statement witness, h⟩, rfl⟩
  sound statement z h := by
    have reconstruction := embed_extract layout statement z h.1
    refine ⟨extract layout z, ?_, reconstruction⟩
    change system.Satisfies (embed layout statement (extract layout z))
    rw [reconstruction]
    exact h.2

theorem satisfies_zero (system : System F m n) : system.Satisfies (fun _ => 0) := by
  intro i
  simp [Sparse.eval]

theorem zero_not_bound [Nontrivial F] (layout : Layout p w n) (statement : Fin p → F) :
    ¬ Bound layout statement (fun _ => 0) := by simp [Bound]

/-- Matrix normalization is sound when it preserves coefficient denotation.
Sparse permutation/merge/zero laws can discharge this without a dense execution. -/
theorem satisfies_congr (left right : System F m n)
    (ha : left.A.denote = right.A.denote) (hb : left.B.denote = right.B.denote)
    (hc : left.C.denote = right.C.denote) (z : Fin n → F) :
    left.Satisfies z ↔ right.Satisfies z := by
  simp only [Satisfies, Sparse.eval_eq_sum]
  change (∀ i, (∑ j, left.A.denote i j * z j) * (∑ j, left.B.denote i j * z j) =
    ∑ j, left.C.denote i j * z j) ↔ _
  rw [ha, hb, hc]
  rfl

/-- Exact rows retain all three linear forms together. -/
def row (system : System F m n) (i : Fin m) :
    Sparse.Row F n × Sparse.Row F n × Sparse.Row F n :=
  (system.A.rows[i], system.B.rows[i], system.C.rows[i])

/-- Removing constraints is sound in this direction only when each retained
row occurs in the source. The converse coverage is needed for equivalence. -/
theorem satisfies_of_rowCover {k : Nat} (left : System F m n)
    (right : System F k n)
    (cover : ∀ j, ∃ i, left.row i = right.row j) (z : Fin n → F)
    (h : left.Satisfies z) : right.Satisfies z := by
  intro j
  obtain ⟨i, same⟩ := cover j
  simp only [row, Prod.mk.injEq] at same
  simpa only [same.1, same.2.1, same.2.2] using h i

/-- Deduplicating or permuting exact rows preserves every assignment when
each side covers the other's rows. Row counts may differ. This is a law for
the transformation; it does not verify the native deduplication algorithm. -/
theorem satisfies_sameRows {k : Nat} (left : System F m n)
    (right : System F k n)
    (forward : ∀ j, ∃ i, left.row i = right.row j)
    (backward : ∀ i, ∃ j, right.row j = left.row i) (z : Fin n → F) :
    left.Satisfies z ↔ right.Satisfies z :=
  ⟨satisfies_of_rowCover left right forward z,
    satisfies_of_rowCover right left backward z⟩

def renameColumns (system : System F m n) (permutation : Fin n ≃ Fin n) : System F m n :=
  ⟨system.A.renameColumns permutation, system.B.renameColumns permutation,
    system.C.renameColumns permutation⟩

theorem satisfies_renameColumns (system : System F m n) (permutation : Fin n ≃ Fin n)
    (z : Fin n → F) :
    (system.renameColumns permutation).Satisfies z ↔ system.Satisfies (z ∘ permutation) := by
  simp [Satisfies, renameColumns, Sparse.Matrix.renameColumns, Sparse.eval_rename]

/-- Reordering columns is harmless only when the independently fixed layout
is transported with them. Reordering public values alone has no such law. -/
theorem family_reorder (system : System F m n) (layout : Layout p w n)
    (permutation : Fin n ≃ Fin n) (statement : Fin p → F) (witness : Fin w → F) :
    ((system.renameColumns permutation).family (layout.trans permutation)).holds statement witness ↔
      (system.family layout).holds statement witness := by
  change (system.renameColumns permutation).Satisfies
    (embed (layout.trans permutation) statement witness) ↔ _
  rw [satisfies_renameColumns, embed_reorder]
  rfl

end System
end Zkc.Relation.RankOne
