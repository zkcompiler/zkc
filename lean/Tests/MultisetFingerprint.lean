import Zkc.Algebra.MultisetFingerprint
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

namespace Tests.MultisetFingerprint

open Polynomial Zkc.Algebra.MultisetFingerprint

private abbrev F := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- A row permutation leaves the fingerprint unchanged, before any evaluation.
private def left : Fin 4 → F := ![1, 2, 2, 5]
private def right : Fin 4 → F := ![2, 5, 1, 2]

example : ofMultiset (rowValues Finset.univ left) = ofMultiset (rowValues Finset.univ right) :=
  congrArg ofMultiset <| rowValues_univ_of_equiv
    (Equiv.swap (0 : Fin 4) 2 |>.trans (Equiv.swap (1 : Fin 4) 3)) left right (by decide)

example (first second : List F) (permuted : first.Perm second) :
    ofMultiset (first : Multiset F) = ofMultiset second :=
  congrArg ofMultiset (Multiset.coe_eq_coe.mpr permuted)

-- The converse recovers an actual value-preserving row bijection.
example : ∃ e : Fin 4 ≃ Fin 4, ∀ i, right (e i) = left i :=
  (rowValues_univ_eq_iff left right).mp (by decide)

-- Same support, different multiplicity: the polynomials differ.
example : ofMultiset ({1, 1, 2} : Multiset F) ≠ ofMultiset {1, 2, 2} :=
  fun same => absurd (ofMultiset_eq_iff.mp same) (by decide)

-- The integral-domain premise is necessary: over `ZMod 4`,
-- `(X - 2)^2 = X^2` although the multisets differ.
example : ofMultiset ({0, 0} : Multiset (ZMod 4)) = ofMultiset {2, 2} ∧
    ({0, 0} : Multiset (ZMod 4)) ≠ {2, 2} := by
  refine ⟨?_, by decide⟩
  have twice : (2 : ZMod 4) + 2 = 0 := by decide
  have square : (2 : ZMod 4) * 2 = 0 := by decide
  calc ofMultiset ({0, 0} : Multiset (ZMod 4)) = X * X := by simp [ofMultiset_apply]
    _ = X * X - C (2 + 2) * X + C (2 * 2) := by rw [twice, square]; simp
    _ = ofMultiset {2, 2} := by simp only [ofMultiset_apply, C_add, C_mul]; simp; ring

-- A fixed challenge can collide, including through a zero factor. The collision
-- set of these equal-size multisets has fewer than two points.
example : ({0, 1} : Multiset F) ≠ {0, 2} ∧
    (ofMultiset ({0, 1} : Multiset F)).eval 0 = (ofMultiset {0, 2}).eval 0 ∧
    (ofMultiset ({0, 1} : Multiset F)).eval 3 ≠ (ofMultiset {0, 2}).eval 3 := by
  refine ⟨by decide, by simp, ?_⟩
  simp
  decide

example (points : Finset F)
    (agree : ∀ z ∈ points,
      (ofMultiset ({0, 1} : Multiset F)).eval z = (ofMultiset {0, 2}).eval z) :
    points.card ≤ 1 := by
  have bound := agreeing_card_lt (s := ({0, 1} : Multiset F)) (t := {0, 2}) (by decide) rfl
    points agree
  simp at bound
  omega

-- Distinct cardinalities are not cancelled: the bound is the larger size.
example (points : Finset F)
    (agree : ∀ z ∈ points,
      (ofMultiset ({4} : Multiset F)).eval z = (ofMultiset {4, 4, 4}).eval z) :
    points.card ≤ 3 :=
  agreeing_card_le (by decide) points agree

-- Unlike reciprocal sums, repeated values need no characteristic bound:
-- in characteristic two, two copies of 0 and of 1 are separated at every point.
example (z : ZMod 2) :
    (ofMultiset ({0, 0} : Multiset (ZMod 2))).eval z ≠ (ofMultiset {1, 1}).eval z := by
  revert z
  simp
  decide

-- Every witness of the recurrence reaches the same terminal, here through a
-- zero factor at row 1 (`3 - 3 = 0`); later rows cannot recover a nonzero value.
private def column : ℕ → F := fun i => if i = 0 then 1 else if i = 1 then 3 else 2

example (state : ℕ → F) (start : state 0 = 1)
    (step : ∀ i < 3, state (i + 1) = state i * (3 - column i)) : state 3 = 0 := by
  rw [recurrence_eq_eval column 3 state 3 start step, eval_ofMultiset_rowValues]
  simp [Finset.prod_range_succ, column]

example (state : ℕ → F) (start : state 0 = 1)
    (step : ∀ i < 3, state (i + 1) = state i * (3 - column i)) : state 2 = 0 := by
  rw [recurrence_eq_prefix_prod _ state 3 step 2 (by decide), start]
  simp [Finset.prod_range_succ, column]

-- A ratio recurrence `next * (z - b) = current * (z - a)` is not determined at a
-- shared zero factor; this is why each side keeps its own forward product.
example : ∃ first second : F, first ≠ second ∧
    first * (3 - 3) = 1 * (3 - 3) ∧ second * (3 - 3) = 1 * (3 - 3) :=
  ⟨0, 1, by decide⟩

-- Padding rows are excluded by their selector, whatever values they carry.
private def padded : ℕ → F := fun i => if i < 2 then i + 1 else 6

example (state : ℕ → F) (start : state 0 = 1)
    (step : ∀ i < 4, state (i + 1) = state i * if i < 2 then 5 - padded i else 1) :
    state 4 = (ofMultiset ({1, 2} : Multiset F)).eval 5 := by
  rw [selected_recurrence_eq_eval (· < 2) padded 5 state 4 start step]
  congr 2

-- Tuple compression is a separate premise: `a + b` identifies different pairs,
-- whereas `a + 2 * b` is injective on the occurring pairs and reflects equality.
example : ({(1, 2), (0, 0)} : Multiset (F × F)) ≠ {(2, 1), (0, 0)} ∧
    ({(1, 2), (0, 0)} : Multiset (F × F)).map (fun x => x.1 + x.2) =
      ({(2, 1), (0, 0)} : Multiset (F × F)).map (fun x => x.1 + x.2) := by
  decide

example (s t : Multiset (F × F))
    (occurs : ∀ x, x ∈ s ∨ x ∈ t → x ∈ ({(1, 2), (0, 0), (2, 1)} : Finset (F × F)))
    (encoded : s.map (fun x => x.1 + 2 * x.2) = t.map (fun x => x.1 + 2 * x.2)) : s = t := by
  have injective : ∀ x ∈ ({(1, 2), (0, 0), (2, 1)} : Finset (F × F)),
      ∀ y ∈ ({(1, 2), (0, 0), (2, 1)} : Finset (F × F)),
        x.1 + 2 * x.2 = y.1 + 2 * y.2 → x = y := by decide
  exact eq_of_map_eq_of_injOn _
    (fun x hx y hy => injective x (occurs x hx) y (occurs y hy)) encoded

-- Base-field values embedded into a larger challenge ring keep the relation.
example {B K : Type} [Field B] [CommRing K] [IsDomain K] [Algebra B K] (s t : Multiset B)
    (same : ofMultiset (s.map (algebraMap B K)) = ofMultiset (t.map (algebraMap B K))) :
    s = t :=
  eq_of_map_eq_of_injOn _ (algebraMap B K).injective.injOn (ofMultiset_eq_iff.mp same)

end Tests.MultisetFingerprint
