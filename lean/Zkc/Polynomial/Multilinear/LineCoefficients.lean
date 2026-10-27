module

public import Zkc.Polynomial.Multilinear.CoefficientRows
public import Zkc.Polynomial.Multilinear.Embedding

@[expose] public section

/-! Polynomial-valued prefix contraction for line coefficient producers.
The final polynomial is the existing independent `linePolynomial`. -/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear.LineCoefficients
open _root_.Polynomial CoefficientRows
variable {F : Type} [CommRing F]

/-- A line coordinate as a polynomial, using the source readback convention. -/
noncomputable def coordinate (start finish : List F) (i : Nat) : F[X] :=
  C (start[i]?.getD 0) + C (finish[i]?.getD 0 - start[i]?.getD 0) * X

noncomputable def coordinatePrefix (start finish : List F) (i : Nat) : List F[X] :=
  (List.range i).map (coordinate start finish)

noncomputable def stage (values start finish : List F) (i : Nat) : List F[X] :=
  restrictPrefixValues (values.map C) (coordinatePrefix start finish i)

@[simp] theorem coordinatePrefix_length (start finish : List F) (i : Nat) :
    (coordinatePrefix start finish i).length = i := by simp [coordinatePrefix]

@[simp] theorem stage_zero (values start finish : List F) :
    stage values start finish 0 = values.map C := rfl

theorem stage_succ (values start finish : List F) (i : Nat) :
    stage values start finish (i + 1) =
      restrictValues (stage values start finish i) (coordinate start finish i) := by
  simp [stage, coordinatePrefix, List.range_succ,
    restrictPrefixValues, List.foldl]

theorem stage_length (values start finish : List F) (width i : Nat)
    (shape : values.length = 2 ^ width) (inside : i ≤ width) :
    (stage values start finish i).length = 2 ^ (width - i) := by
  apply restrictPrefixValues_length
  simp only [List.length_map, coordinatePrefix_length]
  rw [Nat.sub_add_cancel inside]
  exact shape

/-- The literal coefficient-table update, including row resets. -/
def step (count : Nat) (xs : List F) (low high : F) : List F :=
  let left := xs.take (xs.length / 2)
  let right := xs.drop (xs.length / 2)
  let base := List.zipWith (fun a b => a + (b - a) * low) left right
  let rise := List.zipWith (fun a b => (b - a) * (high - low)) left right
  List.zipWith (· + ·) base (shiftAux count 0 0 rise)

theorem step_pack (count : Nat) (ps : List F[X]) (low high : F) (m : Nat)
    (positive : 0 < count) (shape : ps.length = 2 * m) :
    step count (pack count ps) low high =
      pack count (restrictValues ps (C low + C (high - low) * X)) := by
  have middle : (pack count ps).length / 2 = m * count := by
    rw [pack_length, shape, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  have pmiddle : ps.length / 2 = m := by omega
  have same : (ps.drop m).length = (ps.take m).length := by
    simp only [List.length_drop, List.length_take]; omega
  dsimp only [step]
  rw [middle, pack_take, pack_drop,
    pack_zipWith count _ _ same _ _ (fun p q => row_interpolate count p q low),
    pack_zipWith count _ _ same _ _ (fun p q => row_slope count p q (high - low)),
    shiftAux_pack count 0 0 _ positive (by simp),
    pack_zipWith count _ _ (by simp) _ _ (row_add count)]
  congr 1
  unfold restrictValues
  rw [pmiddle]
  apply List.ext_getElem
  · simp
  · intro i left right
    simp only [List.getElem_zipWith, List.getElem_map]
    ring

theorem restrictValues_degree (ps : List F[X]) (r : F[X]) (d : Nat)
    (degrees : ∀ p ∈ ps, p.natDegree ≤ d) (coordinateDegree : r.natDegree ≤ 1) :
    ∀ p ∈ restrictValues ps r, p.natDegree ≤ d + 1 := by
  intro p member
  obtain ⟨i, hi, eq⟩ := List.mem_iff_getElem.mp member
  subst p
  unfold restrictValues at hi ⊢
  rw [List.getElem_zipWith]
  let left := ps.take (ps.length / 2)
  let right := ps.drop (ps.length / 2)
  have hmin : i < min left.length right.length := by simpa only [List.length_zipWith] using hi
  have il : i < left.length := lt_of_lt_of_le hmin (Nat.min_le_left _ _)
  have ir : i < right.length := lt_of_lt_of_le hmin (Nat.min_le_right _ _)
  have da := degrees left[i] (List.mem_of_mem_take (List.getElem_mem il))
  have db := degrees right[i] (List.mem_of_mem_drop (List.getElem_mem ir))
  have sub : (right[i] - left[i]).natDegree ≤ d :=
    (natDegree_sub_le _ _).trans (max_le db da)
  change (left[i] + (right[i] - left[i]) * r).natDegree ≤ d + 1
  exact (natDegree_add_le _ _).trans (max_le (by omega)
    (natDegree_mul_le.trans (by omega)))

theorem coordinate_degree (start finish : List F) (i : Nat) :
    (coordinate start finish i).natDegree ≤ 1 := by
  unfold coordinate
  exact (natDegree_add_le _ _).trans (max_le (by simp)
    (natDegree_mul_le.trans (by simp [natDegree_X_le])))

/-- After `i` contractions every row has degree at most `i`. -/
theorem stage_degree (values start finish : List F) (i : Nat) :
    ∀ p ∈ stage values start finish i, p.natDegree ≤ i := by
  induction i with
  | zero =>
    intro p member
    obtain ⟨v, _, eq⟩ := List.mem_map.mp member
    subst p
    simp
  | succ i ih =>
    rw [stage_succ]
    exact restrictValues_degree _ _ i ih (coordinate_degree start finish i)

/-- In particular the top coefficient is zero before every reached shift. -/
theorem stage_top_zero (values start finish : List F) (width i : Nat)
    (inside : i < width) (p : F[X]) (member : p ∈ stage values start finish i) :
    p.coeff width = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (stage_degree _ _ _ _ p member) inside)

/-- The slope row sent to the shift also has a zero highest coefficient.
Thus resetting at the next row cannot discard a nonzero term. -/
theorem slope_top_zero (values start finish : List F) (width i : Nat)
    (inside : i < width) (p q : F[X])
    (left : p ∈ stage values start finish i) (right : q ∈ stage values start finish i)
    (delta : F) : ((q - p) * C delta).coeff width = 0 := by
  rw [coeff_mul_C, coeff_sub, stage_top_zero _ _ _ _ _ inside q right,
    stage_top_zero _ _ _ _ _ inside p left]
  simp

theorem extension_constants (n : Nat) (table : Table F n) (start finish : Fin n → F) :
    extension n (Embedding.table C table)
      (fun i => C (start i) + C (finish i - start i) * X) =
        linePolynomial n table start finish := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (1 - (C (start 0) + C (finish 0 - start 0) * X)) *
      extension n (Embedding.table C (half table false))
        (fun i => C (start (Fin.succ i)) + C (finish (Fin.succ i) - start (Fin.succ i)) * X) +
      (C (start 0) + C (finish 0 - start 0) * X) *
      extension n (Embedding.table C (half table true))
        (fun i => C (start (Fin.succ i)) + C (finish (Fin.succ i) - start (Fin.succ i)) * X) = _
    rw [ih, ih]
    rfl

/-- Complete contraction has one row, the independent core line polynomial. -/
theorem stage_complete (width : Nat) (values start finish : List F) (table : Table F width)
    (decoded : ofList? width values = some table) :
    stage values start finish width =
      [linePolynomial width table (coordinates width start) (coordinates width finish)] := by
  have initial := Embedding.ofList? (C : F →+* F[X]) values table decoded
  have pointCoordinates : coordinates width (coordinatePrefix start finish width) =
      (fun i => C (coordinates width start i) +
        C (coordinates width finish i - coordinates width start i) * X) := by
    funext i
    simp [coordinates, coordinatePrefix, coordinate, i.isLt]
  have full (points : List F[X]) (size : points.length = width) :
      restrictPrefixValues (values.map C) points =
        [extension width (Embedding.table C table) (coordinates width points)] := by
    subst width
    have law := restrictPrefixValues_complete (values.map C) points
    have empty : (Fin.elim0 : Fin 0 → F[X]) = coordinates 0 [] := by
      funext i; exact Fin.elim0 i
    rw [empty, point_coordinates (n := 0) points.length points [] rfl rfl, List.append_nil] at law
    generalize hdimension : 0 + points.length = dimension at law
    have sameDimension : dimension = points.length := by omega
    rw [sameDimension] at law
    exact law (Embedding.table C table) initial

  rw [stage, full _ (coordinatePrefix_length _ _ _), pointCoordinates, extension_constants]

end Zkc.Polynomial.Multilinear.LineCoefficients
