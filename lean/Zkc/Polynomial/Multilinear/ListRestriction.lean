module

public import Zkc.Polynomial.Multilinear.Prefix

@[expose] public section

/-! Contiguous list restriction and the existing MSB-first table semantics.

The list operations are total. Their shape and table laws require exact input
lengths; they do not assign truncating zip semantics to a checked source map.
The algebra needs only a commutative ring, including characteristic two.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear

variable {F : Type} {n m : Nat}

theorem ofList?_length (values : List F) (table : Table F n)
    (decoded : ofList? n values = some table) : values.length = 2 ^ n := by
  apply (ofList?_isSome_iff values).mp
  rw [decoded]
  rfl

variable [CommRing F]

/-- Interpolate corresponding entries of the contiguous low and high halves. -/
def restrictValues (values : List F) (r : F) : List F :=
  List.zipWith (fun low high => low + (high - low) * r)
    (values.take (values.length / 2)) (values.drop (values.length / 2))

/-- Consume the fixed coordinates from first to last. -/
def restrictPrefixValues (values fixed : List F) : List F :=
  fixed.foldl restrictValues values

omit [CommRing F] in
/-- Exact even shape supplies equal map-input lengths, including the empty case. -/
theorem restrictValues_halves_length (values : List F) (shape : values.length = 2 * m) :
    (values.take (values.length / 2)).length = m ∧
      (values.drop (values.length / 2)).length = m := by
  simp only [List.length_take, List.length_drop, shape]
  omega

theorem restrictValues_length (values : List F) (r : F)
    (shape : values.length = 2 * m) : (restrictValues values r).length = m := by
  obtain ⟨low, high⟩ := restrictValues_halves_length values shape
  simp only [restrictValues, List.length_zipWith, low, high, Nat.min_self]

/-- Each output position uses the same position in the two contiguous halves. -/
theorem restrictValues_getElem (values : List F) (r : F)
    (shape : values.length = 2 * m) (i : Nat) (bound : i < m) :
    (restrictValues values r)[i]'(by rw [restrictValues_length values r shape]; exact bound) =
      values[i]'(by omega) +
        (values[m + i]'(by omega) - values[i]'(by omega)) * r := by
  have middle : values.length / 2 = m := by omega
  simp only [restrictValues, List.getElem_zipWith, List.getElem_take, List.getElem_drop,
    middle]

private theorem rowMajorPosition_lt (rows columns : Nat) (row : Fin rows)
    (column : Fin columns) : row.val * columns + column.val < rows * columns := by
  have rowBound := Nat.mul_le_mul_right columns row.isLt
  have columnBound := column.isLt
  simp only [Nat.succ_mul] at rowBound
  omega

/-- Row-major restriction keeps the column index fixed in both input halves.
This applies to any width; it does not multiply or merge factor columns. -/
theorem restrictValues_getElem_rowMajor (values : List F) (r : F)
    (rows columns : Nat) (shape : values.length = 2 * (rows * columns))
    (row : Fin rows) (column : Fin columns) :
    (restrictValues values r)[row.val * columns + column.val]'(by
        rw [restrictValues_length values r shape]
        exact rowMajorPosition_lt rows columns row column) =
      values[row.val * columns + column.val]'(by
        have := rowMajorPosition_lt rows columns row column
        omega) +
      (values[(rows + row.val) * columns + column.val]'(by
        have := rowMajorPosition_lt rows columns row column
        rw [Nat.add_mul]
        omega) -
      values[row.val * columns + column.val]'(by
        have := rowMajorPosition_lt rows columns row column
        omega)) * r := by
  simpa only [Nat.add_mul, Nat.add_assoc] using
    restrictValues_getElem values r shape (row.val * columns + column.val)
      (rowMajorPosition_lt rows columns row column)

/-- A scalar list of `2^(n+1)` entries restricts to the existing `fixFirst` table. -/
theorem ofList?_restrictValues (values : List F) (table : Table F (n + 1))
    (r : F) (decoded : ofList? (n + 1) values = some table) :
    ofList? n (restrictValues values r) = some (fixFirst table r) := by
  have shape : values.length = 2 * 2 ^ n := by
    rw [ofList?_length values table decoded, Nat.pow_succ, Nat.mul_comm]
  have resultShape := restrictValues_length values r shape
  unfold ofList? at decoded ⊢
  split at decoded
  · cases Option.some.inj decoded
    rw [dite_eq_left resultShape]
    apply congrArg some
    funext bits
    rw [fixFirst_apply]
    simp only [ofVector, half, index, Fin.cons_zero,
      Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
    exact restrictValues_getElem values r shape _ (index n bits).isLt
  · contradiction

theorem restrictPrefixValues_nil (values : List F) :
    restrictPrefixValues values [] = values := rfl

theorem restrictPrefixValues_cons (values fixed : List F) (r : F) :
    restrictPrefixValues values (r :: fixed) =
      restrictPrefixValues (restrictValues values r) fixed := rfl

/-- Composition retains the order of the two coordinate lists. -/
theorem restrictPrefixValues_append (values first second : List F) :
    restrictPrefixValues values (first ++ second) =
      restrictPrefixValues (restrictPrefixValues values first) second :=
  List.foldl_append

/-- Repeated list restriction agrees with ordered mathematical prefix fixing. -/
theorem ofList?_restrictPrefixValues (values fixed : List F)
    (table : Table F (n + fixed.length))
    (decoded : ofList? (n + fixed.length) values = some table) :
    ofList? n (restrictPrefixValues values fixed) =
      some (fixPrefix fixed.length table (coordinates fixed.length fixed)) := by
  induction fixed generalizing values with
  | nil => exact decoded
  | cons r fixed ih =>
      rw [restrictPrefixValues_cons]
      exact ih (restrictValues values r) (fixFirst table r)
        (ofList?_restrictValues values table r decoded)

/-- Explicit arity form for clients whose shape metadata stores the prefix length. -/
theorem ofList?_restrictPrefixValues_of_length (k : Nat) (values fixed : List F)
    (table : Table F (n + k)) (fixedSize : fixed.length = k)
    (decoded : ofList? (n + k) values = some table) :
    ofList? n (restrictPrefixValues values fixed) =
      some (fixPrefix k table (coordinates k fixed)) := by
  subst k
  exact ofList?_restrictPrefixValues values fixed table decoded

/-- Exact residual length follows from mathematical input shape alone. -/
theorem restrictPrefixValues_length (values fixed : List F)
    (shape : values.length = 2 ^ (n + fixed.length)) :
    (restrictPrefixValues values fixed).length = 2 ^ n := by
  induction fixed generalizing values with
  | nil => exact shape
  | cons r fixed ih =>
      rw [restrictPrefixValues_cons]
      apply ih
      apply restrictValues_length
      simpa only [List.length_cons, Nat.add_succ, Nat.pow_succ, Nat.mul_comm] using shape

/-- Repeated restriction also preserves an arbitrary row-major column width. -/
theorem restrictPrefixValues_length_mul (values fixed : List F) (columns : Nat)
    (shape : values.length = 2 ^ (n + fixed.length) * columns) :
    (restrictPrefixValues values fixed).length = 2 ^ n * columns := by
  induction fixed generalizing values with
  | nil => exact shape
  | cons r fixed ih =>
      rw [restrictPrefixValues_cons]
      apply ih
      apply restrictValues_length
      rw [shape, List.length_cons, Nat.add_succ, Nat.pow_succ]
      ac_rfl

/-- A decoded residual list denotes the original extension at the ordered prefix. -/
theorem extension_restrictPrefixValues (values fixed : List F)
    (table : Table F (n + fixed.length)) (result : Table F n)
    (decoded : ofList? (n + fixed.length) values = some table)
    (resultDecoded : ofList? n (restrictPrefixValues values fixed) = some result)
    (suffix : Fin n → F) :
    extension n result suffix = extension (n + fixed.length) table
      (Quadratic.point fixed.length (coordinates fixed.length fixed) suffix) := by
  have same := Option.some.inj
    (resultDecoded.symm.trans (ofList?_restrictPrefixValues values fixed table decoded))
  rw [same, extension_fixPrefix]

/-- Complete restriction leaves exactly one entry, the existing extension value. -/
theorem restrictPrefixValues_complete (values fixed : List F)
    (table : Table F (0 + fixed.length))
    (decoded : ofList? (0 + fixed.length) values = some table) :
    restrictPrefixValues values fixed =
      [extension (0 + fixed.length) table
        (Quadratic.point fixed.length (coordinates fixed.length fixed) Fin.elim0)] := by
  have result := ofList?_restrictPrefixValues values fixed table decoded
  have size : (restrictPrefixValues values fixed).length = 1 := by
    simpa only [Nat.pow_zero] using ofList?_length _ _ result
  obtain ⟨value, singleton⟩ := List.length_eq_one_iff.mp size
  have entry := ofList?_entry _ _ result (0 : Fin (2 ^ 0))
  rw [singleton] at entry
  simp only [Fin.val_zero, List.getElem?_cons_zero, vertex] at entry
  rw [singleton, Option.some.inj entry, fixPrefix_complete]

omit [CommRing F] in
set_option backward.isDefEq.respectTransparency false in
/-- The low contiguous half is the MSB=false mathematical half, without padding. -/
theorem decode_low_half (xs : List F) (table : Table F (n+1))
    (decoded : ofList? (n+1) xs = some table) :
    ofList? n (xs.take (xs.length / 2)) = some (half table false) := by
  have size := ofList?_length xs table decoded
  have middle : xs.length / 2 = 2 ^ n := by rw [size, Nat.pow_succ]; omega
  have lowSize : (xs.take (xs.length / 2)).length = 2 ^ n := by
    rw [List.length_take, middle, Nat.min_eq_left]
    rw [size, Nat.pow_succ]; omega
  unfold ofList? at decoded ⊢
  rw [dite_eq_left lowSize]
  split at decoded
  · cases Option.some.inj decoded
    congr 1
    funext bits
    simp only [ofVector, half, index, Fin.cons_zero, Bool.false_eq_true, ite_false,
      Nat.zero_add, List.getElem_take]
    rfl
  · contradiction

omit [CommRing F] in
set_option backward.isDefEq.respectTransparency false in
/-- The high contiguous half is the MSB=true mathematical half. -/
theorem decode_high_half (xs : List F) (table : Table F (n+1))
    (decoded : ofList? (n+1) xs = some table) :
    ofList? n (xs.drop (xs.length / 2)) = some (half table true) := by
  have size := ofList?_length xs table decoded
  have middle : xs.length / 2 = 2 ^ n := by rw [size, Nat.pow_succ]; omega
  have highSize : (xs.drop (xs.length / 2)).length = 2 ^ n := by
    rw [List.length_drop, middle, size, Nat.pow_succ]; omega
  unfold ofList? at decoded ⊢
  rw [dite_eq_left highSize]
  split at decoded
  · cases Option.some.inj decoded
    congr 1
    funext bits
    simp only [ofVector, half, index, Fin.cons_zero, ite_true, List.getElem_drop, middle]
    rfl
  · contradiction

set_option backward.isDefEq.respectTransparency false in
/-- This is the existing MSB MLE at the actual complete point, not a constant formula. -/
theorem complete_prefix_sum (xs point : List F) (table : Table F (0 + point.length))
    (decoded : ofList? (0 + point.length) xs = some table) :
    (restrictPrefixValues xs point).sum =
      extension (0 + point.length) table (coordinates (0 + point.length) point) := by
  rw [restrictPrefixValues_complete xs point table decoded, List.sum_singleton]
  have empty : (Fin.elim0 : Fin 0 → F) = coordinates 0 [] := by
    funext i; exact Fin.elim0 i
  rw [empty, point_coordinates (n := 0) point.length point [] rfl rfl, List.append_nil]


end Zkc.Polynomial.Multilinear
