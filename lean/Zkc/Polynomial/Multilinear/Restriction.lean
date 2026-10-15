module

public import Zkc.Polynomial.Multilinear

@[expose] public section

/-! Leading-coordinate restriction of the existing MSB-first Boolean tables.
The arity in `Table` enforces the scalar shape; no native capacity is assumed.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear

variable {F : Type} {n : Nat}

/-- Low (`false`) or high (`true`) half, in the existing table order. -/
def half (table : Table F (n + 1)) (side : Bool) : Table F n :=
  fun bits => table (Fin.cons side bits)

/-- Ordered summation: first the low half, then the high half. -/
def booleanSum [Add F] : {n : Nat} → Table F n → F
  | 0, table => table Fin.elim0
  | _ + 1, table => booleanSum (half table false) + booleanSum (half table true)

theorem booleanSum_eq_sum [AddCommMonoid F] (table : Table F n) :
    booleanSum table = ∑ bits, table bits := by
  induction n with
  | zero =>
      rw [Fintype.sum_unique]
      exact congrArg table (Subsingleton.elim _ _)
  | succ n ih =>
      rw [← (Fin.consEquiv (fun _ : Fin (n + 1) => Bool)).sum_comp table]
      rw [Fintype.sum_prod_type, Fintype.sum_bool]
      change booleanSum (half table false) + booleanSum (half table true) =
        (∑ bits, half table true bits) + ∑ bits, half table false bits
      rw [ih, ih, add_comm]

/-- The existing binary index is the bridge to the flat vector sum. -/
theorem booleanSum_ofVector [AddCommMonoid F] (values : Fin (2 ^ n) → F) :
    booleanSum (ofVector values) = ∑ i, values i := by
  rw [booleanSum_eq_sum]
  exact (Equiv.mk (index n) (vertex n) (vertex_index n) (index_vertex n)).sum_comp values

/-- Check a flat scalar table without padding or truncating. This checks the
mathematical shape only; the native dimension/capacity bounds are separate. -/
def ofList? (n : Nat) (values : List F) : Option (Table F n) :=
  if size : values.length = 2 ^ n then
    some (ofVector (fun i => values[i.val]'(by omega)))
  else none

theorem ofList?_isSome_iff (values : List F) :
    (ofList? n values).isSome = true ↔ values.length = 2 ^ n := by
  simp only [ofList?]
  split <;> simp_all

theorem ofList?_ofFn (values : Fin (2 ^ n) → F) :
    ofList? n (List.ofFn values) = some (ofVector values) := by
  simp [ofList?]

theorem ofList?_entry (values : List F) (table : Table F n)
    (decoded : ofList? n values = some table) (position : Fin (2 ^ n)) :
    values[position.val]? = some (table (vertex n position)) := by
  unfold ofList? at decoded
  split at decoded
  · cases Option.some.inj decoded
    simp [ofVector_vertex]
  · contradiction

theorem booleanSum_ofList? [AddCommMonoid F] (values : List F) (table : Table F n)
    (decoded : ofList? n values = some table) : booleanSum table = values.sum := by
  unfold ofList? at decoded
  split at decoded
  · rename_i size
    cases Option.some.inj decoded
    rw [booleanSum_ofVector, ← List.sum_ofFn]
    congr 1
    apply List.ext_getElem
    · simpa using size.symm
    · intro i left right
      simp
  · contradiction

theorem booleanSum_add [AddCommSemigroup F] (left right : Table F n) :
    booleanSum (fun bits => left bits + right bits) =
      booleanSum left + booleanSum right := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [booleanSum]
      unfold half
      rw [ih, ih]
      ac_rfl

theorem booleanSum_scale [NonUnitalNonAssocSemiring F] (c : F) (table : Table F n) :
    booleanSum (fun bits => c * table bits) = c * booleanSum table := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [booleanSum]
      unfold half
      rw [ih, ih, mul_add]

/-- Substitute the leading coordinate; the remaining table has arity `n`. -/
def fixFirst [Ring F] (table : Table F (n + 1)) (r : F) : Table F n :=
  fun bits => (1 - r) * half table false bits + r * half table true bits

theorem fixFirst_zero [Ring F] (table : Table F (n + 1)) :
    fixFirst table 0 = half table false := by
  funext bits
  simp [fixFirst]

theorem fixFirst_one [Ring F] (table : Table F (n + 1)) :
    fixFirst table 1 = half table true := by
  funext bits
  simp [fixFirst]

theorem booleanSum_fixFirst [Ring F] (table : Table F (n + 1)) (r : F) :
    booleanSum (fixFirst table r) =
      (1 - r) * booleanSum (half table false) + r * booleanSum (half table true) := by
  unfold fixFirst
  rw [booleanSum_add, booleanSum_scale, booleanSum_scale]

/-- Match the actual scalar helper's `low + (high - low) * r` formula. -/
theorem fixFirst_apply [CommRing F] (table : Table F (n + 1)) (r : F)
    (bits : Fin n → Bool) :
    fixFirst table r bits = half table false bits +
      (half table true bits - half table false bits) * r := by
  simp only [fixFirst]
  ring

variable [CommRing F]

theorem extension_add (left right : Table F n) (point : Fin n → F) :
    extension n (fun bits => left bits + right bits) point =
      extension n left point + extension n right point := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [extension, ih]; ring

theorem extension_scale (c : F) (table : Table F n) (point : Fin n → F) :
    extension n (fun bits => c * table bits) point = c * extension n table point := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [extension, ih]; ring

theorem extension_fixFirst (table : Table F (n + 1)) (r : F) (point : Fin n → F) :
    extension n (fixFirst table r) point = extension (n + 1) table (Fin.cons r point) := by
  unfold fixFirst half
  rw [extension_add, extension_scale, extension_scale]
  rfl

/-- The ordered table sum is the Boolean sum of its multilinear extension. -/
theorem cubeSum_extension (table : Table F n) :
    cubeSum n (extension n table) = booleanSum table := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [cubeSum]
      have low : (fun tail => extension (n + 1) table (Fin.cons 0 tail)) =
          extension n (half table false) := by
        funext tail
        unfold half
        simp [extension, Function.comp_def]
      have high : (fun tail => extension (n + 1) table (Fin.cons 1 tail)) =
          extension n (half table true) := by
        funext tail
        unfold half
        simp [extension, Function.comp_def]
      rw [low, high, ih, ih]
      rfl

end Zkc.Polynomial.Multilinear
