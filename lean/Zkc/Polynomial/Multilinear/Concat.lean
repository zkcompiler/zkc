module

public import Zkc.Polynomial.Multilinear.Prefix

@[expose] public section

/-! Tables over concatenated coordinates.

`Quadratic.point m fixed tail` places the `m` coordinates of `fixed` first and
concatenates Boolean coordinates as well as field points; `front` and `back`
split a Boolean point the same way. Restricting a table's leading coordinates
at a field point is, entry by entry, the extension in those coordinates. The
extension of a table that is the product of a function of the leading
coordinates and a function of the trailing ones is the product of their
extensions, and the extension of a Boolean sum is the Boolean sum of the
extensions.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear
open Zkc.Polynomial

variable {F : Type} {n : Nat}

/-- The leading `m` coordinates of a concatenated Boolean point. -/
def front : (m : Nat) → (Fin (n + m) → Bool) → Fin m → Bool
  | 0, _ => Fin.elim0
  | m + 1, bits => Fin.cons (bits 0) (front m (bits ∘ Fin.succ))

/-- The trailing `n` coordinates of a concatenated Boolean point. -/
def back : (m : Nat) → (Fin (n + m) → Bool) → Fin n → Bool
  | 0, bits => bits
  | m + 1, bits => back m (bits ∘ Fin.succ)

theorem front_point (m : Nat) (fixed : Fin m → Bool) (tail : Fin n → Bool) :
    front m (Quadratic.point m fixed tail) = fixed := by
  induction m with
  | zero => funext i; exact Fin.elim0 i
  | succ m ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change front m (Quadratic.point m (fixed ∘ Fin.succ) tail) j = fixed j.succ
        rw [ih]
        rfl

theorem back_point (m : Nat) (fixed : Fin m → Bool) (tail : Fin n → Bool) :
    back m (Quadratic.point m fixed tail) = tail := by
  induction m with
  | zero => rfl
  | succ m ih => exact ih (fixed ∘ Fin.succ)

theorem point_front_back (m : Nat) (bits : Fin (n + m) → Bool) :
    Quadratic.point m (front m bits) (back m bits) = bits := by
  induction m with
  | zero => rfl
  | succ m ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change Quadratic.point m (front m (bits ∘ Fin.succ)) (back m (bits ∘ Fin.succ)) j =
          bits j.succ
        rw [ih]
        rfl

variable [CommRing F]

theorem booleanPoint_cons (side : Bool) (bits : Fin n → Bool) :
    booleanPoint (F := F) (Fin.cons side bits : Fin (n + 1) → Bool) =
      Fin.cons (if side then 1 else 0) (booleanPoint bits) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- Restricting the leading coordinates at a field point is, entry by entry,
the extension in those coordinates. -/
theorem fixPrefix_apply (k : Nat) (table : Table F (n + k)) (fixed : Fin k → F)
    (bits : Fin n → Bool) :
    fixPrefix k table fixed bits =
      extension k (fun leading => table (Quadratic.point k leading bits)) fixed := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fixPrefix, ih]
      simp only [fixFirst, half, extension]
      rw [← extension_scale, ← extension_scale, ← extension_add]
      rfl

/-- The extension of a product of a function of the leading coordinates and a
function of the trailing coordinates. -/
theorem extension_separable (m : Nat) (f : Table F m) (g : Table F n) (fixed : Fin m → F)
    (tail : Fin n → F) :
    extension (n + m) (fun bits => f (front m bits) * g (back m bits))
        (Quadratic.point m fixed tail) =
      extension m f fixed * extension n g tail := by
  induction m with
  | zero =>
      change extension n (fun bits => f Fin.elim0 * g bits) tail = f Fin.elim0 * extension n g tail
      exact extension_scale _ _ _
  | succ m ih =>
      change (1 - fixed 0) * extension (n + m)
            (fun bits => f (Fin.cons false (front m bits)) * g (back m bits))
            (Quadratic.point m (fixed ∘ Fin.succ) tail) +
          fixed 0 * extension (n + m)
            (fun bits => f (Fin.cons true (front m bits)) * g (back m bits))
            (Quadratic.point m (fixed ∘ Fin.succ) tail) = _
      rw [ih (fun bits => f (Fin.cons false bits)), ih (fun bits => f (Fin.cons true bits))]
      simp only [extension]
      ring

/-- A function of the leading coordinates alone. -/
theorem extension_front (m : Nat) (f : Table F m) (fixed : Fin m → F) (tail : Fin n → F) :
    extension (n + m) (fun bits => f (front m bits)) (Quadratic.point m fixed tail) =
      extension m f fixed := by
  have product := extension_separable m f (fun _ => (1 : F)) fixed tail
  simp only [mul_one, extension_one] at product
  exact product

/-- A function of the trailing coordinates alone. -/
theorem extension_back (m : Nat) (g : Table F n) (fixed : Fin m → F) (tail : Fin n → F) :
    extension (n + m) (fun bits => g (back m bits)) (Quadratic.point m fixed tail) =
      extension n g tail := by
  have product := extension_separable m (fun _ => (1 : F)) g fixed tail
  simp only [one_mul, extension_one] at product
  exact product


/-- The extension is affine in each coordinate. -/
theorem extension_update (table : Table F n) (point : Fin n → F) (position : Fin n) (r : F) :
    extension n table (Function.update point position r) =
      (1 - r) * extension n table (Function.update point position 0) +
        r * extension n table (Function.update point position 1) := by
  induction n with
  | zero => exact position.elim0
  | succ n ih =>
      refine Fin.cases ?_ (fun later => ?_) position
      · have tail (value : F) : Function.update point 0 value ∘ Fin.succ = point ∘ Fin.succ := by
          funext i
          exact Function.update_of_ne (Fin.succ_ne_zero i) _ _
        simp only [extension, Function.update_self, tail]
        ring
      · have tail (value : F) : Function.update point later.succ value ∘ Fin.succ =
            Function.update (point ∘ Fin.succ) later value :=
          Function.update_comp_eq_of_injective _ (Fin.succ_injective _) _ _
        have head (value : F) : Function.update point later.succ value 0 = point 0 :=
          Function.update_of_ne (Fin.succ_ne_zero later).symm _ _
        simp only [extension, tail, head]
        rw [ih (fun tail => table (Fin.cons false tail)), ih (fun tail => table (Fin.cons true tail))]
        ring

/-- Inserting a value at the next position of a point list. -/
theorem coordinates_insert (point tail : List F) (r : F) (short : point.length < n) :
    coordinates n (point ++ r :: tail) =
      Function.update (coordinates n (point ++ 0 :: tail)) ⟨point.length, short⟩ r := by
  funext i
  by_cases same : i.val = point.length
  · have position : i = ⟨point.length, short⟩ := Fin.ext same
    subst position
    simp [coordinates]
  · have different : i ≠ ⟨point.length, short⟩ := fun equal => same (congrArg Fin.val equal)
    rw [Function.update_of_ne different]
    simp only [coordinates]
    rcases Nat.lt_or_gt_of_ne same with before | after
    · rw [List.getElem?_append_left before, List.getElem?_append_left before]
    · rw [List.getElem?_append_right (Nat.le_of_lt after), List.getElem?_append_right (Nat.le_of_lt after)]
      obtain ⟨offset, shifted⟩ : ∃ offset, i.val - point.length = offset + 1 :=
        ⟨i.val - point.length - 1, by omega⟩
      rw [shifted, List.getElem?_cons_succ, List.getElem?_cons_succ]

/-- The extension at a point list is affine in the value at the next position. -/
theorem extension_insert (table : Table F n) (point tail : List F) (r : F) (short : point.length < n) :
    extension n table (coordinates n (point ++ r :: tail)) =
      (1 - r) * extension n table (coordinates n (point ++ 0 :: tail)) +
        r * extension n table (coordinates n (point ++ 1 :: tail)) := by
  rw [coordinates_insert point tail r short, coordinates_insert point tail 1 short,
    extension_update]
  congr 3
  · funext i
    by_cases same : i = ⟨point.length, short⟩
    · subst same
      simp [coordinates]
    · rw [Function.update_of_ne same]

/-- Coordinates of three concatenated complete points. -/
theorem coordinates_three (first second third : List F) (firstSize : first.length = n)
    (secondSize : second.length = n) (thirdSize : third.length = n) :
    coordinates (n + n + n) (first ++ second ++ third) =
      Quadratic.point n (coordinates n first)
        (Quadratic.point n (coordinates n second) (coordinates n third)) := by
  rw [point_coordinates n second third secondSize thirdSize,
    point_coordinates n first (second ++ third) firstSize (by simp [secondSize, thirdSize]),
    List.append_assoc]

/-- The extension of a family of Boolean sums is the Boolean sum of the
extensions. -/
theorem extension_booleanSum (k : Nat) (family : (Fin k → Bool) → Table F n)
    (point : Fin k → F) :
    extension k (fun leading => booleanSum (family leading)) point =
      booleanSum (fun bits => extension k (fun leading => family leading bits) point) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change extension k (fun leading => booleanSum (half (family leading) false) +
          booleanSum (half (family leading) true)) point = _
      rw [extension_add, ih, ih]
      rfl

/-- The Boolean cube sum of a function is the Boolean sum of its values at
the Boolean points. -/
theorem cubeSum_booleanPoint (g : (Fin n → F) → F) :
    cubeSum n g = booleanSum (fun bits => g (booleanPoint bits)) := by
  induction n with
  | zero =>
      change g Fin.elim0 = g (booleanPoint Fin.elim0)
      congr 1
      funext i
      exact Fin.elim0 i
  | succ n ih =>
      change cubeSum n (fun tail => g (Fin.cons 0 tail)) +
          cubeSum n (fun tail => g (Fin.cons 1 tail)) =
        booleanSum (fun bits => g (booleanPoint (Fin.cons false bits))) +
          booleanSum (fun bits => g (booleanPoint (Fin.cons true bits)))
      rw [ih, ih]
      simp only [booleanPoint_cons, Bool.false_eq_true, ↓reduceIte]

end Zkc.Polynomial.Multilinear
