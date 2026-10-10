import Zkc.Polynomial.Multilinear
import Zkc.Polynomial.Coordinates

/-! Immutable original tables and ordered residual views. The generic laws are
carried forward from the adopted table/storage design; no native storage is assumed. -/

set_option autoImplicit false

namespace Zkc.Polynomial


structure Table (F : Type) (n : Nat) where
  origin : Nat
  cells : List F
  shape : cells.length = 2 ^ n

namespace Table

def admit {F : Type} (n origin : Nat) (cells : List F) : Option (Table F n) :=
  if h : cells.length = 2 ^ n then some ⟨origin, cells, h⟩ else none

def vector {F : Type} {n : Nat} (t : Table F n) (i : Fin (2 ^ n)) : F :=
  t.cells[i.val]'(by rw [t.shape]; exact i.isLt)

def logical {F : Type} {n : Nat} (t : Table F n) :=
  Zkc.Polynomial.Multilinear.ofVector (vector t)

theorem original_cell {F : Type} {n : Nat} (t : Table F n) (i : Fin (2 ^ n)) :
    logical t (Zkc.Polynomial.Multilinear.vertex n i) = vector t i :=
  Zkc.Polynomial.Multilinear.ofVector_vertex (vector t) i

structure Residual (F : Type) (n : Nat) where
  root : Table F n
  coordinates : List F
  bound : coordinates.length ≤ n

def view {F : Type} {n : Nat} (t : Table F n) : Residual F n := ⟨t, [], by simp⟩

def extend {F : Type} {n : Nat} (v : Residual F n) (r : F)
    (room : v.coordinates.length < n) : Residual F n :=
  ⟨v.root, v.coordinates ++ [r], by simp; omega⟩

def restrict {F : Type} {n : Nat} (v : Residual F n) (r : F) : Option (Residual F n) :=
  if room : v.coordinates.length < n then some (extend v r room) else none

def atPoint {F : Type} [CommRing F] {n : Nat} (t : Table F n)
    (point : List F) (shape : point.length = n) : F :=
  Zkc.Polynomial.Multilinear.extension n (logical t)
    (fun i => point[i.val]'(by rw [shape]; exact i.isLt))

def evaluate {F : Type} [CommRing F] {n : Nat} (v : Residual F n)
    (tail : List F) : Option F :=
  if shape : (v.coordinates ++ tail).length = n then some (atPoint v.root _ shape) else none

theorem extend_root {F : Type} {n : Nat} (v : Residual F n) (r : F)
    (room : v.coordinates.length < n) : (extend v r room).root = v.root := rfl

theorem evaluate_original {F : Type} [CommRing F] {n : Nat} (v : Residual F n)
    (tail : List F) (shape : (v.coordinates ++ tail).length = n) :
    evaluate v tail = some (atPoint v.root (v.coordinates ++ tail) shape) := by
  simp [evaluate, shape]

/-- Restricting one coordinate and then evaluating retains the original order,
including invalid final arity. This is uniform in the field and original rank. -/
theorem restrict_evaluate {F : Type} [CommRing F] {n : Nat} (v : Residual F n)
    (r : F) (room : v.coordinates.length < n) (tail : List F) :
    evaluate (extend v r room) tail = evaluate v (r :: tail) := by
  simp [evaluate, extend, List.append_assoc]

theorem restriction_exhausted {F : Type} {n : Nat} (v : Residual F n) (r : F)
    (full : v.coordinates.length = n) : restrict v r = none := by
  simp [restrict, full]

theorem atPoint_coordinates {F : Type} [CommRing F] {n : Nat} (t : Table F n)
    (point : List F) (shape : point.length = n) :
    atPoint t point shape = Zkc.Polynomial.Multilinear.extension n (logical t)
      (Zkc.Polynomial.coordinates n point) := by
  unfold atPoint
  congr 1
  funext i
  have within : i.val < point.length := by rw [shape]; exact i.isLt
  simp [Zkc.Polynomial.coordinates, within]

/-- Exact bridge to the specification's maintained indexed prefix join. -/
theorem evaluate_indexed_join {F : Type} [CommRing F] {n m : Nat}
    (t : Table F (n + m)) (fixed tail : List F)
    (fixedSize : fixed.length = m) (tailSize : tail.length = n) :
    evaluate ⟨t, fixed, by omega⟩ tail =
      some (Zkc.Polynomial.Multilinear.extension (n + m) (logical t)
        (Zkc.Polynomial.Quadratic.point m (Zkc.Polynomial.coordinates m fixed)
          (Zkc.Polynomial.coordinates n tail))) := by
  rw [evaluate_original _ _ (by simp [fixedSize, tailSize, Nat.add_comm]),
    atPoint_coordinates, Zkc.Polynomial.point_coordinates m fixed tail fixedSize tailSize]


end Table
end Zkc.Polynomial
