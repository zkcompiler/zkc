module

public import Zkc.Polynomial.Multilinear.Restriction
public import Zkc.Polynomial.Coordinates

@[expose] public section

/-! Ordered prefix restriction. `Quadratic.point` is the existing generic
coordinate concatenation; using it does not convert a table to coefficients.
The type `Table F (n + k)` becomes `Table F n` after exactly `k` coordinates.
-/

set_option autoImplicit false

namespace Zkc.Polynomial.Multilinear

variable {F : Type} {n : Nat}

def fixPrefix [Ring F] : (k : Nat) → Table F (n + k) → (Fin k → F) → Table F n
  | 0, table, _ => table
  | k + 1, table, point => fixPrefix k (fixFirst table (point 0)) (point ∘ Fin.succ)

theorem fixPrefix_zero [Ring F] (table : Table F n) (point : Fin 0 → F) :
    fixPrefix 0 table point = table := rfl

theorem fixPrefix_succ [Ring F] (k : Nat) (table : Table F (n + (k + 1)))
    (r : F) (point : Fin k → F) :
    fixPrefix (k + 1) table (Fin.cons r point) = fixPrefix k (fixFirst table r) point := rfl

variable [CommRing F]

theorem extension_fixPrefix (k : Nat) (table : Table F (n + k))
    (fixed : Fin k → F) (suffix : Fin n → F) :
    extension n (fixPrefix k table fixed) suffix =
      extension (n + k) table (Quadratic.point k fixed suffix) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [fixPrefix, ih, extension_fixFirst]
      rfl

/-- Restricting a complete point leaves its extension value in the sole row. -/
theorem fixPrefix_complete (k : Nat) (table : Table F (0 + k)) (point : Fin k → F) :
    fixPrefix (n := 0) k table point Fin.elim0 =
      extension (0 + k) table (Quadratic.point k point Fin.elim0) :=
  extension_fixPrefix (n := 0) k table point Fin.elim0

/-- Prefix truth is a sum over the *remaining* Boolean coordinates. -/
theorem booleanSum_fixPrefix (k : Nat) (table : Table F (n + k)) (fixed : Fin k → F) :
    booleanSum (fixPrefix k table fixed) =
      cubeSum n (fun suffix => extension (n + k) table (Quadratic.point k fixed suffix)) := by
  rw [← cubeSum_extension]
  congr 1
  funext suffix
  exact extension_fixPrefix k table fixed suffix

/-- Coordinate lists agree with the existing concatenation convention. -/
theorem extension_fixPrefix_coordinates (k : Nat) (table : Table F (n + k))
    (fixed suffix : List F) (fixedSize : fixed.length = k) (suffixSize : suffix.length = n) :
    extension n (fixPrefix k table (coordinates k fixed)) (coordinates n suffix) =
      extension (n + k) table (coordinates (n + k) (fixed ++ suffix)) := by
  rw [extension_fixPrefix, point_coordinates k fixed suffix fixedSize suffixSize]

end Zkc.Polynomial.Multilinear
