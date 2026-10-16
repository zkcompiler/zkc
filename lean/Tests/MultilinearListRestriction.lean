import Zkc.Polynomial.Multilinear.ListRestriction
import Mathlib.Algebra.Field.ZMod

/-! Kernel controls for the pure list-to-table restriction bridge.
These distinguish table order, coordinate order, factor columns, and exact shape.
-/

set_option autoImplicit false

namespace MultilinearListRestrictionTests

open Zkc.Polynomial Zkc.Polynomial.Multilinear

def values : List ℤ := [2, 5, 11, 19]
def table : Table ℤ 2 := ofVector ![2, 5, 11, 19]

-- Asymmetric entries expose swapping or interleaving the contiguous halves.
example : restrictValues values 2 = [20, 33] := by decide +kernel
example : restrictValues values 0 = [2, 5] := by decide +kernel
example : restrictValues values 1 = [11, 19] := by decide +kernel
example : restrictValues values 2 ≠ restrictValues [11, 19, 2, 5] 2 := by decide +kernel
example : restrictValues values 2 ≠ restrictValues [2, 11, 5, 19] 2 := by decide +kernel

-- Empty, partial, and full prefixes; reversing coordinates changes the answer.
example : restrictPrefixValues values [] = values := by decide +kernel
example : restrictPrefixValues values [2] = [20, 33] := by decide +kernel
example : restrictPrefixValues values [2, 3] = [59] := by decide +kernel
example : restrictPrefixValues values [3, 2] = [65] := by decide +kernel
example : restrictPrefixValues values [2, 3] ≠ restrictPrefixValues values [3, 2] := by
  decide +kernel
example : restrictPrefixValues ([7] : List ℤ) [] = [7] := by decide +kernel
example : restrictPrefixValues ([2, 5, 11, 19, 23, 31, 47, 61] : List ℤ) [2, 3] =
    [161, 195] := by decide +kernel
example : restrictPrefixValues ([2, 5, 11, 19, 23, 31, 47, 61] : List ℤ) [2, 3, 5] =
    [331] := by decide +kernel

-- Reuse the bridge as a theorem client, including the finite-coordinate conversion.
example : ofList? 1 (restrictValues values 2) = some (fixFirst table 2) := by
  apply ofList?_restrictValues
  change ofList? 2 (List.ofFn (![2, 5, 11, 19] : Fin 4 → ℤ)) = some table
  exact ofList?_ofFn _

example : ofList? 0 (restrictPrefixValues values [2, 3]) =
    some (fixPrefix (n := 0) 2 table (coordinates 2 [2, 3])) := by
  apply ofList?_restrictPrefixValues_of_length 2 values [2, 3] table rfl
  change ofList? 2 (List.ofFn (![2, 5, 11, 19] : Fin 4 → ℤ)) = some table
  exact ofList?_ofFn _

example : extension 2 table (coordinates 2 [2, 3]) = 59 := by decide +kernel
example : extension 1 (fixPrefix (n := 1) 1 table (coordinates 1 [2]))
    (coordinates 1 [3]) = extension 2 table (coordinates 2 [2, 3]) :=
  extension_fixPrefix_coordinates 1 table [2] [3] rfl rfl

-- Two independent factor columns remain row-major after one or two restrictions.
example : restrictValues ([2, 3, 5, 7, 11, 13, 17, 19] : List ℤ) 2 =
    [20, 23, 29, 31] := by decide +kernel
example : restrictPrefixValues ([2, 3, 5, 7, 11, 13, 17, 19] : List ℤ) [2, 3] =
    [47, 47] := by decide +kernel
example : (restrictPrefixValues ([2, 3, 5, 7, 11, 13, 17, 19] : List ℤ) [2, 3]).length =
    2 ^ 0 * 2 := restrictPrefixValues_length_mul _ _ 2 rfl
example : restrictValues ([2, 5, 11, 17] : List ℤ) 2 = [20, 29] := by decide +kernel
example : restrictValues ([3, 7, 13, 19] : List ℤ) 2 = [23, 31] := by decide +kernel
example : (restrictValues ([2, 3, 5, 7, 11, 13, 17, 19] : List ℤ) 2)[3] =
    7 + (19 - 7) * 2 :=
  restrictValues_getElem_rowMajor _ _ 2 2 rfl 1 1

-- Six entries have valid even shape without being a scalar power-of-two table.
example : (restrictValues ([2, 3, 5, 7, 11, 13] : List ℤ) 2).length = 3 :=
  restrictValues_length _ _ rfl
example : (ofList? 2 ([2, 3, 5, 7, 11, 13] : List ℤ)).isNone = true := by decide +kernel

-- Total list behavior on malformed shapes does not satisfy scalar decoding premises.
example : (ofList? 2 ([2, 5, 11] : List ℤ)).isNone = true := by decide +kernel
example : (ofList? 2 ([2, 5, 11, 19, 23] : List ℤ)).isNone = true := by decide +kernel
example : (([2, 5, 11] : List ℤ).take 1).length ≠
    (([2, 5, 11] : List ℤ).drop 1).length := by decide +kernel
example : restrictValues ([2, 5, 11] : List ℤ) 2 = [8] := by decide +kernel
-- A valid-looking output alone cannot establish the required input shape.
example : (ofList? 1 (restrictValues ([2, 5, 11, 19, 23] : List ℤ) 2)).isSome = true := by
  decide +kernel
example : (ofList? 0 (restrictPrefixValues values [2, 3, 4])).isNone = true := by
  decide +kernel
example : (ofList? 0 ([] : List ℤ)).isNone = true := by decide +kernel

-- Neither characteristic two nor a non-field commutative ring is excluded.
example : restrictValues ([0, 1, 1, 0] : List (ZMod 2)) 1 = [1, 0] := by decide +kernel
example : restrictPrefixValues ([0, 1, 1, 0] : List (ZMod 2)) [1, 1] = [0] := by
  decide +kernel
example : restrictValues ([2, 5, 1, 7] : List (ZMod 8)) 2 = [0, 1] := by decide +kernel

-- Arbitrary dimensions and rings consume the proved bridge, not concrete reduction.
example {F : Type} [CommRing F] {n : Nat} (xs point : List F)
    (input : Table F (n + point.length))
    (decoded : ofList? (n + point.length) xs = some input) :
    ofList? n (restrictPrefixValues xs point) =
      some (fixPrefix point.length input (coordinates point.length point)) :=
  ofList?_restrictPrefixValues xs point input decoded

example {F : Type} [CommRing F] (xs point : List F)
    (input : Table F (0 + point.length))
    (decoded : ofList? (0 + point.length) xs = some input) :
    restrictPrefixValues xs point =
      [extension (0 + point.length) input
        (Quadratic.point point.length (coordinates point.length point) Fin.elim0)] :=
  restrictPrefixValues_complete xs point input decoded

end MultilinearListRestrictionTests
