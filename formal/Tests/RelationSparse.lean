import Zkc.Relation.SparsePolynomial
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace Tests.RelationSparse

open scoped Matrix

open Zkc.Relation.Sparse
open Zkc.Polynomial.Multilinear

def matrix : Matrix (ZMod 101) 2 4 :=
  ⟨#v[[(0, 2), (3, 5)], [(1, 7), (2, -1)]]⟩

private def z : Fin 4 → ZMod 101 := ![1, 2, 3, 4]
private def rowWeights : Fin 2 → ZMod 101 := ![3, 11]

example : (matrix.mul z).toArray = #[22, 11] := by decide
example : matrix.contract rowWeights = [(0, 6), (3, 15), (1, 77), (2, -11)] := by decide
example : matrix.bilinear rowWeights z = 86 := by decide
example : matrix.bilinear rowWeights z =
    Zkc.Algebra.linearCombination (rowWeights ᵥ* matrix.denote) z :=
  matrix.contract_linearCombination rowWeights z

-- Repeated columns cancel correctly; noncanonical internal views are meaningful.
example : eval ([(1, 7), (1, -7), (3, 0)] : Row (ZMod 101) 4) z = 0 := by decide

example : eval (eraseZeros ([(0, 0), (2, 9), (1, 0)] : Row (ZMod 101) 4)) z = 27 := by decide

-- Non-Boolean points distinguish interpolation from looking up one cell.
example : matrix.atPoint (![2] : Fin 1 → ZMod 101) (![3, 4] : Fin 2 → ZMod 101) = 36 := by decide

example : matrix.atPoint (![2] : Fin 1 → ZMod 101) (![3, 4] : Fin 2 → ZMod 101) =
    extension 1 (ofVector fun i => extension 2 (ofVector (matrix.denote i)) ![3, 4]) ![2] :=
  Matrix.atPoint_tensor (r := 1) (c := 2) matrix _ _

example : matrix.atPoint (booleanPoint ![true]) (booleanPoint ![false, true]) = 7 := by decide

-- Empty dimensions denote a zero map and execute without a dense allocation.
example : ((⟨#v[]⟩ : Matrix (ZMod 101) 0 3).mul ![1, 2, 3]).toArray = #[] := by decide
example : ((⟨#v[[], []]⟩ : Matrix (ZMod 101) 2 0).mul Fin.elim0).toArray = #[0, 0] := by decide

end Tests.RelationSparse
