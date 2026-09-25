import Zkc.Relation.Sparse
import Zkc.Polynomial.Multilinear

/-! Sparse point evaluation of the existing ordered multilinear extension.
The first coordinate is the most significant bit, as in `Multilinear.index`.
Each basis weight takes linear work in the point dimension. No dense matrix
or dense coefficient polynomial is required by the executable definitions.
-/

set_option autoImplicit false

namespace Zkc.Relation.Sparse

open Zkc.Polynomial.Multilinear

variable {F : Type} [CommRing F]

def basis : (d : Nat) → (Fin d → Bool) → (Fin d → F) → F
  | 0, _, _ => 1
  | d + 1, bits, point =>
      (if bits 0 then point 0 else 1 - point 0) * basis d (bits ∘ Fin.succ) (point ∘ Fin.succ)

def weight (d : Nat) (j : Fin (2 ^ d)) (point : Fin d → F) : F :=
  basis d (vertex d j) point

theorem extension_add (d : Nat) (left right : Table F d) (point : Fin d → F) :
    extension d (fun bits => left bits + right bits) point =
      extension d left point + extension d right point := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [extension, ih]; ring

theorem extension_scale (d : Nat) (c : F) (table : Table F d) (point : Fin d → F) :
    extension d (fun bits => c * table bits) point = c * extension d table point := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [extension, ih]; ring

theorem extension_constant (d : Nat) (c : F) (point : Fin d → F) :
    extension d (fun _ => c) point = c := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [extension, ih]; ring

theorem extension_indicator (d : Nat) (bits : Fin d → Bool) (point : Fin d → F) :
    extension d (fun other => if other = bits then 1 else 0) point = basis d bits point := by
  induction d with
  | zero =>
      have h : (Fin.elim0 : Fin 0 → Bool) = bits := funext fun i => Fin.elim0 i
      simp [extension, basis, h]
  | succ d ih =>
      conv_lhs => arg 2; intro other; rw [← Fin.cons_self_tail bits]
      simp only [extension, Fin.cons_inj]
      cases h : bits 0 <;>
        simp [h, basis, ih, extension_constant, Function.comp_def] <;> rfl

theorem extension_column (d : Nat) (j : Fin (2 ^ d)) (point : Fin d → F) :
    extension d (fun bits => if index d bits = j then 1 else 0) point = weight d j point := by
  have eq : ∀ bits, index d bits = j ↔ bits = vertex d j := by
    intro bits
    constructor
    · intro h
      rw [← vertex_index d bits, h]
    · rintro rfl
      exact index_vertex d j
  simp only [eq]
  exact extension_indicator d (vertex d j) point

/-- Sparse coefficients denote the existing table extension at every point,
including non-Boolean points and duplicate/canceling entries. -/
theorem extension_coefficients (d : Nat) (row : Row F (2 ^ d)) (point : Fin d → F) :
    extension d (ofVector (coefficient row)) point = eval row (fun j => weight d j point) := by
  induction row with
  | nil => exact extension_constant d 0 point
  | cons entry row ih =>
      change extension d (fun bits =>
        entry.2 * (if entry.1 = index d bits then 1 else 0) +
        coefficient row (index d bits)) point = _
      rw [extension_add, extension_scale]
      simp only [eq_comm (a := entry.1), extension_column]
      rw [show extension d (fun bits => coefficient row (index d bits)) point =
        eval row (fun j => weight d j point) from ih]
      rfl

theorem extension_vector (d : Nat) (values : Fin (2 ^ d) → F) (point : Fin d → F) :
    extension d (ofVector values) point = ∑ j, values j * weight d j point := by
  let row : Row F (2 ^ d) := List.ofFn fun j => (j, values j)
  have coefficients : coefficient row = values := by
    funext j
    simp [row, coefficient, eval, List.map_ofFn, Function.comp_def, Fin.sum_ofFn, mul_ite]
  rw [← coefficients, extension_coefficients]
  simp [row, eval, List.map_ofFn, Function.comp_def, Fin.sum_ofFn, coefficients]

theorem weight_boolean (d : Nat) (j : Fin (2 ^ d)) (bits : Fin d → Bool) :
    weight (F := F) d j (booleanPoint bits) = if index d bits = j then 1 else 0 := by
  rw [← extension_column, extension_boolean]

namespace Matrix

def atPoint {r c : Nat} (matrix : Matrix F (2 ^ r) (2 ^ c))
    (rowPoint : Fin r → F) (columnPoint : Fin c → F) : F :=
  matrix.bilinear (fun i => weight r i rowPoint) (fun j => weight c j columnPoint)

/-- The contracted column table is extended, rather than the pointwise product
of two tables. This identifies the precise verifier-side polynomial view. -/
theorem atPoint_contracted {r c : Nat} (matrix : Matrix F (2 ^ r) (2 ^ c))
    (rowPoint : Fin r → F) (columnPoint : Fin c → F) :
    matrix.atPoint rowPoint columnPoint =
      extension c (ofVector (coefficient (matrix.contract (fun i => weight r i rowPoint))))
        columnPoint :=
  (extension_coefficients c _ columnPoint).symm

/-- Exact tensor extension of the fixed matrix, with the existing coordinate order. -/
theorem atPoint_tensor {r c : Nat} (matrix : Matrix F (2 ^ r) (2 ^ c))
    (rowPoint : Fin r → F) (columnPoint : Fin c → F) :
    matrix.atPoint rowPoint columnPoint = extension r
      (ofVector fun i => extension c (ofVector (matrix.denote i)) columnPoint) rowPoint := by
  rw [extension_vector]
  simp only [atPoint, bilinear, eval_contract]
  apply Finset.sum_congr rfl
  intro i _
  change _ = extension c (ofVector (coefficient matrix.rows[i])) columnPoint * weight r i rowPoint
  rw [extension_coefficients, mul_comm]

theorem atPoint_boolean {r c : Nat} (matrix : Matrix F (2 ^ r) (2 ^ c))
    (rowBits : Fin r → Bool) (columnBits : Fin c → Bool) :
    matrix.atPoint (booleanPoint rowBits) (booleanPoint columnBits) =
      matrix.denote (index r rowBits) (index c columnBits) := by
  rw [atPoint_tensor, extension_boolean]
  exact extension_boolean c _ columnBits

end Matrix
end Zkc.Relation.Sparse
