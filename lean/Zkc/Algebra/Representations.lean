import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Tactic.Ring

/-!
# Representation and ordered-domain laws

Conditional mathematical facts only. A native adapter must separately establish
that its decoded/cleared carrier has the asserted action. In particular these
lemmas install no scalar-field module structure on raw Edwards representatives.
-/
set_option autoImplicit false
namespace Zkc.Algebra.Representations

/-- Keep the observation and the arithmetic image simultaneously. No inverse of
`image` and no permission to replace `raw` observations is implied. -/
structure ObservedImage (Raw Image : Type*) (image : Raw → Image) where
  raw : Raw
  arithmetic : Image
  agrees : image raw = arithmetic

variable {Raw Image : Type*} {image : Raw → Image}

def decodeAndClear (raw : Raw) (image : Raw → Image) : ObservedImage Raw Image image :=
  ⟨raw, image raw, rfl⟩

@[simp] theorem decodeAndClear_observation (raw : Raw) :
    (decodeAndClear raw image).raw = raw := rfl

/-- Different raw observations can have the same image. Arithmetic equality
cannot establish equality of transcript observations. -/
theorem same_image_not_raw (a b : ObservedImage Raw Image image)
    (same : image a.raw = image b.raw) (different : a.raw ≠ b.raw) :
    a.arithmetic = b.arithmetic ∧ a.raw ≠ b.raw := by
  exact ⟨a.agrees.symm.trans (same.trans b.agrees), different⟩

variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]

/-- Module evidence is an explicit typeclass premise, never inferred from the
ability to decode a point. -/
theorem scalar_reassociate (a b : F) (p : M) :
    a • (b • p) = (a * b) • p := smul_smul a b p

theorem inverse_eight_rewrite (a : F) (p : M) :
    a • ((8 : F)⁻¹ • p) = (a * (8 : F)⁻¹) • p := smul_smul _ _ _

theorem inverse_eight_cancel (nonzero : (8 : F) ≠ 0) (p : M) :
    (8 : F) • ((8 : F)⁻¹ • p) = p := by
  rw [smul_smul, mul_inv_cancel₀ nonzero, one_smul]

/-- One Boolean-axis interpolation, with the low/high endpoints explicit. -/
def lerp (r a b : F) : F := a + r * (b - a)

/-- Two adjacent folds equal half-first folds on the transposed table, with
coordinates identified correctly. This is not permission to reverse only the
challenge list. -/
theorem adjacent_half_transpose (r s a b c d : F) :
    lerp s (lerp r a b) (lerp r c d) =
      lerp r (lerp s a c) (lerp s b d) := by
  simp only [lerp]
  ring

variable {E : Type*} [Field E]

theorem embedding_lerp (embedding : F →+* E) (r a b : F) :
    embedding (lerp r a b) = lerp (embedding r) (embedding a) (embedding b) := by
  simp only [lerp, map_add, map_mul, map_sub]

/-- A domain map is evidence of a bijection of actual index types. -/
def reindex {I J : Type*} (axes : J ≃ I) (values : I → F) : J → F :=
  fun j => values (axes j)

omit [Field F] in
theorem reindex_inverse {I J : Type*} (axes : J ≃ I) (values : I → F) :
    reindex axes.symm (reindex axes values) = values := by
  funext i
  simp [reindex]

/-- A cyclic rotation is a permutation, not an MLE challenge substitution. -/
def rotate {n : Nat} (shift : Fin n) (values : Fin n → F) : Fin n → F :=
  fun i => values (i + shift)

omit [Field F] in
theorem rotate_add {n : Nat} (a b : Fin n) (values : Fin n → F) :
    rotate a (rotate b values) = rotate (a + b) values := by
  funext i
  simp only [rotate]
  congr 1
  exact add_assoc i a b

end Zkc.Algebra.Representations
