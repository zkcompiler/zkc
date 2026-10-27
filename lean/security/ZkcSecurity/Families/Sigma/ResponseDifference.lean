module

public import ZkcSecurity.Families.Sigma.LinearCertificate
public import VCVio.Schemes.Schnorr.SigmaProtocol
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases

public section

/-! A certificate method for the fixed response-difference arithmetic. The
coefficients cancel the shared commitment and isolate the public key. This
proof uses neither VCVio's Schnorr special-soundness theorem nor its module
equation proof; the common forking consumer remains reusable. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sigma.ResponseDifference
open scoped BigOperators

variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G]

@[expose] def rows (first second response₁ response₂ : F) : Fin 2 → Fin 3 → F :=
  ![![response₁, -first, -1], ![response₂, -second, -1]]

@[expose] def target (first second response₁ response₂ : F) : Fin 3 → F :=
  ![(response₁ - response₂) / (first - second), -1, 0]

@[expose] def coefficients (first second : F) : Fin 2 → F :=
  ![(first - second)⁻¹, -(first - second)⁻¹]

theorem checked (first second response₁ response₂ : F) (distinct : first ≠ second) :
    LinearCertificate.check (rows first second response₁ response₂)
      (target first second response₁ response₂) (coefficients first second) = true := by
  unfold LinearCertificate.check
  simp only [decide_eq_true_eq]
  intro coordinate
  have nonzero := sub_ne_zero.mpr distinct
  fin_cases coordinate <;>
    simp [rows, target, coefficients, Fin.sum_univ_succ] <;> field_simp [nonzero] <;> ring

theorem recover (base key commitment : G) (first second response₁ response₂ : F)
    (distinct : first ≠ second)
    (accepted₁ : response₁ • base = commitment + first • key)
    (accepted₂ : response₂ • base = commitment + second • key) :
    ((response₁ - response₂) / (first - second)) • base = key := by
  have accepted : ∀ row,
      LinearCertificate.evaluate (rows first second response₁ response₂ row)
        ![base, key, commitment] = 0 := by
    intro row
    fin_cases row <;>
      simp [LinearCertificate.evaluate, rows, Fin.sum_univ_succ, accepted₁, accepted₂]
  have result := LinearCertificate.soundness (rows first second response₁ response₂)
    (target first second response₁ response₂) (coefficients first second)
    (checked first second response₁ response₂ distinct) ![base, key, commitment] accepted
  apply sub_eq_zero.mp
  simpa [LinearCertificate.evaluate, target, Fin.sum_univ_succ, ← sub_eq_add_neg] using result

theorem shared_challenge (base₁ key₁ commitment₁ base₂ key₂ commitment₂ : G)
    (first second left₁ left₂ right₁ right₂ : F) (distinct : first ≠ second)
    (firstLeft : left₁ • base₁ = commitment₁ + first • key₁)
    (secondLeft : left₂ • base₁ = commitment₁ + second • key₁)
    (firstRight : right₁ • base₂ = commitment₂ + first • key₂)
    (secondRight : right₂ • base₂ = commitment₂ + second • key₂) :
    ((left₁ - left₂) / (first - second)) • base₁ = key₁ ∧
      ((right₁ - right₂) / (first - second)) • base₂ = key₂ :=
  ⟨recover _ _ _ _ _ _ _ distinct firstLeft secondLeft,
    recover _ _ _ _ _ _ _ distinct firstRight secondRight⟩

theorem speciallySound [DecidableEq G] [SampleableType F] [SampleableType G] (base : G) :
    (_root_.Schnorr.sigma F G base).SpeciallySound := by
  intro key commitment first second response₁ response₂ distinct accepted₁ accepted₂ witness supported
  dsimp [_root_.Schnorr.sigma] at *
  simp only [Set.mem_singleton_iff] at supported
  subst witness
  simp only [decide_eq_true_eq] at accepted₁ accepted₂ ⊢
  simpa only [div_eq_mul_inv] using recover base key commitment first second response₁ response₂
    distinct accepted₁ accepted₂

end ZkcSecurity.Families.Sigma.ResponseDifference
