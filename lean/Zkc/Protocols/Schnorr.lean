import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Abel

/-! Algebraic completeness and two-response extraction for the Schnorr equation.

These laws require the same base, public key and nonce commitment. They do not
establish a forking lemma, random-oracle reduction, nonce-generation security,
knowledge of a secret in one execution, or a correspondence with native code.
The extraction law also explains why nonce custody is a separate resource rule.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Schnorr

variable {F G : Type*} [Field F] [AddCommGroup G] [Module F G]

theorem response_equation (nonce challenge secret : F) (base : G) :
    (nonce + challenge * secret) • base =
      nonce • base + challenge • (secret • base) := by
  rw [add_smul, smul_smul]

/-- Two accepting responses to different challenges at the *same* nonce
commitment determine a scalar opening of the public key. No independence or
probability premise is inferred from the two equations. -/
theorem extract_public_key (base key commitment : G)
    (challenge₁ challenge₂ response₁ response₂ : F)
    (distinct : challenge₁ ≠ challenge₂)
    (first : response₁ • base = commitment + challenge₁ • key)
    (second : response₂ • base = commitment + challenge₂ • key) :
    ((response₁ - response₂) / (challenge₁ - challenge₂)) • base = key := by
  have difference : (response₁ - response₂) • base =
      (challenge₁ - challenge₂) • key := by
    rw [sub_smul, first, second, sub_smul]
    abel
  calc
    ((response₁ - response₂) / (challenge₁ - challenge₂)) • base =
        (challenge₁ - challenge₂)⁻¹ • ((response₁ - response₂) • base) := by
      rw [smul_smul, div_eq_mul_inv, mul_comm]
    _ = (challenge₁ - challenge₂)⁻¹ • ((challenge₁ - challenge₂) • key) := by
      rw [difference]
    _ = key := by rw [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr distinct), one_smul]

end Zkc.Protocols.Schnorr
