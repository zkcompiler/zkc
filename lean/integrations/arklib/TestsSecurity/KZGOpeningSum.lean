module
public import ZkcSecurity.ArkLib.KZG.OpeningSum
public import CompPoly.Univariate.Bytes
import all CompPoly.Univariate.ToPoly.Degree

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Concrete algebra controls use a transparent exponent group over F₇.
This deliberately insecure group checks the implementation and reduction, not
a cryptographic hardness claim. The source executes actual KZG pairing checks.
-/

namespace TestsSecurity.KZGOpeningSum
open ZkcSecurity.ArkLib.KZG.OpeningSum
open Zkc.Protocols.OpeningSum

abbrev F := ZMod 7
instance : Fact (Nat.Prime 7) := ⟨by decide⟩
abbrev G := Multiplicative F
instance : PrimeOrderWith G 7 := ⟨by simp [G, F, Nat.card_eq_fintype_card]⟩
instance : Module F (Additive G) := inferInstanceAs (Module F F)

def pairing : Additive G →ₗ[F] Additive G →ₗ[F] Additive G := LinearMap.mul F F
def generator : G := Multiplicative.ofAdd (1 : F)
def srs := Groups.PowerSrs.generate (g₁ := generator) (g₂ := generator) 2 (3 : F)
def coefficients : Fin 3 → F := ![2, 4, 1]
def honest : Submission 7 G 2 :=
  ⟨coefficients, 0, 1, 2, ⟨2, Multiplicative.ofAdd 0⟩, ⟨0, Multiplicative.ofAdd 1⟩⟩

theorem check_exponents (commitment point value proof : F) :
    check (g₁ := generator) (g₂ := generator) pairing srs.2
      (Multiplicative.ofAdd commitment) point ⟨value, Multiplicative.ofAdd proof⟩ =
      decide (commitment - value = proof * (3 - point)) := by
  simp only [check, KZG.verifyOpening, pairing, srs, Groups.PowerSrs.generate,
    Groups.PowerSrs.tower, generator, Vector.getElem_ofFn]
  change decide ((commitment - value.val • (1 : F)) * 1 =
    proof * ((3 : F) - point.val • (1 : F))) = _
  simp [nsmul_eq_mul]

theorem honest_source :
    (sourceExecution (g₁ := generator) (g₂ := generator) pairing srs
      (honestSubmission srs.1 coefficients (0 : F) (1 : F))).outcome =
      PIR.Outcome.returned true :=
  honest_source_accepts pairing 3 coefficients 0 1

theorem actual_polynomial_values :
    evaluate coefficients 0 = 2 ∧ evaluate coefficients 1 = 0 := by
  simp only [evaluate, CompPoly.CPolynomial.eval_eq_sum_degreeLTEquiv
    (CompPoly.CPolynomial.ofFn_mem_degreeLT coefficients)]
  simp only [CompPoly.CPolynomial.degreeLTEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk,
    CompPoly.CPolynomial.degreeLTCoeffs_apply, CompPoly.CPolynomial.coeff_ofFn,
    Fin.isLt, dite_true]
  simp [Fin.sum_univ_succ, coefficients]
  decide +kernel

theorem honest_commitment : KZG.commit srs.1 coefficients = Multiplicative.ofAdd (2 : F) := by
  simp [KZG.commit, srs, Groups.PowerSrs.generate, Groups.PowerSrs.tower,
    coefficients, Fin.prod_univ_succ, generator]
  decide +kernel

theorem changed_claim_rejects :
    (sourceExecution (g₁ := generator) (g₂ := generator) pairing srs
      { honest with claim := 3 }).outcome = PIR.Outcome.returned false := by
  unfold sourceExecution
  rw [program_denote]
  simp only [statement, honest]
  rw [honest_commitment]
  simp only [reference, PIR.Proc.run, replay, PIR.Execution.follow, check_exponents,
    ↓reduceIte, Nat.reduceAdd]
  norm_num
  simp only [PIR.Proc.run, replay, PIR.Execution.follow, check_exponents,
    ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff]
  norm_num
  rfl

theorem changed_opening_rejects :
    (sourceExecution (g₁ := generator) (g₂ := generator) pairing srs
      { honest with left := { honest.left with value := 3 } }).outcome =
        PIR.Outcome.stopped .reject := by
  unfold sourceExecution
  rw [program_denote]
  simp only [statement, honest]
  rw [honest_commitment]
  simp only [reference, PIR.Proc.run, replay, PIR.Execution.follow, check_exponents,
    ↓reduceIte, Nat.reduceAdd]
  norm_num
  rfl

/-- Knowing the trapdoor permits a false opening; security therefore cannot be
concluded from the algebraic correctness theorem alone. -/
def forged : Submission 7 G 2 :=
  { honest with claim := 3, left := ⟨3, Multiplicative.ofAdd (2 : F)⟩ }

theorem forged_acceptance :
    (sourceExecution (g₁ := generator) (g₂ := generator) pairing srs forged).outcome =
      PIR.Outcome.returned true ∧ falseClaim forged := by
  constructor
  · apply (contract_accepted (source_contract _) _ _ _).mpr
    simp only [Accepted, statement, forged, honest]
    rw [honest_commitment]
    rw [check_exponents, check_exponents]
    decide +kernel
  · change (3 : F) ≠ evaluate coefficients 0 + evaluate coefficients 1
    rw [actual_polynomial_values.1, actual_polynomial_values.2]
    decide +kernel

theorem concrete_reduction :
    Groups.tSdhCondition (g₁ := generator) ((3 : F), extraction srs.1 forged) := by
  exact source_false_extract pairing (by decide +kernel) (by decide +kernel)
    3 forged forged_acceptance.1 forged_acceptance.2

#print axioms ZkcSecurity.ArkLib.KZG.OpeningSum.source_advantage
#print axioms ZkcSecurity.ArkLib.KZG.OpeningSum.contract_advantage
end TestsSecurity.KZGOpeningSum
