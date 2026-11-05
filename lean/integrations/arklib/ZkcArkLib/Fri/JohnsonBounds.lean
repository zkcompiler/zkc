/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability

@[expose] public section

/-! # Johnson bounds at the affine-line boundary

The exact-agreement conversions below expose intermediate statements from ArkLib's
`Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Johnson/Probability.lean`
at revision `1e0241333c18d8b22cb68f9522da5f9fb88f9a06` (Quang Dao, Apache 2.0).
The upstream probability bounds are imported directly; no local probability conversion is kept.
This module keeps the uniform, all-candidate `LineExactAgreementBound` visible: for each pair
of words one exceptional set is chosen before the challenge and before every close candidate.
No existentially selected candidate replaces this quantifier.
-/

namespace ZkcSecurity.ArkLib.Fri

open CoreDefinitions ReedSolomon ReedSolomon.HiddenDerivative

variable {F : Type} [Field F]

/-- The pinned Johnson root gives exact agreement simultaneously for all close polynomials. -/
theorem johnson_exactAgreement [DecidableEq F] {n degree : ℕ} {eta : ℝ}
    (domain : Fin n ↪ F) (positiveDegree : 1 ≤ degree) (degreeBound : degree ≤ n - 2)
    (positiveSlack : 0 < eta) (agreementBound : johnsonAgreement n degree eta ≤ 1) :
    LineExactAgreementBound domain (degree + 1) ⌈johnsonAgreement n degree eta * n⌉₊
      (johnsonExceptionCount n degree ⌈johnsonAgreement n degree eta * n⌉₊ eta) := by
  intro f g
  obtain ⟨exceptional, cardinality, good⟩ :=
    exists_johnson_line_exactCorrelatedPair_ceil domain f g positiveDegree degreeBound
      positiveSlack agreementBound
  refine ⟨exceptional, cardinality, fun z hz candidate degree agreement ↦ ?_⟩
  obtain ⟨pair, degreeLow, degreeHigh, specialization, agreementSet⟩ :=
    good z hz candidate degree (by convert agreement)
  refine ⟨pair.1, pair.2, degreeLow, degreeHigh, ?_, ?_⟩
  · simpa [correlatedPairSpecialization] using specialization
  · ext i
    have membership := congrArg (i ∈ ·) agreementSet
    simpa only [polynomialAgreementSet, commonPolynomialAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and, eq_iff_iff, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk, RingHom.id_apply] using membership

/-- A weighted certificate gives one exceptional set valid for every close candidate. -/
theorem weightedJohnson_exactAgreement [DecidableEq F] {n degree A multiplicity B H : ℕ}
    (domain : Fin n ↪ F) (certificate : IsJohnsonWeightedCertificate n degree A multiplicity B H)
    (positiveDegree : 1 ≤ degree) (degreeThreshold : degree + 1 ≤ A) (thresholdSize : A ≤ n)
    (cutoff : B ≤ 2 * degree + 1) :
    LineExactAgreementBound domain (degree + 1) A
      (johnsonWeightedRefinedExceptionCount n degree A B H : ℝ) := by
  intro f g
  obtain ⟨exceptional, cardinality, good⟩ :=
    exists_weightedJohnson_line_exactCorrelatedPair domain f g certificate positiveDegree
      degreeThreshold thresholdSize cutoff
  refine ⟨exceptional, by exact_mod_cast cardinality,
    fun z hz candidate degree agreement ↦ ?_⟩
  obtain ⟨pair, degreeLow, degreeHigh, specialization, agreementSet⟩ :=
    good z hz candidate degree (by convert agreement)
  refine ⟨pair.1, pair.2, degreeLow, degreeHigh, ?_, ?_⟩
  · simpa [correlatedPairSpecialization] using specialization
  · ext i
    have membership := congrArg (i ∈ ·) agreementSet
    simpa only [polynomialAgreementSet, commonPolynomialAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and, eq_iff_iff, Function.Embedding.trans_apply,
      Function.Embedding.coeFn_mk, RingHom.id_apply] using membership


end ZkcSecurity.ArkLib.Fri
