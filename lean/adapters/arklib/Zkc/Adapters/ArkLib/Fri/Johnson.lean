module

public import Zkc.Adapters.ArkLib.Fri.JohnsonBounds
public import Zkc.Adapters.ArkLib.Fri.Soundness

@[expose] public section

/-! # Binary FRI folding from Johnson mutual correlated agreement

The affine-line generator is exactly the one-dimensional powers generator of binary FRI.
These adapters use the existing `FoldingProximity` and `FoldingEscapes` interfaces. The `cons`
lemmas assemble a chain from independently supplied round premises and an existing tail, so
different certificates can serve different rounds without a new soundness engine.

Every Johnson head has code dimension at least two. In the `cons` lemmas this is the explicit
premise `2 ≤ degreeBound R (2 ^ t)`. A dimension-one terminal head, including that of the
unchanged scalar demo, is outside this adapter. None of these mathematical statements asserts
source association, sampler realization, commitment security or native FRI/STARK security.
-/

namespace ZkcSecurity.ArkLib.Fri

open CoreDefinitions ReedSolomon.HiddenDerivative Domain OracleComp

variable {F : Type} [Field F] [Fintype F] [SampleableType F]

/-- The Johnson bound on the precise powers generator and subdomain used by binary FRI. -/
theorem johnson_folding_head {m degree : ℕ} {eta : ℝ}
    (domain : SmoothCosetFftDomain (m + 1) F)
    (positiveDegree : 1 ≤ degree) (degreeSize : degree ≤ 2 ^ (m + 1 - 1) - 2)
    (positiveSlack : 0 < eta)
    (agreementBound : johnsonAgreement (2 ^ (m + 1 - 1)) degree eta ≤ 1) :
    mcaError (univariatePowersGenerator F (2 ^ 1 - 1))
        (ReedSolomon.code (domain.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F) (degree + 1))
        (1 - johnsonAgreement (2 ^ (m + 1 - 1)) degree eta) ≤
      min 1 (ENNReal.ofReal
        (johnsonExceptionCount (2 ^ (m + 1 - 1)) degree
          ⌈johnsonAgreement (2 ^ (m + 1 - 1)) degree eta * (2 ^ (m + 1 - 1) : ℕ)⌉₊ eta /
            (Fintype.card F : ℝ))) := by
  have generator : univariatePowersGenerator F (2 ^ 1 - 1) = AffineLineGenerator F :=
    univariatePowersGenerator_one_eq_affineLineGenerator
  rw [generator]
  exact ReedSolomon.mcaError_affineLine_johnson_le (domain.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F)
    positiveDegree degreeSize positiveSlack agreementBound

/-- A weighted certificate bounds the actual binary-folding MCA head. -/
theorem weightedJohnson_folding_head {m degree A multiplicity B H : ℕ}
    (domain : SmoothCosetFftDomain (m + 1) F)
    (certificate : IsJohnsonWeightedCertificate (2 ^ (m + 1 - 1)) degree A multiplicity B H)
    (positiveDegree : 1 ≤ degree) (degreeThreshold : degree + 1 ≤ A)
    (thresholdSize : A ≤ 2 ^ (m + 1 - 1)) (cutoff : B ≤ 2 * degree + 1) (radius : ℝ)
    (threshold : A ≤ ⌈((2 ^ (m + 1 - 1) : ℕ) : ℝ) * (1 - radius)⌉₊) :
    mcaError (univariatePowersGenerator F (2 ^ 1 - 1))
        (ReedSolomon.code (domain.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F) (degree + 1))
        radius ≤
      min 1 (ENNReal.ofReal
        ((johnsonWeightedRefinedExceptionCount (2 ^ (m + 1 - 1)) degree A B H : ℝ) /
          Fintype.card F)) := by
  have generator : univariatePowersGenerator F (2 ^ 1 - 1) = AffineLineGenerator F :=
    univariatePowersGenerator_one_eq_affineLineGenerator
  rw [generator]
  exact ReedSolomon.mcaError_affineLine_weightedJohnson_le (domain.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F)
    certificate positiveDegree degreeThreshold thresholdSize cutoff radius threshold

variable [DecidableEq F]

/-- For every previously fixed word, a uniform fold challenge has the Johnson escape bound. -/
theorem johnson_fold_escape {m degree : ℕ} {eta : ℝ}
    (domain : SmoothCosetFftDomain (m + 1) F)
    (positiveDegree : 1 ≤ degree) (degreeSize : degree ≤ 2 ^ (m + 1 - 1) - 2)
    (positiveSlack : 0 < eta)
    (agreementBound : johnsonAgreement (2 ^ (m + 1 - 1)) degree eta ≤ 1)
    (word : Fin (2 ^ (m + 1)) → F) :
    Pr{let beta ← $ᵗ F}[_root_.Fri.FoldingAgreementFailure domain word 1 (degree + 1)
        (1 - johnsonAgreement (2 ^ (m + 1 - 1)) degree eta) beta] ≤
      min 1 (ENNReal.ofReal
        (johnsonExceptionCount (2 ^ (m + 1 - 1)) degree
          ⌈johnsonAgreement (2 ^ (m + 1 - 1)) degree eta * (2 ^ (m + 1 - 1) : ℕ)⌉₊ eta /
            (Fintype.card F : ℝ))) :=
  (_root_.Fri.foldingAgreementFailure_prob_le_powers domain word (by omega) _).trans
    (johnson_folding_head domain positiveDegree degreeSize positiveSlack agreementBound)

/-- Weighted Johnson escape bound, uniform over every previously fixed word. -/
theorem weightedJohnson_fold_escape {m degree A multiplicity B H : ℕ}
    (domain : SmoothCosetFftDomain (m + 1) F)
    (certificate : IsJohnsonWeightedCertificate (2 ^ (m + 1 - 1)) degree A multiplicity B H)
    (positiveDegree : 1 ≤ degree) (degreeThreshold : degree + 1 ≤ A)
    (thresholdSize : A ≤ 2 ^ (m + 1 - 1)) (cutoff : B ≤ 2 * degree + 1) (radius : ℝ)
    (threshold : A ≤ ⌈((2 ^ (m + 1 - 1) : ℕ) : ℝ) * (1 - radius)⌉₊)
    (word : Fin (2 ^ (m + 1)) → F) :
    Pr{let beta ← $ᵗ F}[_root_.Fri.FoldingAgreementFailure domain word 1 (degree + 1)
        radius beta] ≤
      min 1 (ENNReal.ofReal
        ((johnsonWeightedRefinedExceptionCount (2 ^ (m + 1 - 1)) degree A B H : ℝ) /
          Fintype.card F)) :=
  (_root_.Fri.foldingAgreementFailure_prob_le_powers domain word (by omega) radius).trans
    (weightedJohnson_folding_head domain certificate positiveDegree degreeThreshold thresholdSize
      cutoff radius threshold)

omit [DecidableEq F] in
/-- Prepend a Johnson round to an existing proximity chain. The equality fixes the common
radius; each round may use its own positive slack and exception count. -/
theorem foldingProximity_cons_johnson {m R t : ℕ} {radius eta : ℝ} {error : ℕ → ENNReal}
    (domain : SmoothCosetFftDomain (m + 1) F)
    (dimension : 2 ≤ degreeBound R (2 ^ t))
    (degreeSize : degreeBound R (2 ^ t) - 1 ≤ 2 ^ (m + 1 - 1) - 2)
    (positiveSlack : 0 < eta)
    (agreementBound : johnsonAgreement (2 ^ (m + 1 - 1)) (degreeBound R (2 ^ t) - 1) eta ≤ 1)
    (radiusEquation : radius =
      1 - johnsonAgreement (2 ^ (m + 1 - 1)) (degreeBound R (2 ^ t) - 1) eta)
    (headError : min 1 (ENNReal.ofReal
      (johnsonExceptionCount (2 ^ (m + 1 - 1)) (degreeBound R (2 ^ t) - 1)
        ⌈johnsonAgreement (2 ^ (m + 1 - 1)) (degreeBound R (2 ^ t) - 1) eta *
          (2 ^ (m + 1 - 1) : ℕ)⌉₊ eta / (Fintype.card F : ℝ))) ≤ error 0)
    (tail : FoldingProximity t radius (domain.subdomain 1) R (fun round ↦ error (round + 1))) :
    FoldingProximity t radius domain (R + 1) error := by
  refine ⟨?_, tail⟩
  have head := johnson_folding_head domain (by omega : 1 ≤ degreeBound R (2 ^ t) - 1)
    degreeSize positiveSlack agreementBound
  rw [Nat.sub_add_cancel (by omega : 1 ≤ degreeBound R (2 ^ t)), ← radiusEquation] at head
  exact head.trans headError

omit [DecidableEq F] in
/-- Prepend a weighted Johnson round, retaining the existing round numbering and tail API. -/
theorem foldingProximity_cons_weightedJohnson {m R t A multiplicity B H : ℕ} {radius : ℝ}
    {error : ℕ → ENNReal} (domain : SmoothCosetFftDomain (m + 1) F)
    (dimension : 2 ≤ degreeBound R (2 ^ t))
    (certificate : IsJohnsonWeightedCertificate (2 ^ (m + 1 - 1))
      (degreeBound R (2 ^ t) - 1) A multiplicity B H)
    (degreeThreshold : degreeBound R (2 ^ t) ≤ A) (thresholdSize : A ≤ 2 ^ (m + 1 - 1))
    (cutoff : B ≤ 2 * (degreeBound R (2 ^ t) - 1) + 1)
    (threshold : A ≤ ⌈((2 ^ (m + 1 - 1) : ℕ) : ℝ) * (1 - radius)⌉₊)
    (headError : min 1 (ENNReal.ofReal
      ((johnsonWeightedRefinedExceptionCount (2 ^ (m + 1 - 1))
        (degreeBound R (2 ^ t) - 1) A B H : ℝ) / Fintype.card F)) ≤ error 0)
    (tail : FoldingProximity t radius (domain.subdomain 1) R (fun round ↦ error (round + 1))) :
    FoldingProximity t radius domain (R + 1) error := by
  refine ⟨?_, tail⟩
  have head := weightedJohnson_folding_head domain certificate
    (by omega : 1 ≤ degreeBound R (2 ^ t) - 1) (by omega) thresholdSize cutoff radius threshold
  rw [Nat.sub_add_cancel (by omega : 1 ≤ degreeBound R (2 ^ t))] at head
  exact head.trans headError

end ZkcSecurity.ArkLib.Fri
