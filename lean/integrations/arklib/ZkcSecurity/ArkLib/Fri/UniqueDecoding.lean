module

public import ZkcSecurity.ArkLib.Fri.Soundness
public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.EpsCa

@[expose] public section

/-! # `fri::LowDegree` in the unique-decoding regime

This module discharges the proximity premise with ArkLib's proved unique-decoding results: the
powers generator of degree one is the affine line generator
(`univariatePowersGenerator_one_eq_affineLineGenerator`), and the line's mutual correlated
agreement error on a Reed–Solomon code is at most `|domain| / |F|` at any positive radius up to
the relative unique-decoding radius (`rs_mcaError_le_of_le_relUDR`, from [BCIKS20]). That radius
is `(1 - ρ) / 2` for rate `ρ` (`relativeUniqueDecodingRadius_RS_eq`), and binary folding keeps
the rate, so one radius serves every round.

For a coset of size `2^(n + 1)`, `R + 1` folds and final degree below `2^t`, folding round `r`
contributes `2^(n - r) / |F|`, the size of the folded domain over the field size, and the query
block `(1 - min θ δ)^s`.
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain OracleComp ProximityGap CoreDefinitions
open scoped NNReal

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

/-- The folding error of round `round` in the unique-decoding regime, for a chain starting at
log size `m`: the folded domain's size over the field size. -/
noncomputable def uniqueDecodingError (F : Type) [Fintype F] (m round : ℕ) : ENNReal :=
  (((2 ^ (m - (round + 1)) : ℕ) / Fintype.card F : ℝ≥0) : ENNReal)

theorem degreeBound_succ_div (R d m : ℕ) :
    (degreeBound (R + 1) d : ℝ≥0) / (2 ^ (m + 1) : ℝ≥0) = (degreeBound R d : ℝ≥0) / 2 ^ m := by
  rw [degreeBound]
  push_cast
  rw [pow_succ, mul_comm (2 ^ m : ℝ≥0) 2, mul_div_mul_left _ _ two_ne_zero]

/-- In the unique-decoding regime the proximity premise holds with
`uniqueDecodingError F m`, for every positive radius at most the common relative
unique-decoding radius `(1 - ρ) / 2` of the folded codes. -/
theorem foldingProximity_uniqueDecoding (t : ℕ) (θ : ℝ≥0) (hθ : 0 < θ) :
    ∀ {m : ℕ} (D : SmoothCosetFftDomain m F) (R : ℕ),
      degreeBound R (2 ^ t) ≤ 2 ^ m →
      θ ≤ ((1 : ℝ≥0) - (degreeBound R (2 ^ t) : ℝ≥0) / (2 ^ m : ℝ≥0)) / 2 →
      FoldingProximity t (θ : ℝ) D R (uniqueDecodingError F m)
  | 0, _, _, _, _ => by simp [FoldingProximity]
  | _ + 1, _, 0, _, _ => by simp [FoldingProximity]
  | m + 1, D, R + 1, hsize, hradius => by
      have hsize' : degreeBound R (2 ^ t) ≤ 2 ^ m := by
        rw [degreeBound, pow_succ] at hsize
        omega
      have hradius' : θ ≤ ((1 : ℝ≥0) - (degreeBound R (2 ^ t) : ℝ≥0) / (2 ^ m : ℝ≥0)) / 2 := by
        rwa [degreeBound_succ_div] at hradius
      have : NeZero (degreeBound R (2 ^ t)) := ⟨(degreeBound_pos (by positivity) R).ne'⟩
      refine ⟨?_, ?_⟩
      · have hcard : Fintype.card (Fin (2 ^ (m + 1 - 1))) = 2 ^ m := by simp
        have hudr : θ ≤ Code.relativeUniqueDecodingRadius (ι := Fin (2 ^ (m + 1 - 1))) (F := F)
            (C := ReedSolomon.code (D.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F)
              (degreeBound R (2 ^ t))) := by
          rw [ReedSolomon.relativeUniqueDecodingRadius_RS_eq (by rw [hcard]; exact hsize'), hcard]
          exact_mod_cast hradius'
        have hmca := rs_mcaError_le_of_le_relUDR hθ hudr
        rw [← univariatePowersGenerator_one_eq_affineLineGenerator] at hmca
        refine le_of_le_of_eq hmca ?_
        simp [uniqueDecodingError]
      · have herror : (fun round => uniqueDecodingError F (m + 1) (round + 1)) =
            uniqueDecodingError F m := by
          funext round
          simp only [uniqueDecodingError]
          rw [show m + 1 - (round + 1 + 1) = m - (round + 1) by omega]
        rw [herror]
        exact foldingProximity_uniqueDecoding t θ hθ (D.subdomain 1) R hsize' hradius'

/-- The folded domains' sizes `2^(m - 1), ..., 2^(m - R)` and the last one sum to `2^m`. -/
theorem sum_folded_sizes (m : ℕ) :
    ∀ R ≤ m, ∑ round ∈ Finset.range R, 2 ^ (m - (round + 1)) + 2 ^ (m - R) = 2 ^ m
  | 0, _ => by simp
  | R + 1, hR => by
      have hdouble : 2 ^ (m - (R + 1)) + 2 ^ (m - (R + 1)) = 2 ^ (m - R) := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      rw [Finset.sum_range_succ, add_assoc, hdouble]
      exact sum_folded_sizes m R (by omega)

omit [DecidableEq F] [SampleableType F] in
/-- The folding errors of the unique-decoding regime sum to less than the initial domain's size
over the field size. -/
theorem sum_uniqueDecodingError_le {m R : ℕ} (hR : R ≤ m) :
    ∑ round ∈ Finset.range R, uniqueDecodingError F m round ≤
      (((2 ^ m : ℕ) / Fintype.card F : ℝ≥0) : ENNReal) := by
  simp only [uniqueDecodingError]
  rw [← ENNReal.ofNNReal_finsetSum]
  apply ENNReal.coe_le_coe.mpr
  rw [← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hsum : ∑ round ∈ Finset.range R, 2 ^ (m - (round + 1)) ≤ 2 ^ m :=
    (sum_folded_sizes m R hR) ▸ Nat.le_add_right _ _
  exact_mod_cast hsum

/-- Round-by-round soundness of `fri::LowDegree` in the unique-decoding regime, at the ideal
interpretation. For a coset of size `2^(n + 1)`, `R + 1` folds, final degree below `2^t` and
`s` queries, take any positive radius `θ` at most `(1 - ρ) / 2`, where `ρ = 2^(t + R + 1) /
2^(n + 1)` is the rate. Every adaptive and randomized prover makes the verifier accept with a
committed initial word at relative distance at least `δ` from the code with probability at most
`∑ r ≤ R, 2^(n - r) / |F| + (1 - min θ δ)^s`. -/
theorem soundness_uniqueDecoding (roots : ℕ → F) (t : ℕ) {n R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (θ : ℝ≥0) (hθ : 0 < θ)
    (hsize : degreeBound (R + 1) (2 ^ t) ≤ 2 ^ (n + 1))
    (hradius : θ ≤ ((1 : ℝ≥0) - (degreeBound (R + 1) (2 ^ t) : ℝ≥0) / (2 ^ (n + 1) : ℝ≥0)) / 2)
    (δ : ℝ) (prover : ProbComp ((Fin (2 ^ (n + 1)) → F) × Strategy F (n + 1) (R + 1))) :
    Pr{let result ← experiment roots t shift s prover}[
      result.2 = true ∧ Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D result.1).initial] ≤
      (∑ round ∈ Finset.range (R + 1), uniqueDecodingError F (n + 1) round) +
        ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s :=
  soundness roots t s D shift hD hcompat θ δ (uniqueDecodingError F (n + 1))
    (foldingProximity_uniqueDecoding t θ hθ D (R + 1) hsize hradius) prover

/-- The unique-decoding bound in closed form: the folding errors sum to less than the initial
coset's size over the field size, so acceptance with a far committed initial word has
probability at most `2^(n + 1) / |F| + (1 - min θ δ)^s`. -/
theorem soundness_uniqueDecoding_le (roots : ℕ → F) (t : ℕ) {n R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (θ : ℝ≥0) (hθ : 0 < θ)
    (hsize : degreeBound (R + 1) (2 ^ t) ≤ 2 ^ (n + 1))
    (hradius : θ ≤ ((1 : ℝ≥0) - (degreeBound (R + 1) (2 ^ t) : ℝ≥0) / (2 ^ (n + 1) : ℝ≥0)) / 2)
    (δ : ℝ) (prover : ProbComp ((Fin (2 ^ (n + 1)) → F) × Strategy F (n + 1) (R + 1))) :
    Pr{let result ← experiment roots t shift s prover}[
      result.2 = true ∧ Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D result.1).initial] ≤
      (((2 ^ (n + 1) : ℕ) / Fintype.card F : ℝ≥0) : ENNReal) +
        ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s := by
  have hfolds : R + 1 ≤ n + 1 := by
    rw [degreeBound_eq] at hsize
    have hpow : 2 ^ (R + 1) ≤ 2 ^ (n + 1) :=
      le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hsize
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hpow
  exact (soundness_uniqueDecoding roots t s D shift hD hcompat θ hθ hsize hradius δ prover).trans
    (add_le_add (sum_uniqueDecodingError_le hfolds) le_rfl)

end ZkcSecurity.ArkLib.Fri
