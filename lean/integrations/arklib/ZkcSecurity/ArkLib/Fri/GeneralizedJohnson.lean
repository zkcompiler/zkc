module

public import ZkcSecurity.ArkLib.Fri.Certificate
public import ArkLib.ProofSystem.Fri.ErrorBounds

@[expose] public section

/-! # `fri::LowDegree` up to the generalized Johnson radius of lines

This module discharges the folding obligations with the powers-generator bound of Bordage,
Chiesa, Guan and Manzur, *All Polynomial Generators Preserve Distance with Mutual Correlated
Agreement*, in ArkLib's form for one FRI folding round
(`foldingAgreementFailure_prob_le_generalizedJohnson`). For a binary fold the generator is the
line, and the bound holds at every radius `θ ≤ 1 - (1 - δmin + η)^(1/3)`, where `δmin` is the
relative minimum distance of the code after the fold and `η` is a positive slack below it.

The Reed–Solomon code of degree below `d` on `2^m` points has relative minimum distance
`(2^m - d + 1) / 2^m` (`relativeDistance`), more than `1 - ρ` for its rate `ρ`. Binary folding
keeps the rate, so the radius `1 - (ρ + η)^(1/3)` serves every round. As `η` tends to zero it
exceeds the unique-decoding radius `(1 - ρ) / 2` exactly when `ρ < ((√5 - 1) / 2)^3 ≈ 0.236`, so
at rates up to `1/8`.

Folding round `r` of a chain starting at log size `m` with `R` folds contributes
`johnsonError F t m R η r`: ArkLib's error for the code of degree below `2^(t + R - r - 1)` on
`2^(m - r - 1)` points (`lineError`).
-/

namespace ZkcSecurity.ArkLib.Fri

open Domain OracleComp
open scoped NNReal

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

/-- The relative minimum distance of the Reed–Solomon code of degree below `d` on `2^m` points. -/
noncomputable def relativeDistance (m d : ℕ) : ℝ≥0 :=
  ((2 ^ m - d + 1 : ℕ) : ℝ≥0) / 2 ^ m

/-- ArkLib's folding error for the line at slack `η`, after a fold onto `2^m` points whose code
has relative minimum distance `δmin`. With `r = 1 - δmin + η` it is
`2^m (1 - r^(1/2)) / (η |F|) + max (2 / (η (r^(1/3) - r^(1/2)) |F|)) (6 / (η |F|))`. -/
noncomputable def lineError (F : Type) [Fintype F] (m : ℕ) (δmin η : ℝ≥0) : ENNReal :=
  let g : ℕ := 2 ^ 1 - 1
  let r : ℝ := 1 - (δmin : ℝ) + (η : ℝ)
  ENNReal.ofReal
    (((2 ^ (m + 1 - 1) : ℝ) * (1 - r ^ ((1 : ℝ) / (g + 1)))) / η * ((g : ℝ) / Fintype.card F)
      + max
        (2 * (g : ℝ) /
          ((η : ℝ) * (r ^ ((1 : ℝ) / (g + 2)) - r ^ ((1 : ℝ) / (g + 1))) * Fintype.card F))
        (((g : ℝ) + 1) * ((g : ℝ) + 2) / ((η : ℝ) * Fintype.card F)))

/-- The folding error of round `round` for a chain starting at log size `m` with `R` folds and
final degree below `2^t`. -/
noncomputable def johnsonError (F : Type) [Fintype F] (t m R : ℕ) (η : ℝ≥0) (round : ℕ) :
    ENNReal :=
  lineError F (m - (round + 1))
    (relativeDistance (m - (round + 1)) (degreeBound (R - (round + 1)) (2 ^ t))) η

theorem relativeDistance_eq {m d : ℕ} (hd : d ≤ 2 ^ m) :
    (relativeDistance m d : ℝ) = 1 - (d : ℝ) / 2 ^ m + 1 / 2 ^ m := by
  have hpow : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [relativeDistance, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat,
    Nat.cast_add, Nat.cast_sub hd, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  field_simp

theorem degreeBound_succ_div_real (R d m : ℕ) :
    (degreeBound (R + 1) d : ℝ) / 2 ^ (m + 1) = (degreeBound R d : ℝ) / 2 ^ m := by
  rw [degreeBound]
  push_cast
  rw [pow_succ, mul_comm ((2 : ℝ) ^ m) 2, mul_div_mul_left _ _ two_ne_zero]

omit [Fintype F] [SampleableType F] in
/-- The relative minimum distance is the minimum distance of the code over its block length. -/
theorem relativeDistance_minDist {m d : ℕ} [NeZero d] (hd : d ≤ 2 ^ m)
    (D : SmoothCosetFftDomain (m + 1) F) :
    (relativeDistance m d : ℝ) =
      (Code.minDist (ReedSolomon.code (D.subdomain 1 : Fin (2 ^ (m + 1 - 1)) ↪ F) d :
        Set (Fin (2 ^ (m + 1 - 1)) → F)) : ℝ) / 2 ^ (m + 1 - 1) := by
  rw [ReedSolomon.minDist_of_le (by simpa using hd), Fintype.card_fin, Nat.add_sub_cancel,
    relativeDistance, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]

/-- Up to the generalized Johnson radius of lines, the folding obligations hold with
`johnsonError F t m R η`, for every positive slack `η` below `1 - ρ`. -/
theorem foldingEscapes_generalizedJohnson (t : ℕ) (θ η : ℝ≥0) (hη : 0 < η) :
    ∀ {m : ℕ} (D : SmoothCosetFftDomain m F) (R : ℕ),
      degreeBound R (2 ^ t) ≤ 2 ^ m →
      (η : ℝ) < 1 - (degreeBound R (2 ^ t) : ℝ) / 2 ^ m →
      (θ : ℝ) ≤ 1 - ((degreeBound R (2 ^ t) : ℝ) / 2 ^ m + η) ^ ((1 : ℝ) / 3) →
      FoldingEscapes t (θ : ℝ) D R (johnsonError F t m R η)
  | 0, _, _, _, _, _ => by simp [FoldingEscapes]
  | _ + 1, _, 0, _, _, _ => by simp [FoldingEscapes]
  | m + 1, D, R + 1, hsize, hslack, hradius => by
      have hsize' : degreeBound R (2 ^ t) ≤ 2 ^ m := by
        rw [degreeBound, pow_succ] at hsize
        omega
      rw [degreeBound_succ_div_real] at hslack hradius
      have hd : 0 < degreeBound R (2 ^ t) := degreeBound_pos (by positivity) R
      have : NeZero (degreeBound R (2 ^ t)) := ⟨hd.ne'⟩
      have hdist := relativeDistance_eq hsize'
      have hpow : (0 : ℝ) < 2 ^ m := by positivity
      have hlow : (1 : ℝ) / 2 ^ m ≤ (degreeBound R (2 ^ t) : ℝ) / 2 ^ m :=
        div_le_div_of_nonneg_right (by exact_mod_cast hd) hpow.le
      refine ⟨fun word => ?_, ?_⟩
      · have hθ : (θ : ℝ) ≤ 1 - (1 - (relativeDistance m (degreeBound R (2 ^ t)) : ℝ) + η) ^
            ((1 : ℝ) / (((2 ^ 1 - 1 : ℕ) : ℝ) + 2)) := by
          have exponent : (1 : ℝ) / (((2 ^ 1 - 1 : ℕ) : ℝ) + 2) = 1 / 3 := by norm_num
          rw [exponent]
          refine hradius.trans (sub_le_sub_left (Real.rpow_le_rpow ?_ ?_ (by norm_num)) 1)
          · rw [hdist]
            linarith [η.coe_nonneg]
          · rw [hdist]
            linarith [one_div_nonneg.mpr hpow.le]
        have hηmin : η < relativeDistance m (degreeBound R (2 ^ t)) := by
          rw [← NNReal.coe_lt_coe, hdist]
          linarith [one_div_nonneg.mpr hpow.le]
        have bound := _root_.Fri.foldingAgreementFailure_prob_le_generalizedJohnson (k := 1) D
          word hd (relativeDistance m (degreeBound R (2 ^ t))) η θ one_pos
          (by rw [pow_one]; exact Fintype.one_lt_card)
          (relativeDistance_minDist hsize' D) hη hηmin hθ
        have error : johnsonError F t (m + 1) (R + 1) η 0 =
            lineError F m (relativeDistance m (degreeBound R (2 ^ t))) η := by
          simp [johnsonError]
        rw [error]
        exact bound
      · have herror : (fun round => johnsonError F t (m + 1) (R + 1) η (round + 1)) =
            johnsonError F t m R η := by
          funext round
          simp only [johnsonError]
          rw [show m + 1 - (round + 1 + 1) = m - (round + 1) by omega,
            show R + 1 - (round + 1 + 1) = R - (round + 1) by omega]
        rw [herror]
        exact foldingEscapes_generalizedJohnson t θ η hη (D.subdomain 1) R hsize' hslack hradius

/-- Round-by-round soundness up to the generalized Johnson radius of lines. -/
theorem soundness_generalizedJohnson (roots : ℕ → F) (t : ℕ) {n R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (θ η : ℝ≥0) (hη : 0 < η)
    (hsize : degreeBound (R + 1) (2 ^ t) ≤ 2 ^ (n + 1))
    (hslack : (η : ℝ) < 1 - (degreeBound (R + 1) (2 ^ t) : ℝ) / 2 ^ (n + 1))
    (hradius : (θ : ℝ) ≤
      1 - ((degreeBound (R + 1) (2 ^ t) : ℝ) / 2 ^ (n + 1) + η) ^ ((1 : ℝ) / 3))
    (δ : ℝ) (prover : ProbComp ((Fin (2 ^ (n + 1)) → F) × Strategy F (n + 1) (R + 1))) :
    Pr{let result ← experiment roots t shift s prover}[
      result.2 = true ∧ Far D (degreeBound (R + 1) (2 ^ t)) δ (toTrace t D result.1).initial] ≤
      (∑ round ∈ Finset.range (R + 1), johnsonError F t (n + 1) (R + 1) η round) +
        ENNReal.ofReal (1 - min (θ : ℝ) δ) ^ s :=
  RoundByRound.soundness
    { fold := foldingEscapes_generalizedJohnson t θ η hη D (R + 1) hsize hslack hradius
      query := fun layers hsafe hfar =>
        query_escape_le roots t s D shift hD hcompat θ δ layers hsafe hfar }
    prover

/-- Up to the generalized Johnson radius of lines, the verifier after a far initial word is a
doomed residual with the folding errors `johnsonError`. -/
theorem afterCommit_doomed_generalizedJohnson (roots : ℕ → F) (t : ℕ) (shift : F) (s : ℕ)
    {N K : ℕ} (D : SmoothCosetFftDomain (N + 1) F) (θ η : ℝ≥0) (hη : 0 < η)
    (hsize : degreeBound (K + 1) (2 ^ t) ≤ 2 ^ (N + 1))
    (hslack : (η : ℝ) < 1 - (degreeBound (K + 1) (2 ^ t) : ℝ) / 2 ^ (N + 1))
    (hradius : (θ : ℝ) ≤
      1 - ((degreeBound (K + 1) (2 ^ t) : ℝ) / 2 ^ (N + 1) + η) ^ ((1 : ℝ) / 3))
    (δ : ℝ) (word : Fin (2 ^ (N + 1)) → F) (far : Far D (degreeBound (K + 1) (2 ^ t)) δ word) :
    Doomed (R₀ := K + 1) roots t shift s D θ δ (johnsonError F t (N + 1) (K + 1) η)
      (afterCommit (R := K) roots t shift s word) :=
  afterCommit_doomed D θ δ _
    (foldingEscapes_generalizedJohnson t θ η hη D (K + 1) hsize hslack hradius) word far

end ZkcSecurity.ArkLib.Fri
