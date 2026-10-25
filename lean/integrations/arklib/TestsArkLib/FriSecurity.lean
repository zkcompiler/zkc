import ZkcArkLib.Fri.Completeness
import ZkcArkLib.Fri.GeneralizedJohnson

/-! Controls for the completeness and round-by-round soundness of `fri::LowDegree` at the ideal
interpretation.

* The library verifier is consistent with honest folding: honestly folded layers are accepted at
  every query position (`honest_folding_accepted`). The soundness bound is therefore not obtained
  from a verifier that rejects everything.
* `examples/projects/fri` and the authored STARK tables run `LowDegree<_, 5, 0, 3, 8>`: a 32-point
  coset, a constant final polynomial, three folds and eight queries, at rate `1/4`. On the coset of
  any primitive 32nd root of unity and nonzero shift:
  * the honest prover is accepted at every query position on every codeword of degree below 8
    (`codeword_accepted`);
  * the unique-decoding premises hold at the radius `3/8`, and every prover is accepted with a
    committed initial word at relative distance at least `δ` from the degree-below-8 code with
    probability at most `(16 + 8 + 4) / |F| + (1 - min (3/8) δ)^8` (`example_bound`);
  * the verifier after such a committed word is a doomed residual of the certificate over
    verifier residuals, with the unique-decoding folding errors (`doomed_after_commit`).
* At rate `1/8` (a 64-point coset, three folds to a constant final polynomial and eight queries),
  the generalized Johnson instance holds at the radius `12/25` with slack `1/100`, beyond the
  unique-decoding radius `7/16`, with no remaining premise (`lowRate_bound`). -/

namespace TestsSecurity.FriSecurity

open OracleComp
open ZkcSecurity.ArkLib.Fri
open scoped NNReal ENNReal

variable {F : Type} [Field F] [DecidableEq F]

/-- Honestly folded layers pass every query of the library verifier. -/
theorem honest_folding_accepted (roots : ℕ → F) (t : ℕ) {n R s : ℕ}
    (D : Domain.SmoothCosetFftDomain (n + 1) F) (shift : F)
    (hD : ∀ i : Fin (2 ^ (n + 1)), D i = point roots shift (n + 1) i)
    (hcompat : Compatible roots (n + 1) (R + 1)) (layers : Layers F (n + 1) (R + 1))
    (hhonest : Honest t D layers) (hbound : bounded t layers.coefficients = true)
    (positions : Fin s → Fin (2 ^ (n + 1))) :
    verify roots t shift layers positions = true :=
  verify_of_honest roots t D shift hD hcompat layers hhonest hbound positions

variable [Fintype F] [SampleableType F]

/-- The soundness bound of the parameters of `examples/projects/fri`, on the natural-order coset
of a primitive 32nd root `ω` with shift `shift`, using the installed root convention
`m ↦ ω ^ 2 ^ (5 - m)`. -/
theorem example_bound (ω shift : F) (hω : IsPrimitiveRoot ω (2 ^ 5)) (hshift : shift ≠ 0)
    (δ : ℝ) (prover : ProbComp ((Fin (2 ^ 5) → F) × Strategy F 5 3)) :
    Pr{let result ← experiment (fun m => ω ^ 2 ^ (5 - m)) 0 shift 8 prover}[
      result.2 = true ∧
        Far (cosetDomain shift ω hshift hω) 8 δ
          (toTrace 0 (cosetDomain shift ω hshift hω) result.1).initial] ≤
      (((28 : ℝ≥0) / Fintype.card F : ℝ≥0) : ℝ≥0∞) + ENNReal.ofReal (1 - min (3 / 8) δ) ^ 8 := by
  have hroot : IsPrimitiveRoot ((fun m => ω ^ 2 ^ (5 - m)) 5) (2 ^ 5) := by simpa using hω
  have h := soundness_uniqueDecoding (fun m => ω ^ 2 ^ (5 - m)) 0 (n := 4) (R := 2) 8
    (cosetDomain shift ω hshift hω) shift
    (fun i => by rw [cosetDomain_apply]; simp [point]) (compatible_powers ω 5 3) (3 / 8)
    (by norm_num) (by decide)
    (by
      norm_num [degreeBound]
      rw [show (1 : ℝ≥0) - 1 / 4 = 3 / 4 from tsub_eq_of_eq_add (by norm_num)]
      norm_num) δ prover
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, uniqueDecodingError, zero_add]
  rw [← ENNReal.coe_add, ← ENNReal.coe_add, ← add_div, ← add_div]
  norm_num

omit [Fintype F] in
/-- Every codeword of degree below 8 on the 32-point coset passes every query of the library
verifier, after every run of the honest prover. -/
theorem codeword_accepted (ω shift : F) (hω : IsPrimitiveRoot ω (2 ^ 5)) (hshift : shift ≠ 0)
    (word : Fin (2 ^ 5) → F)
    (codeword : word ∈ ReedSolomon.code (cosetDomain shift ω hshift hω : Fin (2 ^ 5) ↪ F) 8)
    (layers : Layers F 5 3)
    (member : layers ∈ support
      (commit (honest (R := 2) 0 (by omega) (cosetDomain shift ω hshift hω) word) word))
    (positions : Fin 8 → Fin (2 ^ 5)) :
    verify (fun m => ω ^ 2 ^ (5 - m)) 0 shift layers positions = true :=
  ZkcSecurity.ArkLib.Fri.honest_accepted (fun m => ω ^ 2 ^ (5 - m)) 0 (n := 4) (R := 2)
    (by omega) (cosetDomain shift ω hshift hω) shift
    (fun i => by rw [cosetDomain_apply]; simp [point]) (compatible_powers ω 5 3) word codeword
    layers member positions

/-- At the same parameters, the verifier after a committed initial word at relative distance at
least `δ` from the degree-below-8 code is doomed, with the unique-decoding folding errors and no
remaining premise. -/
theorem doomed_after_commit (ω shift : F) (hω : IsPrimitiveRoot ω (2 ^ 5)) (hshift : shift ≠ 0)
    (δ : ℝ) (word : Fin (2 ^ 5) → F) (far : Far (cosetDomain shift ω hshift hω) 8 δ word) :
    Doomed (R₀ := 3) (fun m => ω ^ 2 ^ (5 - m)) 0 shift 8 (cosetDomain shift ω hshift hω)
      ((3 / 8 : ℝ≥0) : ℝ) δ (uniqueDecodingError F 5)
      (afterCommit (R := 2) (fun m => ω ^ 2 ^ (5 - m)) 0 shift 8 word) :=
  afterCommit_doomed_uniqueDecoding (N := 4) (K := 2) (cosetDomain shift ω hshift hω) (3 / 8)
    (by norm_num) (by decide)
    (by
      norm_num [degreeBound]
      rw [show (1 : ℝ≥0) - 1 / 4 = 3 / 4 from tsub_eq_of_eq_add (by norm_num)]
      norm_num) δ word far

/-- At rate `1/8`, the radius `12/25` lies within the generalized Johnson radius of lines at slack
`1/100`: `(1/8 + 1/100)^(1/3) ≤ 13/25`. -/
theorem lowRate_bound (ω shift : F) (hω : IsPrimitiveRoot ω (2 ^ 6)) (hshift : shift ≠ 0)
    (δ : ℝ) (prover : ProbComp ((Fin (2 ^ 6) → F) × Strategy F 6 3)) :
    Pr{let result ← experiment (fun m => ω ^ 2 ^ (6 - m)) 0 shift 8 prover}[
      result.2 = true ∧
        Far (cosetDomain shift ω hshift hω) 8 δ
          (toTrace 0 (cosetDomain shift ω hshift hω) result.1).initial] ≤
      (∑ round ∈ Finset.range 3, johnsonError F 0 6 3 (1 / 100) round) +
        ENNReal.ofReal (1 - min ((12 / 25 : ℝ≥0) : ℝ) δ) ^ 8 := by
  have cube : (27 / 200 : ℝ) ^ ((1 : ℝ) / 3) ≤ 13 / 25 := by
    have root : ((13 / 25 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) = 13 / 25 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    calc (27 / 200 : ℝ) ^ ((1 : ℝ) / 3) ≤ ((13 / 25 : ℝ) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 13 / 25 := root
  exact soundness_generalizedJohnson (fun m => ω ^ 2 ^ (6 - m)) 0 (n := 5) (R := 2) 8
    (cosetDomain shift ω hshift hω) shift
    (fun i => by rw [cosetDomain_apply]; simp [point]) (compatible_powers ω 6 3) (12 / 25)
    (1 / 100) (by norm_num) (by decide) (by norm_num [degreeBound])
    (by
      have rate : (degreeBound (2 + 1) (2 ^ 0) : ℝ) / 2 ^ (5 + 1) + ((1 / 100 : ℝ≥0) : ℝ) =
          27 / 200 := by
        norm_num [degreeBound]
      have radius : ((12 / 25 : ℝ≥0) : ℝ) = 12 / 25 := by norm_num
      rw [rate, radius]
      linarith [cube]) δ prover

end TestsSecurity.FriSecurity
