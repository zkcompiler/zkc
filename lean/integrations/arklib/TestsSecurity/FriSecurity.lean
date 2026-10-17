import ZkcSecurity.ArkLib.Fri.UniqueDecoding

/-! Controls for the round-by-round soundness of `fri::LowDegree` at the ideal interpretation.

* The library verifier is consistent with honest folding: honestly folded layers are accepted at
  every query position (`honest_accepted`). The soundness bound is therefore not obtained from a
  verifier that rejects everything.
* `examples/projects/fri` and the authored STARK tables run `LowDegree<_, 5, 0, 3, 8>`: a 32-point
  coset, a constant final polynomial, three folds and eight queries, at rate `1/4`. On the coset of
  any primitive 32nd root of unity and nonzero shift, the unique-decoding premises hold at the
  radius `3/8`, and every prover is accepted with a committed initial word at relative distance
  at least `δ` from the degree-below-8 code with probability at most
  `(16 + 8 + 4) / |F| + (1 - min (3/8) δ)^8` (`example_bound`). -/

namespace TestsSecurity.FriSecurity

open OracleComp
open ZkcSecurity.ArkLib.Fri
open scoped NNReal ENNReal

variable {F : Type} [Field F] [DecidableEq F]

/-- Honestly folded layers pass every query of the library verifier. -/
theorem honest_accepted (roots : ℕ → F) (t : ℕ) {n R s : ℕ}
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

end TestsSecurity.FriSecurity
