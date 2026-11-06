module

public import ZkcArkLib.Fri.PhasesSoundness

/-! # Feasible unique-decoding parameters for the source profile

The source retains at least one rate bit: `t + R + 1 ≤ n`. Consequently the
initial rate is at most one half, and radius one quarter is always feasible.
Terminal log zero is admitted. No Johnson-radius improvement is needed here.
The proximity construction is the existing pinned ArkLib/BCIKS20 unique-decoding
construction in `Fri.UniqueDecoding`; this module only discharges its premises.
-/

@[expose] public section

set_option autoImplicit false

namespace ZkcSecurity.ArkLib.Fri.Phases

open Domain OracleComp
open scoped NNReal

theorem source_degree_feasible {n t R : ℕ} (retained : t + R + 1 ≤ n) :
    degreeBound R (2 ^ t) ≤ 2 ^ n ∧
      (degreeBound R (2 ^ t) : ℝ≥0) / (2 ^ n : ℝ≥0) ≤ 1 / 2 := by
  have double : degreeBound R (2 ^ t) * 2 ≤ 2 ^ n := by
    have power := Nat.pow_le_pow_right (by decide : 0 < 2) retained
    simpa only [degreeBound_eq, pow_add, pow_one, mul_assoc, mul_comm, mul_left_comm] using power
  constructor
  · omega
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    simp only [one_mul]
    exact_mod_cast double

theorem source_radius_feasible {n t R : ℕ} (retained : t + R + 1 ≤ n) :
    (1 / 4 : ℝ≥0) ≤
      ((1 : ℝ≥0) - (degreeBound R (2 ^ t) : ℝ≥0) / (2 ^ n : ℝ≥0)) / 2 := by
  have remaining := tsub_le_tsub_left (source_degree_feasible retained).2 (1 : ℝ≥0)
  have half : (1 / 2 : ℝ≥0) ≤
      1 - (degreeBound R (2 ^ t) : ℝ≥0) / (2 ^ n : ℝ≥0) := by
    calc (1 / 2 : ℝ≥0) = 1 - 1 / 2 := by
           apply NNReal.coe_injective
           norm_num [NNReal.coe_sub (by norm_num : (1 / 2 : ℝ≥0) ≤ 1)]
         _ ≤ _ := remaining
  exact (by norm_num : (1 / 4 : ℝ≥0) = (1 / 2) / 2).le.trans
    (div_le_div_of_nonneg_right half (by positivity))

variable {F S E : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

/-- A constructed, feasible `FoldingEscapes`, rather than an unexplained security law. -/
theorem foldingEscapes_uniqueDecoding {n t R : ℕ}
    (D : SmoothCosetFftDomain n F) (retained : t + R + 1 ≤ n) :
    FoldingEscapes t (1 / 4 : ℝ≥0) D R (uniqueDecodingError F n) :=
  foldingEscapes_of_proximity t _ D R _
    (foldingProximity_uniqueDecoding t (1 / 4) (by norm_num) D R
      (source_degree_feasible retained).1 (source_radius_feasible retained))

/-- Causal, abort-preserving ideal soundness with the source's admitted rate profile. -/
theorem soundness_uniqueDecoding (roots : ℕ → F) (t : ℕ) {m R : ℕ} (s : ℕ)
    (D : SmoothCosetFftDomain (m + 1) F) (shift : F)
    (geometry : ∀ i : Fin (2 ^ (m + 1)), D i = point roots shift (m + 1) i)
    (compatible : Compatible roots (m + 1) (R + 1))
    (retained : t + (R + 1) + 1 ≤ m + 1) (δ : ℝ)
    (policy : QueryPolicy) (prover : CausalProver F S (SamplingEvent (m + 1) E))
    (queriesProver : QueryProver (m + 1) S E)
    (reader : PIR.MonadHandler ProbComp checkOperations S (SamplingEvent (m + 1) E))
    (state : S) :
    Pr{let result ← experiment roots t m R s shift policy prover queriesProver reader state}[
      returned (fun output ↦ output.2.accepted = true ∧
        Far D (degreeBound (R + 1) (2 ^ t)) δ output.1) result] ≤
      (∑ r ∈ Finset.range (R + 1), uniqueDecodingError F (m + 1) r) +
        ENNReal.ofReal (1 - min (1 / 4 : ℝ) δ) ^ s := by
  simpa using soundness roots t s D shift geometry compatible (1 / 4 : ℝ≥0) δ
    (uniqueDecodingError F (m + 1)) (foldingEscapes_uniqueDecoding D retained)
    policy prover queriesProver reader state

/-- Both complete source snapshots have this legal terminal-log-zero size profile. -/
theorem snapshot_terminal_zero_feasible :
    degreeBound 3 (2 ^ 0) ≤ 2 ^ 5 ∧
      (1 / 4 : ℝ≥0) ≤ ((1 : ℝ≥0) - (degreeBound 3 (2 ^ 0) : ℝ≥0) / 2 ^ 5) / 2 :=
  ⟨(source_degree_feasible (n := 5) (t := 0) (R := 3) (by decide)).1,
    source_radius_feasible (by decide)⟩

end ZkcSecurity.ArkLib.Fri.Phases
