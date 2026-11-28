module

public import ZkcFormal.Samplers
public import ZkcFormal.ChargedJudgment

@[expose] public section

/-!
The fees of samplers: the policies of the judgment with fees that proofs use.

A budget of fees is a nonnegative rational; `toProbability` reads it as a probability. Under
the fees of samplers (`paysBy`) some effects have a sampler, and there a fee pays for a set of
replies of at most that probability under the sampler; within allowances (`paysWithin`), each
fee is also at most what its effect is allowed. Nothing here bounds a probability of a run:
that a judgment under these policies bounds the value of a process, and so the probability of
a bad return, is in `ZkcFormal.ChargedReturn`.
-/

namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core OracleComp
open scoped NNRat NNReal ENNReal

/-- A budget of fees, as a probability. -/
noncomputable def toProbability (budget : ℚ≥0) : ℝ≥0∞ := ((budget : ℝ≥0) : ℝ≥0∞)

theorem toProbability_add (a b : ℚ≥0) : toProbability (a + b) = toProbability a + toProbability b := by
  simp [toProbability]

theorem toProbability_le_iff {a b : ℚ≥0} : toProbability a ≤ toProbability b ↔ a ≤ b := by
  unfold toProbability
  exact_mod_cast Iff.rfl

theorem toProbability_mono {a b : ℚ≥0} (le : a ≤ b) : toProbability a ≤ toProbability b :=
  toProbability_le_iff.mpr le

/-- A count over a positive count, as a probability. -/
theorem toProbability_natCast_div (count total : ℕ) (positive : 0 < total) :
    toProbability ((count : ℚ≥0) / total) = (count : ℝ≥0∞) / total := by
  have nonzero : ((total : ℝ≥0)) ≠ 0 := by exact_mod_cast positive.ne'
  simp [toProbability, ENNReal.coe_div nonzero]

variable {S : Sig} {σ H A : Type}

/-! ## The fees of samplers -/

/-- The fees of samplers. The zero fee excludes nothing, at every effect. At an effect with a
sampler, a fee pays for a set of replies whose toProbability under the sampler is at most the fee.
The set is chosen before the reply, from what the process has seen so far. -/
def paysBy (samplers : Samplers S) : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop :=
  fun op fee excluded => (fee = 0 ∧ ∀ v, ¬ excluded v) ∨
    ∃ draw, samplers op = some draw ∧ Pr{let v ← draw}[excluded v] ≤ toProbability fee

/-! ## Fees within what each effect is allowed -/

/-- The fees of samplers within allowances: a fee that the sampler of the effect pays for, and
that is at most what the effect is allowed. A bound that is judged under this policy is paid
effect by effect within the allowances, and not only in total: a fee cannot be moved from the
effect that a source charges to another. -/
def paysWithin (samplers : Samplers S) (allowance : S.Op → ℚ≥0) :
    (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop :=
  fun op fee excluded => paysBy samplers op fee excluded ∧ fee ≤ allowance op

end ZkcFormal.ProbabilisticProcess
