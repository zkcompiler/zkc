module

public import ZkcFormal.Written.PortSamplers
public import ZkcFormal.ChargedProbability

@[expose] public section

/-! The fee of a draw of a position: the probability of one position is at most one over the
positions, as a fee. -/

namespace ZkcFormal.Written
open Zkc.Core ProbabilisticProcess OracleComp ProbComp
open scoped NNRat ENNReal

/-- A drawn position is a given one with probability at most one over the positions. -/
theorem prEvent_drawPosition_eq_le (n position : ℕ) :
    Pr{let v ← drawPosition n}[v = position] ≤
      toProbability (((1 : ℕ) : ℚ≥0) / ((n + 1 : ℕ) : ℚ≥0)) := by
  rw [prEvent_drawPosition, toProbability_natCast_div 1 (n + 1) (Nat.succ_pos n)]
  have few : (Finset.univ.filter fun i : Fin (n + 1) => (i : ℕ) = position).card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb =>
      Fin.ext ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
  push_cast
  exact ENNReal.div_le_div_right (by exact_mod_cast few) _

end ZkcFormal.Written
