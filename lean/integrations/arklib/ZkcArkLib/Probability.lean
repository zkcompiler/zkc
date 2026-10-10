import VCVio.OracleComp.Constructions.SampleableType
import Zkc.Probability.Concentration

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Probability
open OracleComp ENNReal
/-- Retain the entire pre-draw state, not only a public marginal. -/
def freshJoint {S D : Type} [SampleableType D] (coins : ProbComp S) : ProbComp (S × D) := do
  let st ← coins
  let d ← $ᵗ D
  pure (st,d)

/-- Kernel-level conditional freshness: at every pre-draw state, the joint mass
    factors. For positive state mass this gives conditional mass 1/card D. -/
theorem fresh_joint_mass {S D : Type} [SampleableType D] [Fintype D]
    (coins : ProbComp S) (st : S) (d : D) :
    Pr[= (st,d) | freshJoint coins] = Pr[= st | coins] * (Fintype.card D : ℝ≥0∞)⁻¹ := by
  simp [freshJoint]

/-- Finite anti-concentration, not an independence or uniformity theorem. -/
theorem event_bound {D : Type} [Fintype D] (draw : ProbComp D)
    (event : D → Prop) [DecidablePred event] (ε : ℝ≥0∞) (cap : ∀ d, Pr[= d | draw] ≤ ε) :
    Pr[event | draw] ≤ ((Finset.univ.filter event).card : ℝ≥0∞) * ε := by
  rw [probEvent_eq_sum_filter_univ]
  exact Zkc.Probability.finite_event_bound (fun d => Pr[= d | draw]) event ε cap

-- ProbComp has only total pure/uniform-query constructors. It cannot silently
-- supply an empty challenge type, even for the custom sampler interface.
theorem sampler_nonempty {D : Type} (draw : ProbComp D) : Nonempty D := by
  induction draw using ProbComp.inductionOn with
  | pure d => exact ⟨d⟩
  | query_bind n mx ih => exact ih 0

theorem sampler_card_positive {D : Type} [Fintype D] (draw : ProbComp D) :
    0 < Fintype.card D := by
  let := sampler_nonempty draw
  exact Fintype.card_pos


end ZkcArkLib.Probability
