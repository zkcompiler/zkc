import ZkcArkLib.Sumcheck.OneRound.Prover
import ZkcArkLib.Sumcheck.OneRound.Probability

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.OneRound
open Zkc.Protocols.Sumcheck.ProductFamily.OneRound ZkcArkLib.Probability OracleComp ENNReal
/-- Actual ArkLib acceptance probability, not an assumed equality of abstract games. -/
theorem actual_bound {F D S : Type} [Field F] [DecidableEq F]
    [SampleableType D] [Fintype D] (embed : D → F) (inj : Function.Injective embed)
    (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) (st : S) (hs : s ≠ 2) :
    Pr[= some () | actual embed choose s st] ≤ (2 : ℝ≥0∞) / Fintype.card D := by
  rw [actual_eq]
  exact fresh_bound embed inj s _ _ _ hs

/-- Arbitrary pre-draw coins/state and arbitrary coefficient choice retain the bound. -/
theorem experiment_bound {F D S : Type} [Field F] [DecidableEq F]
    [SampleableType D] [Fintype D] (embed : D → F) (inj : Function.Injective embed)
    (coins : ProbComp S) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) (hs : s ≠ 2) :
    Pr[= some () | experiment embed coins choose s] ≤ (2 : ℝ≥0∞) / Fintype.card D := by
  unfold experiment
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro st _
  rw [probEvent_eq_eq_probOutput]
  exact actual_bound embed inj choose s st hs

/-- The actual experiment is the fresh joint law pushed through the ZkcArkLib.Sumcheck.Scalar checker. -/
theorem experiment_transport {F D S : Type} [CommRing F] [DecidableEq F]
    [SampleableType D] (embed : D → F) (coins : ProbComp S)
    (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) :
    experiment embed coins choose s =
      (fun sd => let msg := choose s sd.1
        ZkcArkLib.Sumcheck.Scalar.accept 0 Zkc.Protocols.AlgebraicRounds.Scalar.value s (interpret embed (transcript msg.1 msg.2.1 msg.2.2 sd.2)))
        <$> (freshJoint (D := D) coins) := by
  simp [experiment,actual_eq,freshJoint,interpret_transcript,consumer_formula]


end ZkcArkLib.Sumcheck.OneRound
