import ZkcArkLib.Sumcheck.OneRound.Security

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.OneRound.Kernel
open Zkc.Protocols.Sumcheck.ProductFamily.OneRound ZkcArkLib.Probability

open OracleSpec OracleComp ProtocolSpec ENNReal
open scoped BigOperators

/-- An explicit sampler interpreter, without a SampleableType instance. Its law
    may depend on the complete pre-challenge state in the outer experiment. -/
def kernelImpl {F D : Type} (draw : ProbComp D) :
    QueryImpl ([]ₒ + [(protocol F D).Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => match q with
  | .inl impossible => nomatch impossible
  | .inr q => (challengeEquiv q.1).symm <$> draw

def actualKernel {F D S : Type} [CommRing F] [DecidableEq F]
    (embed : D → F) (draw : ProbComp D) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F)
    (s : F) (st : S) : ProbComp (Option Unit) :=
  simulateQ (kernelImpl draw) ((Reduction.mk (prover choose) (verifier embed)).verdict s st).run

theorem kernel_transport {F D S : Type} [CommRing F] [DecidableEq F]
    (embed : D → F) (draw : ProbComp D) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F)
    (s : F) (st : S) :
    actualKernel embed draw choose s st = (do
      let d ← draw
      let msg := choose s st
      pure (verdict s msg.1 msg.2.1 msg.2.2 (embed d))) := by
  simp [actualKernel,Reduction.verdict,Reduction.run,prover_run,Verifier.run,
    actual_verifier,OptionT.run_bind,OptionT.run_monadLift,
    Option.elimM,Option.getM,
    ProtocolSpec.getChallenge]
  rw [← bind_pure_comp]
  congr 1
  · change simulateQ (kernelImpl draw)
      (liftComp ((protocol F D).getChallenge ⟨3,rfl⟩)
        ([]ₒ + [(protocol F D).Challenge]ₒ'challengeOracleInterface)) = _
    let sampler : QueryImpl ([(protocol F D).Challenge]ₒ'challengeOracleInterface) ProbComp :=
      fun q => (challengeEquiv q.1).symm <$> draw
    rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply (kernelImpl draw)
      sampler (fun _ => rfl)]
    have queryLaw := simulateQ_spec_query sampler ⟨⟨3,rfl⟩,()⟩
    exact queryLaw.trans (by change id <$> draw = draw; exact id_map draw)
  · funext d
    cases h : verdict s (choose s st).1 (choose s st).2.1 (choose s st).2.2 (embed d) <;> rfl

def experiment {F D S : Type} [CommRing F] [DecidableEq F]
    (embed : D → F) (coins : ProbComp S) (draw : S → ProbComp D)
    (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) : ProbComp (Option Unit) := do
  let st ← coins
  actualKernel embed (draw st) choose s st

/-- Conditional point-mass bounds suffice, even for a biased, state-dependent
    challenge law. Only reachable pre-draw states need the cap. This does not
    manufacture that premise for Fiat-Shamir or adversarial oracle histories. -/
theorem experiment_bound {F D S : Type} [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (coins : ProbComp S)
    (draw : S → ProbComp D) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F)
    (ε : ℝ≥0∞) (cap : ∀ st ∈ support coins, ∀ d, Pr[= d | draw st] ≤ ε)
    (hs : s ≠ 2) : Pr[= some () | experiment embed coins draw choose s] ≤ 2 * ε := by
  unfold experiment
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro st hst
  rw [kernel_transport,bind_pure_comp,probEvent_map]
  let msg := choose s st
  change Pr[(fun d => verdict s msg.1 msg.2.1 msg.2.2 (embed d) = some ()) | draw st] ≤ _
  refine (event_bound (draw st) _ ε (cap st hst)).trans ?_
  apply mul_le_mul_left
  exact_mod_cast accepting_card embed inj s msg.1 msg.2.1 msg.2.2 hs

-- A false claim itself may depend on pre-draw state. Both falsity and the
-- point-mass cap are required only on reachable states.
theorem adaptive_claim_bound {F D S : Type} [Field F] [DecidableEq F] [Fintype D]
    (embed : D → F) (inj : Function.Injective embed) (coins : ProbComp S)
    (draw : S → ProbComp D) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (claim : S → F)
    (ε : ℝ≥0∞) (cap : ∀ st ∈ support coins, ∀ d, Pr[= d | draw st] ≤ ε)
    (false_claim : ∀ st ∈ support coins, claim st ≠ 2) :
    Pr[= some () | (do
      let st ← coins
      ZkcArkLib.Sumcheck.OneRound.Kernel.actualKernel embed (draw st) choose (claim st) st)] ≤ 2 * ε := by
  rw [← probEvent_eq_eq_probOutput]
  apply probEvent_bind_le_of_forall_le
  intro st hst
  rw [ZkcArkLib.Sumcheck.OneRound.Kernel.kernel_transport,bind_pure_comp,probEvent_map]
  let msg := choose (claim st) st
  change Pr[(fun d => Zkc.Protocols.Sumcheck.ProductFamily.OneRound.verdict (claim st) msg.1 msg.2.1 msg.2.2 (embed d) = some ()) |
    draw st] ≤ _
  refine (ZkcArkLib.Probability.event_bound (draw st) _ ε (cap st hst)).trans ?_
  apply mul_le_mul_left
  exact_mod_cast Zkc.Protocols.Sumcheck.ProductFamily.OneRound.accepting_card embed inj (claim st) msg.1 msg.2.1 msg.2.2 (false_claim st hst)


end ZkcArkLib.Sumcheck.OneRound.Kernel
