import ZkcArkLib.Sumcheck.OneRound.Protocol
import Zkc.Protocols.AlgebraicRounds.Early

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.Sumcheck.OneRound
open Zkc.Protocols.Sumcheck.ProductFamily.OneRound

open OracleSpec OracleComp ProtocolSpec

/-- All coefficients are chosen from an arbitrary pre-draw private state and claim.
    No honest-message restriction. The only challenge occurs after all three sends. -/
def prover {F D S : Type} (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) :
    Prover []ₒ F S Unit Unit (protocol F D) where
  PrvState _ := Zkc.Protocols.AlgebraicRounds.Early.Message F
  input sw := choose sw.1 sw.2
  sendMessage i msg := by
    have h : i.val.val ≠ 3 := by
      have := i.property
      simpa [protocol] using this
    exact pure (by simpa [protocol,h] using
      (if i.val.val = 0 then msg.1 else if i.val.val = 1 then msg.2.1 else msg.2.2), msg)
  receiveChallenge _ msg := pure (fun _ => msg)
  output _ := pure ((),())

/-- This uses ArkLib's actual challengeQueryImpl and the empty shared oracle. -/
def freshImpl {F D : Type} [SampleableType D] :
    QueryImpl ([]ₒ + [(protocol F D).Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => match q with
  | .inl impossible => nomatch impossible
  | .inr q => challengeQueryImpl q

def actual {F D S : Type} [CommRing F] [DecidableEq F] [SampleableType D]
    (embed : D → F) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) (st : S) :
    ProbComp (Option Unit) :=
  simulateQ freshImpl ((Reduction.mk (prover choose) (verifier embed)).verdict s st).run

/-- Arbitrary coins/history are sampled BEFORE running the actual interaction. -/
def experiment {F D S : Type} [CommRing F] [DecidableEq F] [SampleableType D]
    (embed : D → F) (coins : ProbComp S) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) :
    ProbComp (Option Unit) := do
  let st ← coins
  actual embed choose s st

theorem prover_run {F D S : Type} (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) (st : S) :
    (prover (D := D) choose).run s st = (do
      let d ← (protocol F D).getChallenge ⟨3,rfl⟩
      let msg := choose s st
      pure (transcript msg.1 msg.2.1 msg.2.2 d,(),())) := by
  simp [Prover.run,Prover.runToRound,Prover.processRound,prover,protocol,
    Fin.induction,Fin.induction.go]
  congr 1
  funext d
  congr 2
  funext i
  fin_cases i <;> rfl

/-- Exact program transport proved by unfolding the actual ArkLib reduction. -/
theorem actual_eq {F D S : Type} [CommRing F] [DecidableEq F] [SampleableType D]
    (embed : D → F) (choose : F → S → Zkc.Protocols.AlgebraicRounds.Early.Message F) (s : F) (st : S) :
    actual embed choose s st = (do
      let d ← $ᵗ D
      let msg := choose s st
      pure (verdict s msg.1 msg.2.1 msg.2.2 (embed d))) := by
  simp [actual,Reduction.verdict,Reduction.run,prover_run,Verifier.run,
    actual_verifier,OptionT.run_bind,OptionT.run_monadLift,
    Option.elimM,Option.getM,
    ProtocolSpec.getChallenge]
  rw [← bind_pure_comp]
  congr 1
  · change simulateQ freshImpl
      (liftComp ((protocol F D).getChallenge ⟨3,rfl⟩)
        ([]ₒ + [(protocol F D).Challenge]ₒ'challengeOracleInterface)) = _
    rw [QueryImpl.simulateQ_liftComp_right_eq_of_apply freshImpl
      challengeQueryImpl (fun _ => rfl)]
    exact simulateQ_spec_query (challengeQueryImpl (pSpec := protocol F D)) ⟨⟨3,rfl⟩,()⟩
  · funext d
    cases h : verdict s (choose s st).1 (choose s st).2.1 (choose s st).2.2 (embed d) <;> rfl


end ZkcArkLib.Sumcheck.OneRound
