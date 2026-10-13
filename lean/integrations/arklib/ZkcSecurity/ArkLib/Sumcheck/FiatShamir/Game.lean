module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Replay
public import Zkc.Specification

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Quantitative soundness in ArkLib's actual cached restoration experiment.
The adversary selects the entire public statement, messages, and salts adaptively.
Its all-branch query budget includes offline work; two further accesses complete
the selected proof in the same cache. This is a canonical oracle model, not a
claim about an arbitrary native transcript provider or Merlin/STROBE.
-/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir

open Interaction.Oracle Interaction.Oracle.Security
open Interaction.Oracle.Security.StateRestoration
open OracleComp OracleSpec
open Zkc.Protocols.Sumcheck.Common

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]
variable {Salt : Type} [DecidableEq Salt]

abbrev RestorationOracle (F Salt : Type) [Field F] [DecidableEq F] [Fintype F]
    [SampleableType F] := oracleSpec (Statement F) Salt (rounds (F := F) 2)

/-- Unit is the public-polynomial soundness witness; no secret relation is assumed. -/
abbrev Adversary (F Salt : Type) [Field F] [DecidableEq F] [Fintype F]
    [SampleableType F] :=
  OracleComp (RestorationOracle F Salt) (Statement F × Messages Salt (rounds (F := F) 2) × Unit)

/-- Execute the native ArkLib strategies after cached transcript completion. -/
def nativeGame (adversary : Adversary F Salt) :=
  verificationGame initial inputImpl Out terminal adversary

/-- The actual native cached game rejects false statements except with the
all-prefix restoration error. No local security or execution law is assumed. -/
theorem soundness (adversary : Adversary F Salt) (Q : Nat)
    (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (nativeGame adversary)).run' ∅}[
      result.2.2.1 = true ∧ result.1.claim ≠ (polynomial result.1.coefficients).booleanSum] ≤
        (Q + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  have bound := stateRestoration_knowledge_soundness inputState statementExtractor Set.univ
    (2 / (Fintype.card F : ENNReal))
    (fun z _ => prover_preserving 2 True (polynomial z.coefficients) z.claim)
    (fun z _ => locally_bounded 2 True (polynomial z.coefficients) z.claim)
    initial inputImpl Out terminal
    (fun z _ => z.claim = (polynomial z.coefficients).booleanSum)
    (fun _ _ output (_ : Unit) => output = true)
    terminalWitness (fun _ _ => by exact and_iff_right True.intro) outputLaw
    adversary Q queryBound
  simpa only [nativeGame, Set.mem_univ, true_and, rounds_length, Nat.cast_ofNat] using bound

/-- The actual common PIR verifier on the completed logical transcript.
The returned execution still records its own early-stop state and event prefix. -/
def replayProgram (program : Verifier F) (service : Nat) (z : Statement F)
    (p : (tree (F := F)).ExecutionPath) :=
  run program z.coefficients z.claim service ⟨p.1, fun _ => p.2.2.1⟩ p.2.1 p.2.2.2.1

/-- Complete the adversary's proof in the cached oracle, then run the contracted
PIR verifier with those messages/challenges, retaining its execution record. -/
def programGame (program : Verifier F) (service : Nat) (adversary : Adversary F Salt) :=
  (fun result => (result.1, replayProgram program service result.1 result.2.1)) <$>
    restoredExecution (rounds (F := F) 2) adversary

/-- Reusable consumer of the existing imported-program contract. This projects
only acceptance; it does not identify PIR early-stop traces with completed replay. -/
theorem program_soundness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (service : Nat)
    (adversary : Adversary F Salt) (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (programGame program service adversary)).run' ∅}[
      result.2.outcome = PIR.Outcome.returned (some true) ∧
        result.1.claim ≠ (polynomial result.1.coefficients).booleanSum] ≤
          (Q + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  have bound := soundness adversary Q queryBound
  rw [nativeGame, verificationGame_eq, simulateQ_map] at bound
  simp only [StateT.run'_map', prEvent_map] at bound
  rw [programGame, simulateQ_map]
  simp only [StateT.run'_map', prEvent_map]
  apply le_trans (le_of_eq ?_) bound
  apply prEvent_congr
  rintro ⟨z, p, witness⟩
  rcases p with ⟨firstMessage, first, secondMessage, second, finish⟩
  cases finish
  exact and_congr (actualVerifier_accepts_iff certificate z service
    firstMessage first secondMessage second) Iff.rfl

omit [DecidableEq Salt] in
/-- The final-completion budget is charged even for unqueried or rejected proofs. -/
theorem completion_queryBound (z : Statement F) (messages : Messages Salt (rounds (F := F) 2)) :
    IsTotalQueryBound (complete (rounds (F := F) 2) z messages) 2 :=
  complete_queryBound _ z messages

omit [DecidableEq Salt] in
theorem total_queryBound (adversary : Adversary F Salt) (Q : Nat)
    (queryBound : IsTotalQueryBound adversary Q) :
    IsTotalQueryBound (restoredExecution (rounds (F := F) 2) adversary) (Q + 2) :=
  restoredExecution_queryBound _ adversary Q queryBound

/-- Independent private coins may select a family of adaptive oracle programs.
Each branch has the same all-branch query bound. -/
theorem randomized_program_soundness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring program) (service : Nat) {Coins : Type}
    (coins : ProbComp Coins) (adversary : Coins → Adversary F Salt) (Q : Nat)
    (queryBound : ∀ coin, IsTotalQueryBound (adversary coin) Q) :
    Pr{let result ← (coins >>= fun coin =>
      (simulateQ randomOracle (programGame program service (adversary coin))).run' ∅)}[
      result.2.outcome = PIR.Outcome.returned (some true) ∧
        result.1.claim ≠ (polynomial result.1.coefficients).booleanSum] ≤
          (Q + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal)) :=
  prEvent_bind_le_of_forall_le coins _ _
    (fun coin => program_soundness certificate service (adversary coin) Q (queryBound coin))

noncomputable def soundnessProperty (service : Nat) (adversary : Adversary F Salt)
    (Q : Nat) : Zkc.Verification.Property (Verifier F) where
  assumptions _ := IsTotalQueryBound adversary Q
  conclusion program :=
    Pr{let result ← (simulateQ randomOracle (programGame program service adversary)).run' ∅}[
      result.2.outcome = PIR.Outcome.returned (some true) ∧
        result.1.claim ≠ (polynomial result.1.coefficients).booleanSum] ≤
          (Q + 2 : ENNReal) * (2 / (Fintype.card F : ENNReal))

theorem soundnessConsumer (wiring : Wiring) (service : Nat) (adversary : Adversary F Salt)
    (Q : Nat) : Zkc.Verification.Consumer (VerifierContract wiring)
      (soundnessProperty service adversary Q) :=
  ⟨fun _ certificate queryBound => program_soundness certificate service adversary Q queryBound⟩

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir
