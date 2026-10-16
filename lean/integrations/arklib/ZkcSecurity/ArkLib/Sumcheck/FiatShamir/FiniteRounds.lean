module

public import ZkcSecurity.ArkLib.Sumcheck.FiatShamir.Knowledge
public import ZkcSecurity.ArkLib.FiatShamir.Transcript.Security
public import Zkc.Protocols.Sumcheck.Execution

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-! Full-prefix Fiat–Shamir soundness for any finite quadratic Sumcheck.
The local knowledge laws are discharged by the polynomial root bound, rather
than assumed of the protocol. The adversary and verifier share one cached RO.
-/

namespace ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds

open Interaction.Oracle Interaction.Oracle.Security
open OracleComp OracleSpec
open Zkc.Polynomial Zkc.Protocols.AlgebraicRounds
open ZkcSecurity.ArkLib.FiatShamir

variable {F : Type} [Field F] [DecidableEq F] [Fintype F] [SampleableType F]

abbrev Path (n : Nat) := (StateRestoration.protocol (rounds (F := F) n)).tree.ExecutionPath

/-- Every boundary check and the final restricted constant must pass. -/
def accepted : (n : Nat) → Quadratic F n → F → Path (F := F) n → Prop
  | 0, p, claim, _ => claim = p.booleanSum
  | n + 1, p, claim, ⟨message, challenge, path⟩ =>
      message.boundary = claim ∧ accepted n (p.restrict challenge) (message.evaluate challenge) path

instance acceptedDecidable (n : Nat) (p : Quadratic F n) (claim : F)
    (path : Path (F := F) n) : Decidable (accepted n p claim path) := by
  induction n generalizing claim with
  | zero => exact inferInstanceAs (Decidable (claim = p.booleanSum))
  | succ n ih =>
      rcases path with ⟨message, challenge, path⟩
      letI := ih (p.restrict challenge) (message.evaluate challenge) path
      exact inferInstanceAs (Decidable (message.boundary = claim ∧
        accepted n (p.restrict challenge) (message.evaluate challenge) path))

def witness : (n : Nat) → (prior : Prop) → (p : Quadratic F n) → (claim : F) →
    (path : Path (F := F) n) → ((extractor n prior p claim).terminalState path).Witness
  | 0, _, _, _, _ => ()
  | n + 1, prior, p, claim, ⟨message, challenge, path⟩ =>
      witness n (prior ∧ message.boundary = claim) (p.restrict challenge)
        (message.evaluate challenge) path

theorem witness_iff (n : Nat) (prior : Prop) (p : Quadratic F n) (claim : F)
    (path : Path (F := F) n) :
    ((extractor n prior p claim).terminalState path).holds (witness n prior p claim path) ↔
      prior ∧ accepted n p claim path := by
  induction n generalizing prior claim with
  | zero => rfl
  | succ n ih =>
      rcases path with ⟨message, challenge, path⟩
      exact (ih (prior ∧ message.boundary = claim) (p.restrict challenge)
        (message.evaluate challenge) path).trans and_assoc

/-- This strategy replays the messages in a completed FS proof. It does not
assert that the proof was generated independently of its oracle challenges. -/
def strategy : (n : Nat) → Path (F := F) n → Zkc.Protocols.Sumcheck.Strategy F n
  | 0, _ => .done
  | n + 1, ⟨message, _, path⟩ => .send message (fun _ => strategy n path)

def coins : (n : Nat) → Path (F := F) n → Zkc.Probability.AdaptiveTape.Tape F n
  | 0, _ => ()
  | n + 1, ⟨_, challenge, path⟩ => (challenge, coins n path)

theorem verify_iff (n : Nat) (p : Quadratic F n) (claim : F) (path : Path (F := F) n) :
    Zkc.Protocols.Sumcheck.verify p claim (strategy n path) (coins n path) = true ↔
      accepted n p claim path := by
  induction n generalizing claim with
  | zero =>
      cases p
      simp [strategy, coins, accepted, Zkc.Protocols.Sumcheck.verify,
        Quadratic.booleanSum, cubeSum, Quadratic.eval]
  | succ n ih =>
      rcases path with ⟨message, challenge, path⟩
      by_cases passes : message.boundary = claim
      · simp only [strategy, coins, Zkc.Protocols.Sumcheck.verify,
          accepted, passes, true_and]
        exact ih (p.restrict challenge) (message.evaluate challenge) path
      · simp [strategy, coins, Zkc.Protocols.Sumcheck.verify, accepted, passes]

def messages : (n : Nat) → Path (F := F) n → List (Message F)
  | 0, _ => []
  | n + 1, ⟨message, _, path⟩ => message :: messages n path

def send : List (Message F) → Message F × List (Message F)
  | [] => (⟨0, 0, 0⟩, [])
  | message :: rest => (message, rest)

theorem replay_strategy (n : Nat) (path : Path (F := F) n) :
    Zkc.Protocols.Sumcheck.Execution.strategy send (fun state _ => state) n (messages n path) =
      strategy n path := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rcases path with ⟨message, challenge, path⟩
      simp only [messages, Zkc.Protocols.Sumcheck.Execution.strategy, send, strategy, ih]

/-- Acceptance of the existing typed, staged source, with all checks and final
polynomial evaluation, is the event used in the ROM theorem below. -/
theorem source_accepted_iff (n : Nat) (p : Quadratic F n) (claim : F)
    (path : Path (F := F) n) :
    (Zkc.Protocols.Sumcheck.Execution.run send (fun state _ => state) p claim (messages n path)
      (Zkc.Protocols.Sumcheck.tapeList n (coins n path))).outcome = .returned true ↔
        accepted n p claim path := by
  rw [Zkc.Protocols.Sumcheck.Execution.accepted_iff, replay_strategy, verify_iff]

/-- Adaptively chosen public inputs and proofs are included. The total call
budget counts adversarial accesses, including retries, and `n` verifier accesses. -/
theorem soundness {Input : Type} (n : Nat) (polynomial : Input → Quadratic F n)
    (claim : Input → F)
    (adversary : OracleComp (Transcript.Spec Input (rounds (F := F) n))
      (Input × Transcript.Messages (rounds (F := F) n) × Unit))
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (Transcript.execution (rounds (F := F) n)
      adversary)).run' ∅}[
      accepted n (polynomial result.1) (claim result.1) result.2.1 ∧
        claim result.1 ≠ (polynomial result.1).booleanSum] ≤
      ((Q + n : Nat) : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  have bound := Transcript.extraction_bound (rounds := rounds (F := F) n)
    (fun z => residualState True (polynomial z) (claim z))
    (fun z => extractor n True (polynomial z) (claim z)) Set.univ
    (2 / (Fintype.card F : ENNReal))
    (fun z _ => prover_preserving n True (polynomial z) (claim z))
    (fun z _ => locally_bounded n True (polynomial z) (claim z))
    (fun z path (_ : Unit) => witness n True (polynomial z) (claim z) path)
    adversary Q queryBound
  simp only [rounds_length] at bound
  apply le_trans (le_of_eq ?_) bound
  apply prEvent_congr
  rintro ⟨z, path, token⟩
  rw [witness_iff]
  simp only [Set.mem_univ, true_and, residualState]

/-- The security event names execution of the existing whole source program.
Completion retains a full path while source execution may reject early. Only
acceptance is transported, and all adversarial preparation uses the shared RO. -/
theorem source_soundness {Input : Type} (n : Nat) (polynomial : Input → Quadratic F n)
    (claim : Input → F)
    (adversary : OracleComp (Transcript.Spec Input (rounds (F := F) n))
      (Input × Transcript.Messages (rounds (F := F) n) × Unit))
    (Q : Nat) (queryBound : IsTotalQueryBound adversary Q) :
    Pr{let result ← (simulateQ randomOracle (Transcript.execution (rounds (F := F) n)
      adversary)).run' ∅}[
      (Zkc.Protocols.Sumcheck.Execution.run send (fun state _ => state)
        (polynomial result.1) (claim result.1) (messages n result.2.1)
        (Zkc.Protocols.Sumcheck.tapeList n (coins n result.2.1))).outcome = PIR.Outcome.returned true ∧
      claim result.1 ≠ (polynomial result.1).booleanSum] ≤
      ((Q + n : Nat) : ENNReal) * (2 / (Fintype.card F : ENNReal)) := by
  have bound := soundness n polynomial claim adversary Q queryBound
  apply le_trans (le_of_eq ?_) bound
  apply prEvent_congr
  intro result
  exact and_congr (source_accepted_iff n _ _ _) Iff.rfl

end ZkcSecurity.ArkLib.Sumcheck.FiatShamir.FiniteRounds
