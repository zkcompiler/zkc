import Zkc.Protocols.Sumcheck.Execution

/-! Source-bound completeness and ordinary interactive soundness.

The accepting event is the actual staged source's terminal outcome. The prover
has arbitrary explicit state and adaptive callbacks, fixed independently of
the verifier's product tape. A separate lemma mixes independent private seeds.
-/

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Security

open PIR Zkc.Polynomial Zkc.Probability
open AlgebraicRounds (Message)
open AdaptiveTape (Tape)

variable {F : Type}

abbrev HonestState (F : Type) := (n : Nat) × Quadratic F n

section Semiring
variable [CommSemiring F] [DecidableEq F]

def honestSend : HonestState F → Message F × HonestState F
  | state@⟨0, _⟩ => (⟨0, 0, 0⟩, state)
  | state@⟨_ + 1, p⟩ => (roundPolynomial p, state)

def honestReact : HonestState F → F → HonestState F
  | state@⟨0, _⟩, _ => state
  | ⟨n + 1, p⟩, r => ⟨n, p.restrict r⟩

omit [DecidableEq F] in
theorem honest_strategy {n : Nat} (p : Quadratic F n) :
    Execution.strategy honestSend honestReact n ⟨n, p⟩ = honest p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [Execution.strategy, honestSend, honestReact, honest]
      congr 1
      funext r
      exact ih _

theorem source_completeness {n : Nat} (p : Quadratic F n) (coins : Tape F n) :
    (Execution.run honestSend honestReact p p.booleanSum ⟨n, p⟩ (tapeList n coins)).outcome =
      .returned true := by
  rw [Execution.accepted_iff, honest_strategy]
  exact completeness p coins

end Semiring

variable [Field F] [Fintype F] [DecidableEq F]

/-- Probability of the actual source terminal acceptance event. -/
def sourceAcceptance {S : Type} (send : S → Message F × S) (react : S → F → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (prover : S) : ℚ :=
  UniformTape.average n (fun coins =>
    if (Execution.run send react p claim prover (tapeList n coins)).outcome = .returned true
    then 1 else 0)

theorem sourceAcceptance_eq {S : Type} (send : S → Message F × S) (react : S → F → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (prover : S) :
    sourceAcceptance send react p claim prover = acceptance p claim (Execution.strategy send react n prover) := by
  simp only [sourceAcceptance, acceptance, Execution.accepted_iff]

theorem source_soundness {S : Type} (send : S → Message F × S) (react : S → F → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (prover : S) (falseClaim : claim ≠ p.booleanSum) :
    sourceAcceptance send react p claim prover ≤ (2 * (n : ℚ)) / Fintype.card F := by
  rw [sourceAcceptance_eq]
  exact soundness p claim _ falseClaim

theorem source_perfect_completeness {n : Nat} (p : Quadratic F n) :
    sourceAcceptance honestSend honestReact p p.booleanSum ⟨n, p⟩ = 1 := by
  rw [sourceAcceptance_eq, honest_strategy, perfect_completeness]

/-- Uniform private seeds are sampled independently before the verifier tape.
The per-state theorem also permits arbitrary fixed private state. -/
theorem randomized_source_soundness {Seed S : Type} [Fintype Seed] [Nonempty Seed]
    (send : S → Message F × S) (react : S → F → S) (privateState : Seed → S)
    {n : Nat} (p : Quadratic F n) (claim : F) (falseClaim : claim ≠ p.booleanSum) :
    UniformTape.average (F := Seed) 1 (fun seed => sourceAcceptance send react p claim (privateState seed.1)) ≤
      (2 * (n : ℚ)) / Fintype.card F := by
  rw [← UniformTape.constant (F := Seed) 1 ((2 * (n : ℚ)) / Fintype.card F)]
  exact UniformTape.monotone 1 _ _ (fun _ => source_soundness send react p claim _ falseClaim)

end Zkc.Protocols.Sumcheck.Security
