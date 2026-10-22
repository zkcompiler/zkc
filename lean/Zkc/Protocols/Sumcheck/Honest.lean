module

public import Zkc.Protocols.Sumcheck.Execution

@[expose] public section

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


end Zkc.Protocols.Sumcheck.Security
