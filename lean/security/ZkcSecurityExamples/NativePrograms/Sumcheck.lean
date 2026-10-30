module

public import ZkcExamples.NativePrograms.Sumcheck
public import ZkcSecurity.Families.Sumcheck.Common

@[expose] public section

set_option autoImplicit false
noncomputable section

namespace ZkcExamples.NativePrograms.Sumcheck

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Polynomial Zkc.Probability

variable {F : Type} [Field F] [DecidableEq F]

export Zkc.Protocols.Sumcheck.Common
  (Strategy strategy strategy_surjective received transcriptHandler handler_receive_field handler_query
    handler_send honestStrategy honest_strategy)

variable [Fintype F]

/-- Exactly two independent uniform field challenges. The fixed prover cannot
inspect the unconsumed tape; no sampler claim is attached to a native handle. -/
abbrev acceptance := Zkc.Protocols.Sumcheck.Common.acceptance (verifier (F := F))

theorem acceptance_eq (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F) :
    acceptance coefficients claim service prover =
      Zkc.Protocols.Sumcheck.acceptance (polynomial coefficients) claim (strategy prover) := by
  exact contract.acceptance_eq coefficients claim service prover

/-- Ordinary interactive soundness for arbitrary causal coefficient messages.
This is not knowledge soundness, Fiat–Shamir, or a committed oracle claim. -/
theorem soundness (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    acceptance coefficients claim service prover ≤ 4 / (Fintype.card F : ℚ) := by
  exact contract.soundness coefficients claim service prover falseClaim

theorem perfect_completeness (coefficients : Coefficients F) (service : Nat) :
    acceptance coefficients (polynomial coefficients).booleanSum service (honestStrategy coefficients) = 1 := by
  exact contract.perfect_completeness coefficients service

/-- A uniformly sampled private seed is independent of the verifier tape.
Arbitrary fixed private state is already covered by `soundness`. -/
theorem randomized_soundness {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Seed → Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    UniformTape.average (F := Seed) 1 (fun seed => acceptance coefficients claim service (prover seed.1)) ≤
      4 / (Fintype.card F : ℚ) := by
  exact contract.randomized_soundness coefficients claim service prover falseClaim


end ZkcExamples.NativePrograms.Sumcheck

end
