module

public import Zkc.Protocols.Sumcheck.Common
public import ZkcSecurity.Families.Sumcheck.Source

@[expose] public section

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Common

open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.AlgebraicRounds (Message)
open Zkc.Polynomial Zkc.Probability

variable {F : Type} [Field F] [DecidableEq F]
variable {wiring : Wiring} {program : Verifier F}

variable [Fintype F]

/-- Exactly two independent uniform field challenges. The fixed prover cannot
inspect the unconsumed tape; no sampler claim is attached to a native handle. -/
def acceptance (program : Verifier F) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F) : ℚ :=
  UniformTape.average 2 (fun coins =>
    if (run program coefficients claim service prover coins.1 coins.2.1).outcome = .returned (some true)
    then 1 else 0)

theorem VerifierContract.acceptance_eq (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F) :
    acceptance program coefficients claim service prover =
      Zkc.Protocols.Sumcheck.acceptance (polynomial coefficients) claim (strategy prover) := by
  unfold acceptance Zkc.Protocols.Sumcheck.acceptance
  congr 1
  funext coins
  rcases coins with ⟨first, second, terminal⟩
  cases terminal
  simp only [certificate.accepted_iff]

/-- Ordinary interactive soundness for arbitrary causal coefficient messages.
This is not knowledge soundness, Fiat–Shamir, or a committed oracle claim. -/
theorem VerifierContract.soundness (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    acceptance program coefficients claim service prover ≤ 4 / (Fintype.card F : ℚ) := by
  rw [certificate.acceptance_eq]
  convert Zkc.Protocols.Sumcheck.soundness (polynomial coefficients) claim (strategy prover) falseClaim using 1
  norm_num

theorem VerifierContract.perfect_completeness (certificate : VerifierContract wiring program) (coefficients : Coefficients F) (service : Nat) :
    acceptance program coefficients (polynomial coefficients).booleanSum service (honestStrategy coefficients) = 1 := by
  rw [certificate.acceptance_eq, honest_strategy]
  exact Zkc.Protocols.Sumcheck.perfect_completeness _

/-- A uniformly sampled private seed is independent of the verifier tape.
Arbitrary fixed private state is already covered by `soundness`. -/
theorem VerifierContract.randomized_soundness (certificate : VerifierContract wiring program) {Seed : Type} [Fintype Seed] [Nonempty Seed]
    (coefficients : Coefficients F) (claim : F) (service : Nat) (prover : Seed → Strategy F)
    (falseClaim : claim ≠ (polynomial coefficients).booleanSum) :
    UniformTape.average (F := Seed) 1 (fun seed => acceptance program coefficients claim service (prover seed.1)) ≤
      4 / (Fintype.card F : ℚ) := by
  rw [← UniformTape.constant (F := Seed) 1 (4 / (Fintype.card F : ℚ))]
  exact UniformTape.monotone 1 _ _ (fun _ => certificate.soundness coefficients claim service _ falseClaim)


end Zkc.Protocols.Sumcheck.Common
