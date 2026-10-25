module

public import Zkc.Protocols.Sumcheck.FactorOpening.Execution
public import ZkcSecurity.Families.Sumcheck.Common
public import ZkcSecurity.Families.Sumcheck.Committed.Security

@[expose] public section

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.FactorOpening
open Zkc.Source Zkc.Source.Common Zkc.Source.Common.Native
open Zkc.Protocols.Sumcheck.Common
open Zkc.Probability

variable {F : Type} [Field F] [DecidableEq F]

variable [Fintype F]

noncomputable def acceptance (program : Verifier F) (statement : Statement F) (claim : F)
    (service : Nat) (prover : Strategy F) : ℚ :=
  Committed.probability (fun coins : AdaptiveTape.Tape F 2 =>
    (run program statement claim service prover coins.1 coins.2.1).outcome = .returned (some true))

noncomputable def openingLoss (checks : Checks F) (statement : Statement F) (claim : F)
    (prover : Strategy F) : ℚ :=
  Committed.probability (fun coins : AdaptiveTape.Tape F 2 =>
    BadOpening checks statement prover claim coins.1 coins.2.1)

theorem VerifierContract.conditional_soundness {wiring : Wiring} {checks : Checks F} {program : Verifier F}
    (certificate : VerifierContract wiring checks program) (statement : Statement F) (claim : F)
    (service : Nat) (prover : Strategy F) (epsilon : ℚ)
    (falseClaim : claim ≠ (polynomial (coefficients statement)).booleanSum)
    (openingBound : openingLoss checks statement claim prover ≤ epsilon) :
    acceptance program statement claim service prover ≤ 4 / (Fintype.card F : ℚ) + epsilon := by
  have bound := Committed.probability_le_add
    (fun coins : AdaptiveTape.Tape F 2 =>
      (run program statement claim service prover coins.1 coins.2.1).outcome = .returned (some true))
    (fun coins => Zkc.Protocols.Sumcheck.verify (polynomial (coefficients statement)) claim
      (Common.strategy prover.rounds) coins = true)
    (fun coins => BadOpening checks statement prover claim coins.1 coins.2.1) (by
      rintro ⟨first, second, ⟨⟩⟩ accepted
      exact accepted_source_or_bad checks statement prover claim first second
        ((certificate.accepted_iff statement claim service prover first second).mp accepted))
  have sourceEq : Committed.probability (fun coins : AdaptiveTape.Tape F 2 =>
      Zkc.Protocols.Sumcheck.verify (polynomial (coefficients statement)) claim
        (Common.strategy prover.rounds) coins = true) =
      Zkc.Protocols.Sumcheck.acceptance (polynomial (coefficients statement)) claim (Common.strategy prover.rounds) := by
    classical
    unfold Committed.probability Zkc.Protocols.Sumcheck.acceptance
    congr 1
    funext coins
    split <;> simp_all
  rw [sourceEq] at bound
  apply bound.trans
  apply add_le_add _ openingBound
  have sourceBound := Zkc.Protocols.Sumcheck.soundness (polynomial (coefficients statement))
    claim (Common.strategy prover.rounds) falseClaim
  norm_num at sourceBound
  exact sourceBound

theorem public_openingLoss (statement : Statement F) (claim : F) (prover : Strategy F) :
    openingLoss publicChecks statement claim prover = 0 := by
  classical
  simp only [openingLoss, Committed.probability, public_no_bad, ite_false]
  exact UniformTape.constant 2 0

theorem VerifierContract.soundness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring publicChecks program) (statement : Statement F)
    (claim : F) (service : Nat) (prover : Strategy F)
    (falseClaim : claim ≠ (polynomial (coefficients statement)).booleanSum) :
    acceptance program statement claim service prover ≤ 4 / (Fintype.card F : ℚ) := by
  simpa using certificate.conditional_soundness statement claim service prover 0 falseClaim
    (le_of_eq (public_openingLoss statement claim prover))

theorem VerifierContract.perfect_completeness {wiring : Wiring} {program : Verifier F}
    (certificate : VerifierContract wiring publicChecks program) (statement : Statement F) (service : Nat) :
    acceptance program statement (polynomial (coefficients statement)).booleanSum service
      (honestStrategy statement) = 1 := by
  classical
  simp only [acceptance, Committed.probability, certificate.completeness, ite_true]
  exact UniformTape.constant 2 1


end Zkc.Protocols.Sumcheck.FactorOpening
