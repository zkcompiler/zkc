module

public import Zkc.Protocols.Sumcheck.Committed.Contract
public import ZkcSecurity.Families.Sumcheck.Committed.Security

@[expose] public section

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.Committed
open Zkc.Polynomial Zkc.Probability
open AdaptiveTape (Tape)

variable {F S : Type} {n : Nat} {scheme : Scheme F n}
variable [Field F] [DecidableEq F]

variable [Fintype F]

/-- Both events use this implementation and the same fixed adversary/tape law. -/
theorem RoundContract.soundness {implementation : RoundImplementation F}
    (certificate : RoundContract implementation n) (statement : Statement scheme)
    (adversary : Adversary scheme S) (claim : F) (prover : S) (epsilonOpen : ℚ)
    (falseClaim : claim ≠ statement.polynomial.booleanSum)
    (openingBound : probability (BadOpeningWith implementation statement adversary claim prover) ≤ epsilonOpen) :
    probability (AcceptedWith implementation statement adversary claim prover) ≤
      (2 * (n : ℚ)) / Fintype.card F + epsilonOpen := by
  have acceptedEq : AcceptedWith implementation statement adversary claim prover =
      Accepted statement adversary claim prover := by
    funext coins
    simp only [AcceptedWith, Accepted, certificate.runWith_eq]
  have badEq : BadOpeningWith implementation statement adversary claim prover =
      BadOpening statement adversary claim prover := by
    funext coins
    simp only [BadOpeningWith, BadOpening, certificate.runWith_eq]
  rw [acceptedEq]
  rw [badEq] at openingBound
  exact Zkc.Protocols.Sumcheck.Committed.soundness statement adversary claim prover
    epsilonOpen falseClaim openingBound


end Zkc.Protocols.Sumcheck.Committed
