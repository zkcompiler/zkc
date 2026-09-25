import Tests.SessionControls
import Zkc.Protocols.AlgebraicRounds.EarlySource

set_option autoImplicit false
namespace Tests.SessionBoundaries
open PIR

/-- The actual round endpoint reaches finished at every returned terminal.
    Rejected messages stop and cannot create a returned terminal phase. -/
theorem round_returns {F : Type} [CommRing F] [DecidableEq F]
    (evaluate : Zkc.Protocols.AlgebraicRounds.Scalar.Round F → F) (n : Nat) (claim : F) :
    Boundary.Returns (Zkc.Protocols.AlgebraicRounds.EarlySource.interaction evaluate)
      (fun _ phase => phase = .finished) (Zkc.Protocols.AlgebraicRounds.EarlySource.source evaluate n claim)
      (Zkc.Protocols.AlgebraicRounds.EarlySource.start n claim) := by
  induction n generalizing claim with
  | zero => rfl
  | succ n ih =>
    intro msg
    by_cases h : Zkc.Protocols.AlgebraicRounds.Scalar.boundary (Zkc.Protocols.AlgebraicRounds.Early.roundOf msg 0) = claim
    · simp only [Boundary.Returns,Zkc.Protocols.AlgebraicRounds.EarlySource.interaction,Zkc.Protocols.AlgebraicRounds.EarlySource.start,if_pos h]
      exact fun _ => ih _
    · simp [Boundary.Returns,Zkc.Protocols.AlgebraicRounds.EarlySource.interaction,Zkc.Protocols.AlgebraicRounds.EarlySource.start,h]

end Tests.SessionBoundaries
