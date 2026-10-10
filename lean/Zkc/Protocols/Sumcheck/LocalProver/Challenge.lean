import Zkc.Protocols.Sumcheck.LocalProver.Code
import Zkc.Probability.ConditionalTape

set_option autoImplicit false

namespace Zkc.Protocols.Sumcheck.LocalProver
open PIR ProductTape
variable {D S E F : Type} {J : Signature}

/-- The local prover boundary permits a challenge only after a committed message.
    Cut.stopped is local result data; it requires this explicit interpretation. -/
def committedOnly (active : View D S E (Cut F) → Bool)
    (v : View D S E (Cut F)) : Bool :=
  match v.outcome with
  | .returned (.committed _) => active v
  | _ => false

theorem abort_no_draw (localH : MonadHandler PMF J S E)
    (active : View D S E (Cut F) → Bool) (localState : State F)
    (s : S) (n : Nat) (es : List (Sum D E)) (rest : List D) :
    (request (committedOnly active) ⟨.returned (.stopped localState),(s,n),es⟩).runM
      (persistent localH) (s,rest) =
        (pure ⟨.stopped .abort,(s,rest),[]⟩ : PMF _) := by
  simp [request, committedOnly, Proc.runM]

end Zkc.Protocols.Sumcheck.LocalProver
