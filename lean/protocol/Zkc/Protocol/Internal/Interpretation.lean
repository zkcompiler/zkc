module

public import Zkc.Protocol.Internal.Process

/-! The sole backend interpretation commutes with component substitution. -/

public section
open PIR PFunctor

namespace ProtocolProof.Internal
variable {I J : Signature} {A : Type}

/-- Expanding a component before encoding is the same as substituting its encoded body.
Stopped replies short-circuit on both sides; no failure or continuation is discarded. -/
theorem encode_interpret (implementation : OperationInterpretation I J) (client : Process I A) :
    encode (client.interpret implementation) =
      (encode client).liftM (fun operation ↦ encode (implementation operation)) := by
  induction client with
  | done value => rfl
  | halt reason => rfl
  | call operation next ih =>
      simp only [Process.interpret, encode_bind, encode, FreeM.liftM, outcomeBind]
      congr 1
      funext outcome
      cases outcome with
      | returned value => exact ih value
      | stopped reason => rfl

end ProtocolProof.Internal
