import Zkc.Protocols.ScalarBytecode.ProverCorrespondence
import Tests.ScalarBytecode.HashFixture

set_option autoImplicit false

namespace Tests.ScalarBytecode.Prover
open Zkc.Realization.ByteEncoding Zkc.Protocols.ScalarBytecode.Codec Zkc.Protocols.ScalarBytecode.Prover Zkc.Protocols.ScalarBytecode.ProverCorrespondence

-- A countermodel for the stronger observer. This finite fixture hash returns
-- [] outside the recorded producer chains; it is not native SHA-256.
def atomicBlock (hash : Hash) (s : Bytes) (bs : Bytes) : Option (List Nat) × Bytes :=
  match readWords 3 bs with
  | none => (none,s)
  | some (xs,_) => (some xs,xs.foldl (fun h x => absorb hash h (enc x)) s)

def streamingBlock (hash : Hash) : Nat → Bytes → Bytes → Option (List Nat) × Bytes
  | 0,s,_ => (some [],s)
  | n+1,s,bs => match readScalar bs with
    | none => (none,s)
    | some (x,rest) =>
      let out := streamingBlock hash n (absorb hash s (enc x)) rest
      (out.1.map (x :: ·),out.2)

def fixtureState : Bytes := (derived Tests.ScalarBytecode.HashFixture.fixtureHash false 3).1
def malformedBlock : Bytes := wire [1654834368763198252,Zkc.Protocols.ScalarBytecode.Parameters.modulus,0]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem residual_state_separator :
    (atomicBlock Tests.ScalarBytecode.HashFixture.fixtureHash fixtureState malformedBlock).1 = none ∧
    (streamingBlock Tests.ScalarBytecode.HashFixture.fixtureHash 3 fixtureState malformedBlock).1 = none ∧
    (atomicBlock Tests.ScalarBytecode.HashFixture.fixtureHash fixtureState malformedBlock).2 ≠
      (streamingBlock Tests.ScalarBytecode.HashFixture.fixtureHash 3 fixtureState malformedBlock).2 := by
  decide

end Tests.ScalarBytecode.Prover
