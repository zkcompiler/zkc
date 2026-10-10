import Zkc.Protocols.ScalarBytecode.Probability

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Tests.ScalarBytecode.Stopping
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

/-- A counter counts exactly challenge notices, retaining byte state as well. -/
def drawCountSupplier : Supplier (Bytes × Nat) where
  read := fun k n s => let a := bufferSupplier.read k n s.1; (a.1,(a.2,s.2))
  ended := fun k s => let a := bufferSupplier.ended k s.1; (a.1,(a.2,s.2))
  challenge := fun _ _ s => (s.1,s.2+1)

def countedSource (claim : Nat) (bs : Bytes) :=
  run (openStep (fun _ => []) drawCountSupplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.code
    ⟨(Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs).verifier,(bs,0)⟩

/-- Actual source, canonical values, canonical public input: it stops before draw. -/
theorem actual_early_reject :
    (countedSource 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).outcome = .reject "check_failure" ∧
    (countedSource 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).state.external = ([],0) ∧
    (countedSource 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).state.verifier.offset = 24 := by decide

/-- Swap only the adjacent guard/draw in the actual reified source. -/
def deferredCode := Zkc.Protocols.ScalarBytecode.OneRound.Source.code.take 11 ++
  (Zkc.Protocols.ScalarBytecode.OneRound.Source.code.drop 12).take 1 ++ (Zkc.Protocols.ScalarBytecode.OneRound.Source.code.drop 11).take 1 ++
  Zkc.Protocols.ScalarBytecode.OneRound.Source.code.drop 13

def deferredSource :=
  run (openStep (fun _ => []) drawCountSupplier) deferredCode
    ⟨(Zkc.Protocols.ScalarBytecode.OneRound.Source.initial 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).verifier,(Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0],0)⟩

/-- Same input, hash, supplier and retained-state observer; same rejection,
    but the deferred version has consumed one challenge notice. -/
theorem same_provider_deferred_obstruction :
    deferredSource.outcome = (countedSource 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).outcome ∧
    deferredSource.state.external = ([],1) ∧
    (countedSource 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).state.external = ([],0) := by decide

/-- Normalizing a noncanonical byte word to its residue discards a real refusal.
    Both byte strings have residue coefficients [0,2,0], but different outcomes. -/
theorem normalization_loses_rejection :
    Zkc.Protocols.ScalarBytecode.Parameters.modulus % Zkc.Protocols.ScalarBytecode.Parameters.modulus = 0 ∧
    (countedSource 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [Zkc.Protocols.ScalarBytecode.Parameters.modulus,2,0])).outcome =
      .reject "abi_decode_failure:noncanonical" ∧
    (countedSource 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [Zkc.Protocols.ScalarBytecode.Parameters.modulus,2,0])).state.verifier.offset = 8 ∧
    (countedSource 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,2,0])).outcome = .accept := by decide

/-- Constant-zero is admissible for caller_refinement but is not a fresh law.
    False claim 0 for target polynomial 2X is accepted with all-zero coefficients. -/
theorem arbitrary_hash_is_not_soundness :
    (countedSource 0 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).outcome = .accept ∧
    (countedSource 0 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).state.external.2 = 1 := by decide

end Tests.ScalarBytecode.Stopping
