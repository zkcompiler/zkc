import Zkc.Protocols.ScalarBytecode.OneRound.Compilation
import Tests.ScalarBytecode.BlockExtraction
import Zkc.Protocols.ScalarBytecode.OneRound.Source

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Tests.ScalarBytecode.OneRound
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Compiler.Blocks Zkc.Protocols.ScalarBytecode.BlockExecution

def source (claim : Nat) (bs : Bytes) :=
  run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.OneRound.Source.code (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial claim bs)

theorem accepts : (source 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,2,0])).outcome = .accept := by decide
theorem short_retains_offset :
    (source 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 0 ++ [⟨9,by decide⟩])).state.verifier.offset = 8 ∧
    (source 2 (Zkc.Protocols.ScalarBytecode.Codec.enc 0 ++ [⟨9,by decide⟩])).outcome =
      .reject "abi_decode_failure:underrun" := by decide
theorem noncanonical_consumes_word :
    (source 2 (Zkc.Protocols.ScalarBytecode.Codec.enc Zkc.Protocols.ScalarBytecode.Parameters.modulus)).state.verifier.offset = 8 ∧
    (source 2 (Zkc.Protocols.ScalarBytecode.Codec.enc Zkc.Protocols.ScalarBytecode.Parameters.modulus)).outcome =
      .reject "abi_decode_failure:noncanonical" := by decide

/-- An external service may distinguish source occurrences. Read the same
    proof bytes, but answer end-of-proof only at the selected source site. -/
def siteSupplier : Supplier Bytes where
  read := bufferSupplier.read
  ended := fun key s => ((key.site == 20) && s.isEmpty,s)
  challenge := bufferSupplier.challenge
def renameEnd (i : Instr) : Instr :=
  if i.site == 20 then {i with site := 15} else i
def keyed (code : List Instr) :=
  run (openStep (fun _ => []) siteSupplier) code (Zkc.Protocols.ScalarBytecode.OneRound.Source.initial 2 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,2,0]))

theorem raw_occurrence_matters :
    (keyed Zkc.Protocols.ScalarBytecode.OneRound.Source.code).outcome = .accept ∧
    (keyed (Zkc.Protocols.ScalarBytecode.OneRound.Source.code.map renameEnd)).outcome = .reject "proof_trailing_data" := by decide

/-- Pure module equality does not validate an actual caller's operand order. -/
theorem swapped_inputs_change_value :
    (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.loadInputs Zkc.Protocols.ScalarBytecode.OneRound.Compilation.selectedRef.inputs Tests.ScalarBytecode.BlockExtraction.start.verifier 1).val = 2 ∧
    (Zkc.Protocols.ScalarBytecode.OneRound.Compilation.loadInputs [5,13,9,25] Tests.ScalarBytecode.BlockExtraction.start.verifier 1).val = 0 ∧
    (Zkc.Protocols.ScalarBytecode.BlockExtraction.moduleResult Tests.ScalarBytecode.BlockExtraction.start.verifier).val = 6 := by decide

end Tests.ScalarBytecode.OneRound
