import Zkc.Protocols.ScalarBytecode.StreamingFamily

set_option autoImplicit false

namespace Tests.ScalarBytecode.StreamingFamily
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.StreamingFamily

def zeroHash : Hash := fun _ => []

-- One successful word, then a short word in the wider second round. The
-- completed earlier reads/absorbs/draw remain visible on failure.
theorem zero_rounds_accepts :
    (run (tailStep zeroHash) (instantiate 0) (initial [])).outcome = .accept := by decide

theorem varying_lengths : (instantiate 1).length = 5 ∧ (instantiate 3).length = 17 := by decide

theorem partial_second_round :
    (run (tailStep zeroHash) (instantiate 2)
      (initial (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0] ++ [⟨1,by decide⟩]))).state.offset = 16 ∧
    (run (tailStep zeroHash) (instantiate 2)
      (initial (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0] ++ [⟨1,by decide⟩]))).outcome =
        .reject "abi_decode_failure:underrun" := by decide

end Tests.ScalarBytecode.StreamingFamily
