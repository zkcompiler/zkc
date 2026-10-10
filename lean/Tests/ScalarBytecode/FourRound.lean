import Zkc.Protocols.ScalarBytecode.FourRound.Optimization
import Tests.ScalarBytecode.BlockExtraction

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Tests.ScalarBytecode.FourRound
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Protocols.ScalarBytecode.FourRound.Optimization

def zeroInput : World Bytes :=
  ⟨⟨⟨"r32","n4",4⟩,⟨fun _ => 0,[],0⟩,0,0,[]⟩,Zkc.Protocols.ScalarBytecode.Codec.wire (List.replicate 12 0)⟩

theorem nonvacuous_acceptance :
    (run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.sourceOps zeroInput).outcome = .accept ∧
    (run (openStep (fun _ => []) bufferSupplier) composedOps zeroInput).outcome = .accept := by decide

theorem malformed_preserved :
    (run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.sourceOps
      {zeroInput with external := []}).outcome = .reject "abi_decode_failure:underrun" ∧
    (run (openStep (fun _ => []) bufferSupplier) composedOps
      {zeroInput with external := []}).outcome = .reject "abi_decode_failure:underrun" := by decide

/-- The exact stronger observer cannot be silently retained through arithmetic
    deletion. This uses the existing actual Sumcheck opcode region. -/
theorem scratch_discriminator :
    (run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.Horner.oldPure
      Tests.ScalarBytecode.BlockExtraction.start).state.verifier.core.regs 44 = 6 ∧
    (run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.Horner.newPure
      Tests.ScalarBytecode.BlockExtraction.start).state.verifier.core.regs 44 = 0 := by decide

theorem no_all_register_upgrade : ¬ TerminalRel (OpenRel Zkc.Protocols.ScalarBytecode.Scheduling.allRegs Eq)
    (run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.Horner.oldPure Tests.ScalarBytecode.BlockExtraction.start)
    (run (openStep (fun _ => []) bufferSupplier) Zkc.Protocols.ScalarBytecode.Horner.newPure Tests.ScalarBytecode.BlockExtraction.start) := by
  intro h
  have bad := h.2.1.1.2.2.2.2 44 True.intro
  rw [scratch_discriminator.1,scratch_discriminator.2] at bad
  cases bad

end Tests.ScalarBytecode.FourRound
