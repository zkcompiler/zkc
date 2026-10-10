import Zkc.Protocols.ScalarBytecode.FourRound.Scheduling
import Zkc.Protocols.ScalarBytecode.Endpoint.Horner

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

namespace Zkc.Protocols.ScalarBytecode.FourRound.Optimization
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Suppliers

/-- The actual n4 source still contains the earlier five-row Sumcheck region
    after Zkc.Protocols.ScalarBytecode.FourRound.Scheduling schedules the independent work near the last draw. -/
theorem source_segment : Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps =
    Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.take 22 ++ (Zkc.Protocols.ScalarBytecode.Horner.oldPure ++ Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.drop 27) := by rfl

theorem suffix_safe :
    ∀ i ∈ Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.drop 27, Zkc.Protocols.ScalarBytecode.Frames.Safe Zkc.Protocols.ScalarBytecode.Horner.Live i := by
  simp [Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps,Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.sourceOps,Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.newBlock,Zkc.Protocols.ScalarBytecode.Scheduling.mulI,Zkc.Protocols.ScalarBytecode.Scheduling.addI,
    Zkc.Protocols.ScalarBytecode.Scheduling.drawI,Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.prefixProduct,Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.lastDraw,Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.lastPoly,Zkc.Protocols.ScalarBytecode.Frames.Safe,Zkc.Protocols.ScalarBytecode.Frames.Reads,Zkc.Protocols.ScalarBytecode.Horner.Live]

def composedOps : List Instr :=
  Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.take 22 ++ (Zkc.Protocols.ScalarBytecode.Horner.newPure ++ Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.drop 27)

/-- An actual two-pass construction on one represented n4 source, for arbitrary
    deterministic suppliers, initial state and malformed responses. -/
theorem schedule_then_horner {S : Type} (supplier : Supplier S) (hash : Hash)
    (s : World S) :
    TerminalRel (OpenRel Zkc.Protocols.ScalarBytecode.Horner.Live Eq)
      (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.sourceOps s)
      (run (openStep hash supplier) composedOps s) := by
  have first := weaken Zkc.Protocols.ScalarBytecode.Horner.Live Zkc.Protocols.ScalarBytecode.Scheduling.allRegs (fun _ _ => True.intro)
    (Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.bound_source_context supplier hash s)
  have second := open_block_context supplier Zkc.Protocols.ScalarBytecode.Horner.Live hash Zkc.Protocols.ScalarBytecode.Horner.oldPure Zkc.Protocols.ScalarBytecode.Horner.newPure
    (Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.take 22) (Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.scheduledOps.drop 27)
    (pure_open_replacement supplier hash) suffix_safe s
  rw [← source_segment] at second
  exact terminal_trans Zkc.Protocols.ScalarBytecode.Horner.Live first second

theorem represented_lengths : Zkc.Protocols.ScalarBytecode.FourRound.Scheduling.sourceOps.length = 73 ∧ composedOps.length = 72 := by decide

end Zkc.Protocols.ScalarBytecode.FourRound.Optimization
