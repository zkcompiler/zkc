import Zkc.Protocols.ScalarBytecode.Endpoint.Frames
import Zkc.Protocols.ScalarBytecode.Horner

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Endpoint
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Suppliers Zkc.Protocols.ScalarBytecode.Schedules

/- The old Zkc.Protocols.ScalarBytecode.Horner polynomial identity under the actual open interpreter.
    All arithmetic here is silent to Supplier; no tape/closure law is used. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem pure_open_replacement {S : Type} (supplier : Supplier S) (hash : Hash) (s : World S) :
    TerminalRel (OpenRel Zkc.Protocols.ScalarBytecode.Horner.Live Eq)
      (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.Horner.oldPure s) (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.Horner.newPure s) := by
  simp [TerminalRel,OpenRel,LocalRel,Zkc.Protocols.ScalarBytecode.Frames.CoreRel,Zkc.Protocols.ScalarBytecode.Horner.oldPure,Zkc.Protocols.ScalarBytecode.Horner.newPure,sumcheck,run,
    openStep,serve,notify,update,mapStep,eventsOf,effect,request,Zkc.Protocols.ScalarBytecode.Execution.get,put]
  intro n hn
  rcases hn with ⟨h44,h46,h48⟩
  simp only [h44,h46,h48,↓reduceIte]
  by_cases h52 : n = 52
  · subst n
    simp only [↓reduceIte]
    congr 1; ring
  · by_cases h50 : n = 50
    · subst n
      simp only [h52,↓reduceIte]
      congr 1; ring
    · simp [h52,h50]

/-- Universal in the actual Zkc.Protocols.ScalarBytecode.Endpoint deterministic supplier, including malformed
    and adaptive answers; preserves its entire private final state. -/
theorem sumcheck_open {S : Type} (supplier : Supplier S) (hash : Hash) (s : World S) :
    TerminalRel (OpenRel Zkc.Protocols.ScalarBytecode.Horner.Live Eq)
      (run (openStep hash supplier) sumcheck s)
      (run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.Horner.optimized s) :=
  open_block_context supplier Zkc.Protocols.ScalarBytecode.Horner.Live hash Zkc.Protocols.ScalarBytecode.Horner.oldPure Zkc.Protocols.ScalarBytecode.Horner.newPure (sumcheck.take 22) Zkc.Protocols.ScalarBytecode.Horner.suffix
    (pure_open_replacement supplier hash) Zkc.Protocols.ScalarBytecode.Horner.suffix_safe s

/-- The same law reaches actual local PC dispatch at each program's own
    remaining length. A common fixed fuel or step observer is not assumed. -/
theorem endpoint_optimization {S : Type} (supplier : Supplier S) (hash : Hash)
    (v : Local) (s : S) (hv : v.pc = 0) :
    TerminalRel (OpenRel Zkc.Protocols.ScalarBytecode.Horner.Live Eq)
      (endpoint hash supplier sumcheck sumcheck.length ⟨v,s⟩)
      (endpoint hash supplier Zkc.Protocols.ScalarBytecode.Horner.optimized Zkc.Protocols.ScalarBytecode.Horner.optimized.length ⟨v,s⟩) := by
  rw [show endpoint hash supplier sumcheck sumcheck.length ⟨v,s⟩ =
      run (openStep hash supplier) sumcheck ⟨v,s⟩ from endpoint_list hash supplier [] _ _ hv]
  rw [show endpoint hash supplier Zkc.Protocols.ScalarBytecode.Horner.optimized Zkc.Protocols.ScalarBytecode.Horner.optimized.length ⟨v,s⟩ =
      run (openStep hash supplier) Zkc.Protocols.ScalarBytecode.Horner.optimized ⟨v,s⟩ from endpoint_list hash supplier [] _ _ hv]
  exact sumcheck_open supplier hash _

end Zkc.Protocols.ScalarBytecode.Endpoint
