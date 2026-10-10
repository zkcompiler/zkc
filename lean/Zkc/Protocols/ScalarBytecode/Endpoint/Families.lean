import Zkc.Protocols.ScalarBytecode.Endpoint.Execution
import Zkc.Protocols.ScalarBytecode.StreamingFamily

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Endpoint
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution

/-- The exact N9 family, with the same byte failures, all raw initial states,
    and every public parameter, now has an open local implementation. -/
theorem family_join (n : Nat) (hash : Hash) (g : World Bytes) :
    TerminalRel (fun s t => toTail s = t)
      (run (openStep hash bufferSupplier) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) g)
      (Zkc.Protocols.ScalarBytecode.StreamingFamily.execBlocks hash (Zkc.Protocols.ScalarBytecode.StreamingFamily.blocks n) (toTail g)) := by
  rw [← Zkc.Protocols.ScalarBytecode.StreamingFamily.family_execution]
  exact buffer_run hash _ g

theorem admitted_family_join (cap n : Nat) (ops : List Instr)
    (h : Zkc.Protocols.ScalarBytecode.StreamingFamily.boundedInstance cap n = some ops) (hash : Hash) (g : World Bytes) :
    ops.length ≤ cap ∧ TerminalRel (fun s t => toTail s = t)
      (run (openStep hash bufferSupplier) ops g) (run (tailStep hash) ops (toTail g)) :=
  ⟨Zkc.Protocols.ScalarBytecode.StreamingFamily.admitted_list_bound cap n ops h, buffer_run hash ops g⟩


theorem endpoint_family (n : Nat) (hash : Hash) (p : Public) (bs : Bytes) :
    TerminalRel (fun s t => toTail s = t)
      (endpoint hash bufferSupplier (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n).length
        ⟨initial p,bs⟩)
      (Zkc.Protocols.ScalarBytecode.StreamingFamily.execBlocks hash (Zkc.Protocols.ScalarBytecode.StreamingFamily.blocks n) (Zkc.Protocols.ScalarBytecode.StreamingFamily.initial bs)) := by
  rw [show endpoint hash bufferSupplier (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n).length
      ⟨initial p,bs⟩ = run (openStep hash bufferSupplier) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) ⟨initial p,bs⟩ from
        endpoint_list hash bufferSupplier [] _ _ rfl]
  exact family_join n hash ⟨initial p,bs⟩

def subject (artifact : String) (n : Nat) : Public := ⟨artifact,"N9-stream-probe-v1",n⟩
def familyEndpoint (artifact : String) (n : Nat) (hash : Hash) (bs : Bytes) :=
  endpoint hash bufferSupplier (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n).length
    ⟨initial (subject artifact n),bs⟩

theorem family_endpoint_join (artifact : String) (n : Nat) (hash : Hash) (bs : Bytes) :
    TerminalRel (fun s t => toTail s = t) (familyEndpoint artifact n hash bs)
      (Zkc.Protocols.ScalarBytecode.StreamingFamily.execBlocks hash (Zkc.Protocols.ScalarBytecode.StreamingFamily.blocks n) (Zkc.Protocols.ScalarBytecode.StreamingFamily.initial bs)) :=
  endpoint_family n hash (subject artifact n) bs

theorem different_instance_keys (artifact : String) (n m site : Nat) (h : n ≠ m) :
    (Key.mk (subject artifact n) site) ≠ Key.mk (subject artifact m) site := by
  intro eqk
  exact h (congrArg (fun k => k.subject.parameter) eqk)

end Zkc.Protocols.ScalarBytecode.Endpoint
