import Zkc.Protocols.ScalarBytecode.Suppliers.Representations
import Zkc.Protocols.ScalarBytecode.StreamingFamily

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Suppliers
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Zkc.Protocols.ScalarBytecode.Schedules

theorem cursor_family (hash : Hash) (n : Nat) (v : Local) (s : TapeCursor) :
    TerminalRel (WorldRel CursorRel)
      (run (openStep hash cursorSupplier) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) ⟨v,s⟩)
      (run (openStep hash bufferSupplier) (Zkc.Protocols.ScalarBytecode.StreamingFamily.instantiate n) ⟨v,s.full.drop s.position⟩) :=
  cursor_run hash _ v s

theorem cursor_schnorr (hash : Hash) (v : Local) (s : TapeCursor) :
    TerminalRel (WorldRel CursorRel)
      (run (openStep hash cursorSupplier) schnorr ⟨v,s⟩)
      (run (openStep hash bufferSupplier) schnorr ⟨v,s.full.drop s.position⟩) :=
  cursor_run hash _ v s

end Zkc.Protocols.ScalarBytecode.Suppliers
