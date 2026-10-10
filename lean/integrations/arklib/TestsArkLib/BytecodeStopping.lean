import Tests.ScalarBytecode.Stopping
import ZkcArkLib.Sumcheck.Stopping

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace TestsArkLib.BytecodeStopping
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint Tests.ScalarBytecode.Stopping

/-- ZkcArkLib.Sumcheck.Scalar already documents deferred failure. This anchors its resource obstruction
    to the actual bytecode source, rather than reporting it as a new ZkcArkLib.Sumcheck.Scalar defect. -/
theorem actual_source_deferred_resource_mismatch :
    (countedSource 1 (Zkc.Protocols.ScalarBytecode.Codec.wire [0,0,0])).state.external.2 ≠ ZkcArkLib.Sumcheck.Scalar.Stopping.arkFailure.2 := by
  rw [ZkcArkLib.Sumcheck.Scalar.Stopping.actual_arklib_failure_consumes_challenge]
  decide

end TestsArkLib.BytecodeStopping
