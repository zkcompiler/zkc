import ZkcArkLib.PolyFun.Reads

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace TestsArkLib.TypedReads
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint ZkcArkLib.PolyFun.Reads

def start (bs : Bytes) : World Bytes := ⟨initial ⟨"r24","two-read",0⟩,bs⟩
def execute (bs : Bytes) :=
  ((two 7 11 19 11).liftM (interpret (fun _ => []) bufferSupplier)).run (start bs,[])

theorem distinct_reads :
    (execute (Zkc.Protocols.ScalarBytecode.Codec.wire [3,7])).1.map (fun xy => (xy.1.val,xy.2.val)) = .ok (3,7) ∧
    (execute (Zkc.Protocols.ScalarBytecode.Codec.wire [3,7])).2.1.verifier.offset = 16 ∧
    ((execute (Zkc.Protocols.ScalarBytecode.Codec.wire [3,7])).2.2.map Event.site) = [7,19] := by decide

theorem second_noncanonical :
    (execute (Zkc.Protocols.ScalarBytecode.Codec.wire [3,11])).1 = .error (.reject "abi_decode_failure:noncanonical") ∧
    (execute (Zkc.Protocols.ScalarBytecode.Codec.wire [3,11])).2.1.verifier.offset = 16 ∧
    (execute (Zkc.Protocols.ScalarBytecode.Codec.wire [3,11])).2.1.external = [] := by decide

theorem second_short :
    (execute (Zkc.Protocols.ScalarBytecode.Codec.enc 3 ++ [⟨9,by decide⟩])).1 = .error (.reject "abi_decode_failure:underrun") ∧
    (execute (Zkc.Protocols.ScalarBytecode.Codec.enc 3 ++ [⟨9,by decide⟩])).2.1.verifier.offset = 8 ∧
    (execute (Zkc.Protocols.ScalarBytecode.Codec.enc 3 ++ [⟨9,by decide⟩])).2.1.external = [⟨9,by decide⟩] := by decide

theorem first_failure_stops :
    ((execute (Zkc.Protocols.ScalarBytecode.Codec.wire [11,7])).2.2.map Event.site) = [7] ∧
    (execute (Zkc.Protocols.ScalarBytecode.Codec.wire [11,7])).2.1.external = Zkc.Protocols.ScalarBytecode.Codec.enc 7 := by decide

end TestsArkLib.TypedReads
