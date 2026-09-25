import Zkc.Protocols.ScalarBytecode.MessageEvaluation.Evaluation

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.MessageEvaluation
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality

def absorbCore (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (c : Zkc.Protocols.ScalarBytecode.Execution.Core) (v dest adest : Nat) : Zkc.Protocols.ScalarBytecode.Execution.Core :=
 {Zkc.Protocols.ScalarBytecode.Execution.put (Zkc.Protocols.ScalarBytecode.Execution.put c dest v) adest 0 with
 provider := hash (c.provider ++ [⟨0,by decide⟩] ++ Zkc.Protocols.ScalarBytecode.Codec.enc v)}
def receivedCore (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (c : Zkc.Protocols.ScalarBytecode.Execution.Core) (b : Block) :=
 absorbCore hash (absorbCore hash (absorbCore hash c b.a.val 27 28) b.b.val 31 32) b.c.val 35 36

def receivedEvents (b : Block) : List Zkc.Protocols.ScalarBytecode.Execution.Event :=
 [⟨13,.read,"g2_0",b.a.val,Zkc.Protocols.ScalarBytecode.Codec.enc b.a.val⟩,⟨14,.absorb,"g2_0",b.a.val,Zkc.Protocols.ScalarBytecode.Codec.enc b.a.val⟩,
  ⟨15,.read,"g2_1",b.b.val,Zkc.Protocols.ScalarBytecode.Codec.enc b.b.val⟩,⟨16,.absorb,"g2_1",b.b.val,Zkc.Protocols.ScalarBytecode.Codec.enc b.b.val⟩,
  ⟨17,.read,"g2_2",b.c.val,Zkc.Protocols.ScalarBytecode.Codec.enc b.c.val⟩,⟨18,.absorb,"g2_2",b.c.val,Zkc.Protocols.ScalarBytecode.Codec.enc b.c.val⟩]
def receive (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :=
 run (Zkc.Protocols.ScalarBytecode.Execution.tailStep hash) ((Zkc.Protocols.ScalarBytecode.Schedules.sumcheck.drop 13).take 6) t

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem streaming_block (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (core : Zkc.Protocols.ScalarBytecode.Execution.Core) (offset : Nat)
 (b : Block) (tail : Bytes) :
 receive hash ⟨Zkc.Protocols.ScalarBytecode.Codec.wire (values b) ++ tail,offset,core⟩ =
 ⟨.incomplete,⟨tail,offset+24,receivedCore hash core b⟩,receivedEvents b⟩ := by
 have hqa : b.a.val < 2305843009213697249 := b.a.isLt
 have hqb : b.b.val < 2305843009213697249 := b.b.isLt
 have hqc : b.c.val < 2305843009213697249 := b.c.isLt
 have ha : b.a.val < 256^8 := Nat.lt_trans b.a.isLt (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
 have hb : b.b.val < 256^8 := Nat.lt_trans b.b.isLt (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
 have hc : b.c.val < 256^8 := Nat.lt_trans b.c.isLt (by decide : Zkc.Protocols.ScalarBytecode.Parameters.modulus < 256^8)
 simp [receive,Zkc.Protocols.ScalarBytecode.Schedules.sumcheck,run,Zkc.Protocols.ScalarBytecode.Execution.tailStep,Zkc.Protocols.ScalarBytecode.Execution.tailHandler,Zkc.Protocols.ScalarBytecode.Execution.effect,Zkc.Protocols.ScalarBytecode.Execution.request,
 Zkc.Protocols.ScalarBytecode.Execution.get,Zkc.Protocols.ScalarBytecode.Execution.put,receivedCore,absorbCore,receivedEvents,values,Zkc.Protocols.ScalarBytecode.Codec.wire,Zkc.Protocols.ScalarBytecode.Codec.enc,
 Zkc.Realization.ByteEncoding.value_be 8 b.a.val ha,Zkc.Realization.ByteEncoding.value_be 8 b.b.val hb,Zkc.Realization.ByteEncoding.value_be 8 b.c.val hc,
 hqa,hqb,hqc,List.append_assoc,Nat.add_assoc]

-- Semantic bridge: actual received coefficients are exactly the Zkc.Protocols.ScalarBytecode.Messages carrier values.
theorem received_projection (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (core : Zkc.Protocols.ScalarBytecode.Execution.Core) (b : Block) :
 project (receivedCore hash core b) 29 = b.a.val ∧
 project (receivedCore hash core b) 30 = b.b.val ∧
 project (receivedCore hash core b) 31 = b.c.val ∧
 rhs (receivedCore hash core b) = rhs core := by
 simp [project,receivedCore,absorbCore,Zkc.Protocols.ScalarBytecode.Execution.put,rhs,Zkc.Protocols.ScalarBytecode.Certificates.round2Right,Zkc.Source.LocalArithmetic.Expr.eval]

def continueJoin (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (out : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event) : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event :=
 if out.outcome = .incomplete then
   match joinedCheck hash out.state with
   | .next t es => ⟨.incomplete,t,out.events ++ es⟩
   | .halt why t es => ⟨why,t,out.events ++ es⟩
 else out

def continueOriginal (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (out : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event) : Terminal Zkc.Protocols.ScalarBytecode.Execution.Tail Zkc.Protocols.ScalarBytecode.Execution.Event :=
 if out.outcome = .incomplete then
   match Zkc.Protocols.ScalarBytecode.Execution.tailStep hash checkInstr (evaluated hash out.state).state with
   | .next t es => ⟨.incomplete,t,out.events ++ es⟩
   | .halt why t es => ⟨why,t,out.events ++ es⟩
 else out

theorem stream_checked_composition (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (t : Zkc.Protocols.ScalarBytecode.Execution.Tail) :
 continueJoin hash (receive hash t) = continueOriginal hash (receive hash t) := by
 simp only [continueJoin,continueOriginal,checked_composition]

-- No desired evaluation equality or honesty equation appears as a premise.
theorem canonical_block_join (hash : Zkc.Protocols.ScalarBytecode.Execution.Hash) (core : Zkc.Protocols.ScalarBytecode.Execution.Core) (offset : Nat)
 (b : Block) (tail : Bytes) :
 continueJoin hash (receive hash ⟨Zkc.Protocols.ScalarBytecode.Codec.wire (values b) ++ tail,offset,core⟩) =
 continueOriginal hash ⟨.incomplete,⟨tail,offset+24,receivedCore hash core b⟩,receivedEvents b⟩ := by
 rw [stream_checked_composition,streaming_block]

end Zkc.Protocols.ScalarBytecode.MessageEvaluation
