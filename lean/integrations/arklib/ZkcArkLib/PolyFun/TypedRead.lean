import Zkc.Protocols.ScalarBytecode.Endpoint.Reads
import PolyFun.PFunctor.Free.Basic

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace ZkcArkLib.PolyFun.TypedRead
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint PFunctor

inductive Op where
  | read : Nat → Op
  | abort : Exit → Op
def signature : PFunctor where
  A := Op
  B := fun op => match op with
    | .read bound => Except Exit (Fin bound)
    | .abort _ => PEmpty

-- A failed read routes to a nullary operation. On success the continuation
-- receives a certified canonical value, not an arbitrary Nat/status code.
def readValue (bound : Nat) : FreeM signature Nat :=
  .liftBind (.read bound) (fun result => match result with
    | .ok v => .pure v.val
    | .error why => .liftBind (.abort why) PEmpty.elim)

abbrev M := ExceptT Exit (StateM (Local × List Event))
def interpret (hash : Hash) (site : Nat) (word : Word) :
    (op : signature.A) → M (signature.B op)
  | .read bound => fun s =>
    let p := readPacket hash site bound s.1 word
    (.ok p.result, p.state, s.2 ++ p.events)
  | .abort why => fun s => (.error why,s)

theorem actual_typed_read (hash : Hash) (site bound : Nat) (word : Word)
    (v : Local) (log : List Event) :
    ((readValue bound).liftM (interpret hash site word)).run (v,log) =
      ((readPacket hash site bound v word).result.map Fin.val,
       (readPacket hash site bound v word).state,
       log ++ (readPacket hash site bound v word).events) := by
  simp only [readValue,FreeM.liftM]
  change (FreeM.liftM (interpret hash site word)
    (match (readPacket hash site bound v word).result with
      | .ok x => .pure x.val
      | .error why => .liftBind (.abort why) PEmpty.elim)).run
      ((readPacket hash site bound v word).state,
       log ++ (readPacket hash site bound v word).events) = _
  cases h : (readPacket hash site bound v word).result <;> rfl

-- Erase only the proof refinement; retain failure state and the actual Zkc.Protocols.ScalarBytecode.Suppliers
-- update. This consumes the earlier read-packet erasure theorem.
theorem primitive_erasure (hash : Hash) (site bound : Nat) (word : Word) (v : Local) :
    erasePacket (readPacket hash site bound v word) = update hash (readInstr site bound) word v :=
  read_packet_step hash site bound v word

theorem failure_state (hash : Hash) (site bound : Nat) (word : Word)
    (v : Local) (log : List Event) (why : Exit)
    (h : (readPacket hash site bound v word).result = .error why) :
    ((readValue bound).liftM (interpret hash site word)).run (v,log) =
      (.error why, (readPacket hash site bound v word).state,
       log ++ (readPacket hash site bound v word).events) := by
  rw [actual_typed_read,h]
  rfl

end ZkcArkLib.PolyFun.TypedRead
