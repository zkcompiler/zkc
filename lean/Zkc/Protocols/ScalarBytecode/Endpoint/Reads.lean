import Zkc.Protocols.ScalarBytecode.Endpoint.Execution

set_option autoImplicit false

namespace Zkc.Protocols.ScalarBytecode.Endpoint
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution

def readInstr (site bound : Nat) : Instr :=
  ⟨site,.read,.binding,.binding,bound,[],"typed-word",0⟩

/-- Wrap an already lawful reply. This does not rerun or replace the decoder. -/
def refineRead (r : Request sig) (isRead : r.op = .read) (reply : Reply sig r)
    (law : LegalReply r reply) : Except Exit (Fin r.arg.a) :=
  match reply with
  | .ok value => .ok ⟨value,law isRead⟩
  | .reject why => .error (.reject why)
  | .unavailable why => .error (.unavailable why)

def typedRead (hash : Hash) (site bound : Nat) (v : Local) (w : Word) : Except Exit (Fin bound) :=
  let r := request (readInstr site bound) v.core
  let t : Tail := ⟨w.val,v.offset,v.core⟩
  refineRead r rfl (tailHandler hash r t).1 (handler_lawful hash r t trivial)

def eraseRead {n : Nat} (out : Except Exit (Fin n)) : Except Exit Nat :=
  out.map Fin.val

def rawReply (r : Request sig) (reply : Reply sig r) : Except Exit Nat :=
  match reply with
  | .ok value => .ok value
  | .reject why => .error (.reject why)
  | .unavailable why => .error (.unavailable why)

theorem refineRead_erasure (r : Request sig) (isRead : r.op = .read) (reply : Reply sig r)
    (law : LegalReply r reply) :
    eraseRead (refineRead r isRead reply law) = rawReply r reply := by
  cases reply <;> rfl

def rawRead (hash : Hash) (site bound : Nat) (v : Local) (w : Word) : Except Exit Nat :=
  rawReply (request (readInstr site bound) v.core)
    (effect hash (request (readInstr site bound) v.core) v.core w.val).1

theorem typed_erasure (hash : Hash) (site bound : Nat) (v : Local) (w : Word) :
    eraseRead (typedRead hash site bound v w) = rawRead hash site bound v w :=
  refineRead_erasure (request (readInstr site bound) v.core) rfl
    (tailHandler hash (request (readInstr site bound) v.core) ⟨w.val,v.offset,v.core⟩).1
    (handler_lawful hash _ _ trivial)

/-- The continuation is supplied the actual post-read local state and a
    value certified by Zkc.Protocols.ScalarBytecode.Execution's read law. Failure does not invoke it. -/
def continueRead {X : Type} (hash : Hash) (site bound : Nat) (v : Local) (w : Word)
    (k : Fin bound → Local → X) : Except Exit X :=
  (typedRead hash site bound v w).map (fun value =>
    k value (stateOf (update hash (readInstr site bound) w v)))

theorem failed_continuation {X : Type} (hash : Hash) (site bound : Nat) (v : Local) (w : Word)
    (k : Fin bound → Local → X) (why : Exit) (h : typedRead hash site bound v w = .error why) :
    continueRead hash site bound v w k = .error why := by
  simp only [continueRead,h]
  rfl

theorem open_local_erasure {S : Type} (hash : Hash) (supplier : Supplier S) (i : Instr) (g : World S) :
    mapStep view (openStep hash supplier i g) =
      update hash i (serve supplier i g.verifier g.external).1 g.verifier := by
  dsimp only [openStep]
  generalize update hash i (serve supplier i g.verifier g.external).1 g.verifier = out
  cases out <;> rfl

theorem equal_response_successor {S : Type} (hash : Hash) (supplier : Supplier S) (i : Instr)
    (g h : World S) (sameView : view g = view h)
    (sameInput : (serve supplier i g.verifier g.external).1 = (serve supplier i h.verifier h.external).1) :
    mapStep view (openStep hash supplier i g) = mapStep view (openStep hash supplier i h) := by
  rw [open_local_erasure,open_local_erasure,sameInput]
  exact congrArg (update hash i _) sameView

structure ReadPacket (bound : Nat) where
  result : Except Exit (Fin bound)
  state : Local
  events : List Event

/-- Retain state and events on error as well as success. The two pure decoder
    evaluations here are a reference construction, not a once-only native API. -/
def readPacket (hash : Hash) (site bound : Nat) (v : Local) (w : Word) : ReadPacket bound :=
  let out := update hash (readInstr site bound) w v
  ⟨typedRead hash site bound v w,stateOf out,eventsOf out⟩

def erasePacket {bound : Nat} (p : ReadPacket bound) : Step Local Event :=
  match p.result with
  | .ok _ => .next p.state p.events
  | .error why => .halt why p.state p.events

def rawResultStep (r : Except Exit Nat) (out : Step Local Event) : Step Local Event :=
  match r with
  | .ok _ => .next (stateOf out) (eventsOf out)
  | .error why => .halt why (stateOf out) (eventsOf out)

/-- The typed result and entire original local step agree,
    including the failure exit, post-state, consumed offset and events. -/
theorem read_packet_step (hash : Hash) (site bound : Nat) (v : Local) (w : Word) :
    erasePacket (readPacket hash site bound v w) = update hash (readInstr site bound) w v := by
  calc
    _ = rawResultStep (rawRead hash site bound v w) (update hash (readInstr site bound) w v) := by
      rw [← typed_erasure]
      dsimp only [erasePacket,readPacket]
      cases typedRead hash site bound v w <;> rfl
    _ = _ := by
      dsimp only [rawRead,update,readInstr,inputBytes]
      generalize effect hash (request ⟨site,.read,.binding,.binding,bound,[],"typed-word",0⟩ v.core) v.core w.val = e
      rcases e with ⟨reply,core,consumed,events⟩
      cases reply <;> rfl

theorem read_packet_value (hash : Hash) (site bound : Nat) (v : Local) (w : Word)
    (x : Fin bound) (h : (readPacket hash site bound v w).result = .ok x) :
    (readPacket hash site bound v w).state.core.regs 0 = x.val := by
  change typedRead hash site bound v w = .ok x at h
  have hr := congrArg eraseRead h
  rw [typed_erasure] at hr
  change rawRead hash site bound v w = .ok x.val at hr
  have ht : w.val.take 8 = w.val := List.take_of_length_le w.property
  by_cases hw : w.val.length = 8 <;>
    by_cases hv : Zkc.Realization.ByteEncoding.valueBE w.val < bound <;>
    simp [rawRead,rawReply,readPacket,update,readInstr,
      request,inputBytes,effect,ht,hw,hv,stateOf,eventsOf,put] at hr ⊢
  exact hr

def onRead {X : Type} {bound : Nat} (p : ReadPacket bound) (k : Fin bound → Local → X) :
    Except Exit X × Local × List Event :=
  (p.result.map (fun x => k x p.state),p.state,p.events)

theorem onRead_error_retains_state {X : Type} {bound : Nat} (p : ReadPacket bound)
    (k : Fin bound → Local → X) (why : Exit) (h : p.result = .error why) :
    onRead p k = (.error why,p.state,p.events) := by
  simp only [onRead,h]
  rfl

theorem continueRead_packet {X : Type} (hash : Hash) (site bound : Nat) (v : Local) (w : Word)
    (k : Fin bound → Local → X) :
    (onRead (readPacket hash site bound v w) k).1 = continueRead hash site bound v w k := rfl

end Zkc.Protocols.ScalarBytecode.Endpoint
