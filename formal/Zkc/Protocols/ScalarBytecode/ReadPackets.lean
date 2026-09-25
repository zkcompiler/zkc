import Zkc.Protocols.ScalarBytecode.Endpoint.Reads

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Protocols.ScalarBytecode.ReadPackets
open Zkc.Realization.InstructionSequence Zkc.Semantics.OperationContract Zkc.Realization.ByteEncoding Zkc.Semantics.Locality Zkc.Protocols.ScalarBytecode.Execution Zkc.Protocols.ScalarBytecode.Endpoint

structure Packet (S : Type) (bound : Nat) where
  result : Except Exit (Fin bound)
  world : World S
  events : List Event

def receive {S : Type} (hash : Hash) (supplier : Supplier S)
    (site bound : Nat) (g : World S) : Packet S bound :=
  let a := supplier.read ⟨g.verifier.subject,site⟩ bound g.external
  let p := readPacket hash site bound g.verifier a.1
  ⟨p.result,⟨p.state,notify supplier g.verifier.subject p.events a.2⟩,p.events⟩

def erase {S : Type} {bound : Nat} (p : Packet S bound) : Step (World S) Event :=
  match p.result with
    | .ok _ => .next p.world p.events
    | .error why => .halt why p.world p.events

theorem receive_erasure {S : Type} (hash : Hash) (supplier : Supplier S)
    (site bound : Nat) (g : World S) :
    erase (receive hash supplier site bound g) =
      openStep hash supplier (readInstr site bound) g := by
  unfold openStep
  change _ = mapStep (fun (v : Local) => (⟨v,notify supplier g.verifier.subject
    (eventsOf (update hash (readInstr site bound)
      (supplier.read ⟨g.verifier.subject,site⟩ bound g.external).1 g.verifier))
      (supplier.read ⟨g.verifier.subject,site⟩ bound g.external).2⟩ : World S))
    (update hash (readInstr site bound)
      (supplier.read ⟨g.verifier.subject,site⟩ bound g.external).1 g.verifier)
  rw [← read_packet_step]
  unfold receive erase
  dsimp only
  generalize readPacket hash site bound g.verifier
    (supplier.read ⟨g.verifier.subject,site⟩ bound g.external).1 = p
  cases hp : p.result <;> simp [erasePacket,hp,mapStep,eventsOf]

def erasedTerminal {S X : Type} (r : Except Exit X × World S × List Event) :
    Terminal (World S) Event :=
  ⟨match r.1 with | .ok _ => .incomplete | .error why => why,r.2.1,r.2.2⟩

end Zkc.Protocols.ScalarBytecode.ReadPackets
