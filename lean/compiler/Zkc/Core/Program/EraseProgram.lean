module

public import Zkc.Core.Program.ElaborateLocal

@[expose] public section

/-!
The program by names of a typed program: its erasure. Its definitions are in order, each with
its header, a function's summary among it, and the erased form of its body, which has the names
of its inputs and the names that its body binds.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- What is written for an operation of a protocol. -/
def ProtocolOp.print {hs : Headers V} {ins res : List (LTy V)} :
    ProtocolOp V hs ins res → ProtocolRaw V
  | .compute R o _ _ _ => .compute R (LocalOp.print o)
  | .flow (τ := τ) kind giver getters _ _ => .event (.flow kind giver getters) τ
  | .given kind owner hearers _ τ _ _ _ => .event (.given kind owner hearers) τ
  | .narrow R _ => .narrow R
  | .apply (hdr := hdr) _ roles _ _ _ _ => .apply hdr.key roles

/-- The erased form of a protocol's body: the names of its ports, its instructions and its
exit. -/
def eraseProtocol {hs : Headers V} {hdr : ProtocolHeader V} (inputs : Names hdr.ins)
    (body : Prot V hs hdr inputs) : Region (ProtocolRaw V) (List Role) :=
  let erased := eraseBody (fun o => ProtocolOp.print o) (fun w => w) body
  .mk inputs.toList erased.1 erased.2

/-- The erased definitions of a program, in order, each with its header. -/
def Defs.erase : {hs : Headers V} → Defs V hs → List (Definition V)
  | _, .nil => []
  | _, .fn hdr inputs body _ rest =>
      rest.erase ++
        [.fn hdr.key hdr.ins hdr.outs hdr.canStop hdr.kernel hdr.summary (eraseFn inputs body)]
  | _, .protocol hdr inputs body _ rest =>
      rest.erase ++ [.protocol hdr.key hdr.roles hdr.ins hdr.outs (eraseProtocol inputs body)]

/-- The program by names of a typed program: its erasure. -/
def erase (p : Typed V) : NamedProgram V := ⟨p.defs.erase⟩

end

end Zkc.Core
