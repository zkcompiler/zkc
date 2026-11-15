module

public import Zkc.Core.Program.ElaborateLocal

@[expose] public section

/-!
The printed form of a typed program: its definitions in order, each value named by its level.
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

/-- The printed form of a protocol. -/
def printProtocol {hs : Headers V} (hdr : ProtocolHeader V) (body : Prot V hs hdr) : Definition V :=
  .protocol hdr.key hdr.roles hdr.ins hdr.outs
    (printRegion (fun o => ProtocolOp.print o) (fun w => w) body)

/-- The printed definitions of a program, in order. -/
def Defs.print : {hs : Headers V} → Defs V hs → List (Definition V)
  | _, .nil => []
  | _, .fn hdr body _ rest => rest.print ++ [printFn hdr body]
  | _, .protocol hdr body _ rest => rest.print ++ [printProtocol hdr body]

/-- The printed form of a typed program: each value has its level as its name. -/
def print (p : Typed V) : NamedProgram V := ⟨p.defs.print⟩

end

end Zkc.Core
