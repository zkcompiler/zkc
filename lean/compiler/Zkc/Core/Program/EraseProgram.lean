module

public import Zkc.Core.Program.ElaborateLocal
public import Zkc.Core.Program.ElaborateProtocol

@[expose] public section

/-!
The program by names of a typed program: its erasure. Its definitions are in order, each with
its header, a function's summary among it, and the erased form of its body, which has the names
of its inputs and the names that its body binds.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The erased definitions of a program, in order, each with its header. -/
def Defs.erase : {hs : Headers V} → Defs V hs → List (Definition V)
  | _, .nil => []
  | _, .fn hdr inputs body _ rest notes =>
      rest.erase ++
        [.fn hdr.key hdr.ins hdr.outs hdr.canStop hdr.kernel hdr.summary (eraseFn inputs body) notes]
  | _, .protocol hdr inputs body _ rest =>
      rest.erase ++ [.protocol hdr.key hdr.roles hdr.ins hdr.outs (eraseProtocol inputs body)]

/-- The program by names of a typed program: its erasure. -/
def erase (p : Typed V) : NamedProgram V := ⟨p.defs.erase⟩

end

end Zkc.Core
