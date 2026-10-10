import Zkc.Source.Decoding

/-! Structural size of finite source data.

Each constructor counts once, including dormant branches and a loop's body and
suffix. Loop bodies are not unrolled. Operand lists, operation payloads, numeric
encodings and runtime work require separate measures.
-/

set_option autoImplicit false

namespace Zkc.Source

def RawProgram.nodeCount {Ty Op : Type} : RawProgram Ty Op → Nat
  | .ret _ | .stop _ => 1
  | .letOp _ _ next => 1 + next.nodeCount
  | .branch _ yes no => 1 + yes.nodeCount + no.nodeCount
  | .iterate _ _ _ body next => 1 + body.nodeCount + next.nodeCount

end Zkc.Source
