module

public import Zkc.IR.Source.Structured.Vocabulary
public import Zkc.Program.Source.Participant

@[expose] public section

/-! Typed service signatures. A scalar index request and a block request are
different operations; their bounds and counts are actual ordered SSA operands.
This signature grants no distribution or provider implementation. -/
set_option autoImplicit false
namespace Zkc.Source.Structured

inductive ServiceOp where
  | draw (field : String)
  | sampleIndex (contract : String)
  | sampleIndices (contract : String)
  deriving DecidableEq, Repr

def ServiceOp.contract : ServiceOp → String
  | .draw field => "random." ++ field ++ "/0"
  | .sampleIndex contract | .sampleIndices contract => contract

def ServiceOp.method : ServiceOp → String
  | .draw _ => "draw"
  | .sampleIndex _ => "index"
  | .sampleIndices _ => "indices"

abbrev ServiceOp.arguments (operation : ServiceOp) : List Ty :=
  .service operation.contract :: match operation with
    | .draw _ => []
    | .sampleIndex _ => [.index]
    | .sampleIndices _ => [.index, .index]

abbrev ServiceOp.result : ServiceOp → Ty
  | .draw field => .field field
  | .sampleIndex _ => .index
  | .sampleIndices _ => .indices

abbrev services : Participant.Services Ty where
  Op := ServiceOp
  arguments := ServiceOp.arguments
  result := ServiceOp.result

end Zkc.Source.Structured
