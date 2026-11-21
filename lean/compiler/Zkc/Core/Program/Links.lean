module

public import Zkc.Core.Program.NamedProgram

@[expose] public section

/-!
What a stored program links of its vocabulary: the rows that its operations name, and the laws
of the coins that it draws.

A model gives a meaning to every row and a support to every law. Whether it gives the intended
one to those that a program uses is a question about the program: a result stated over a model
says what a reader takes it to say only of a program whose rows the model interprets. The rows
and the laws are read here from the program by names, before any typing, by a fold that enters
every region: the arms of a choice and of a case, the body of a loop, of a block and of an
attempt.
-/

namespace Zkc.Core

section
variable {Op Who : Type}

mutual
  /-- The operations of an instruction, in order, with those of every region inside it. -/
  def Instruction.operations : Instruction Op Who → List Op
    | .op _ _ o _ => [o]
    | .guard .. => []
    | .choose _ _ _ _ onTrue onFalse => onTrue.operations ++ onFalse.operations
    | .cases _ _ _ _ arms => Region.operationsOfAll arms
    | .loop _ _ _ _ _ body => body.operations
    | .block _ _ _ body => body.operations
    | .attempt _ _ _ body => body.operations
  /-- The operations of a region. -/
  def Region.operations : Region Op Who → List Op
    | .mk _ body _ => Instruction.operationsOfAll body
  def Instruction.operationsOfAll : List (Instruction Op Who) → List Op
    | [] => []
    | instruction :: rest => instruction.operations ++ Instruction.operationsOfAll rest
  def Region.operationsOfAll : List (Region Op Who) → List Op
    | [] => []
    | region :: rest => region.operations ++ Region.operationsOfAll rest
end

end

variable {V : Vocabulary}

/-- The row that an operation of a function names, when it names one. -/
def LocalRaw.rowKey? : LocalRaw V → Option V.RowKey
  | .row key => some key
  | _ => none

/-- The row that an operation of a protocol names: the row of a computation. -/
def ProtocolRaw.rowKey? : ProtocolRaw V → Option V.RowKey
  | .compute _ o => o.rowKey?
  | _ => none

/-- The law of a coin that an operation of a protocol draws, with the type of its reply. -/
def ProtocolRaw.law? : ProtocolRaw V → Option (V.LawKey × V.Ty)
  | .event (.given (.coin law) _ _) τ => some (law, τ)
  | _ => none

/-- The rows of the vocabulary that a definition names, in the order of its text, a row once for
each place that names it. -/
def Definition.rows : Definition V → List V.RowKey
  | .fn _ _ _ _ _ _ body _ => body.operations.filterMap LocalRaw.rowKey?
  | .protocol _ _ _ _ body => body.operations.filterMap ProtocolRaw.rowKey?

/-- The laws of the coins that a definition draws, each with the type of its reply. -/
def Definition.laws : Definition V → List (V.LawKey × V.Ty)
  | .fn .. => []
  | .protocol _ _ _ _ body => body.operations.filterMap ProtocolRaw.law?

/-- The rows of the vocabulary that a program links: those that its definitions name. -/
def NamedProgram.rows (p : NamedProgram V) : List V.RowKey :=
  p.definitions.flatMap Definition.rows

/-- The laws of the coins that a program draws, each with the type of its reply. -/
def NamedProgram.laws (p : NamedProgram V) : List (V.LawKey × V.Ty) :=
  p.definitions.flatMap Definition.laws

end Zkc.Core
