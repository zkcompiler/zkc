module

public import Zkc.Core.Program.NamedProgram
public import Zkc.Core.Program.Sites

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

How often an operation can run is read in the same way. `Region.counted` gives, for the body of
one definition, each operation with the product of the written counts of the kept loops around
it: the counts of the draws and of the applications of a definition, which a table of caps
states and a module checks against the stored program. `NamedProgram.occurrences` follows the
applications from a root and gives every site of a coin with its count along the way; it grows
with the number of ways to a draw and not with the program, and is the view that tests compare
a table with.
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

section
variable {Op Who : Type}

/-- The count of the loops around an instruction times a written count; none when a count that
is read at run time, or an attempt, stands around it. -/
def timesMore : Option Nat → Repeat → Option Nat
  | some times, .fixed n => some (times * n)
  | _, _ => none

mutual
  /-- The operations of an instruction, each with its key and how often it can run in one run
  of the instruction, given how often the instruction runs: the product of the written counts
  of the loops around it. A block of a stepped loop runs once; under a loop whose count is read
  at run time, and in an attempt, there is no count. -/
  def Instruction.counted : Instruction Op Who → Option Nat → List (Key × Op × Option Nat)
    | .op key _ o _, times => [(key, o, times)]
    | .guard .., _ => []
    | .choose _ _ _ _ onTrue onFalse, times => onTrue.counted times ++ onFalse.counted times
    | .cases _ _ _ _ arms, times => Region.countedAll arms times
    | .loop _ _ count _ _ body, times => body.counted (timesMore times count)
    | .block _ _ _ body, times => body.counted times
    | .attempt _ _ _ body, _ => body.counted none
  /-- The counted operations of a region. -/
  def Region.counted : Region Op Who → Option Nat → List (Key × Op × Option Nat)
    | .mk _ body _, times => Instruction.countedAll body times
  def Instruction.countedAll : List (Instruction Op Who) → Option Nat →
      List (Key × Op × Option Nat)
    | [], _ => []
    | instruction :: rest, times =>
      instruction.counted times ++ Instruction.countedAll rest times
  def Region.countedAll : List (Region Op Who) → Option Nat → List (Key × Op × Option Nat)
    | [], _ => []
    | region :: rest, times => region.counted times ++ Region.countedAll rest times
end

end

variable {V : Vocabulary}

/-- The sites of the coins that a run of a definition can reach, below the applications
`through` and given how often the definition runs, each with how often it can occur on one
path. An application is entered into the definition that it applies, with its key added to the
way. `depth` bounds the applications entered: a definition applies only earlier ones, so the
number of definitions of a program is enough. -/
def NamedProgram.occurrencesFrom (p : NamedProgram V) :
    Nat → Key → List Key → Option Nat → List (Site × Option Nat)
  | 0, _, _, _ => []
  | depth + 1, definition, through, times =>
    match p.definitions.find? (·.key == definition) with
    | some (.protocol _ _ _ _ body) =>
      (body.counted times).flatMap fun (key, operation, count) =>
        match operation with
        | .event (.given (.coin _) _ _) _ => [(⟨through, key⟩, count)]
        | .apply callee _ => p.occurrencesFrom depth callee (through ++ [key]) count
        | _ => []
    | _ => []

/-- **How often each draw can occur.** The sites of the coins that a run of a root can reach,
each with how often it can occur on one path of the run: the product of the written counts of
the loops around the draw, along the applications. A site under a loop whose count is read at
run time, or in an attempt, has no count. -/
def NamedProgram.occurrences (p : NamedProgram V) (root : Key) : List (Site × Option Nat) :=
  p.occurrencesFrom p.definitions.length root [] (some 1)

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
