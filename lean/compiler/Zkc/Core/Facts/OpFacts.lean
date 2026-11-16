module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.Requirement
public import Zkc.Core.Value.Skeleton

@[expose] public section

/-!
What the analysis is told about the operations of a dialect: the one description of them.

The analysis walks a term of any dialect. Of an operation it reads its written form: an operation
that is a value is shared by it, and what the analysis knows of it (what it requires, the ranges
of its results, how its result reads) is said once per written form, for every dialect whose
operations compute. A dialect says which of its operations are values and how they are written,
which written operations commute, where the table places them, the range of a natural of each of
its types, and which of its types have no value (`FactRules`). The value form reads a part of
it (`FactRules.values`).
-/

namespace Zkc.Core

/-- How the check reads the first result of a written operation: these are the forms that its
rules name. -/
inductive ResultForm where
  /-- The sum of its two operands. -/
  | sum
  /-- The first operand less the second. -/
  | difference
  /-- Whether the first operand is less than the second. -/
  | less
  /-- Whether its two operands are equal naturals. -/
  | equal
  /-- The negation of its operand. -/
  | negation
  /-- The conjunction of its two operands. -/
  | conjunction
  /-- The disjunction of its two operands. -/
  | disjunction
  /-- A truth value that is written. -/
  | truth (value : Bool)
deriving DecidableEq, Repr

/-- What the check knows of written operations. -/
structure OpFacts (Raw : Type) where
  /-- What an application must satisfy to be inside the operation's domain; nothing for an
  operation without one. -/
  requires : Raw → List (Requirement Raw)
  /-- What is known of each result from what is known of each operand, beyond what the
  result's type says: a range for a natural, nothing otherwise. -/
  ranges : Raw → List (Option Range) → List (Option Range)
  /-- How the first result reads. -/
  form : Raw → Option ResultForm

/-- What a dialect tells the analysis of its operations. -/
structure FactRules (D : Dialect) (Raw : Type) where
  /-- The written form of an operation that is a value: equal applications of it are one value,
  and it has no place of its own in the order of a term. Nothing for an operation that is kept in
  order: one whose results are new values each time, or that can stop with a reason. -/
  written : ∀ {ins res : List D.Ty}, D.Op ins res → Option Raw
  /-- Whether the result of a written operation of two operands does not depend on their order.
  Such an operation is placed in the table with its operands in one order, whichever way they
  were written. -/
  commutes : Raw → Bool
  /-- What the type alone says of a natural of the type; nothing for a type that is not a
  natural. -/
  range : D.Ty → Option Range
  /-- Whether a type has no value: a region where a value of such a type comes into scope never
  runs. -/
  noValue : D.Ty → Bool
  /-- What the check knows of the written operations. -/
  ops : OpFacts Raw
  /-- A number for a written operation, by which the table places its applications with their
  operands' identifiers: any number will do, since the applications placed together are
  compared whole; operations that it tells apart fall in different places. -/
  place : Raw → Nat

/-- The rules as the value form reads them: which operations are values, how they are written,
where the table places them, and which commute. -/
def FactRules.values {D : Dialect} {Raw : Type} (rules : FactRules D Raw) : ValueRules D Raw where
  written := rules.written
  place := rules.place
  commutes := rules.commutes

end Zkc.Core
