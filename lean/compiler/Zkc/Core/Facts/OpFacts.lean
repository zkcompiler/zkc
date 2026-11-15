module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.Requirement

@[expose] public section

/-!
What the check of facts is told about operations.

The check walks a term of any dialect. Of an operation it reads its written form: an operation
that computes is shared by it, and what the check knows of it (what it requires, the ranges of
its results, how its result reads) is said once per written form, for every dialect whose
operations compute. A dialect says which of its operations compute, and the range of a natural
of each of its types.
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

/-- What a dialect tells the check of facts. -/
structure FactRules (D : Dialect) (Raw : Type) where
  /-- The written form of an operation that computes: equal applications of it are one value.
  Nothing for an operation whose results are new values each time. -/
  written : ∀ {ins res : List D.Ty}, D.Op ins res → Option Raw
  /-- What the type alone says of a natural of the type; nothing for a type that is not a
  natural. -/
  range : D.Ty → Option Range
  /-- What the check knows of the written operations. -/
  ops : OpFacts Raw

end Zkc.Core
