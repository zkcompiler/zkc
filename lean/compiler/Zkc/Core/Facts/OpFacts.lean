module

public import Zkc.Core.Program.Term
public import Zkc.Core.Program.Requirement
public import Zkc.Core.Value.Skeleton

@[expose] public section

/-!
What the analysis is told about the operations of a dialect: the one description of them.

The analysis walks a term of any dialect. Every operation has a written form, and what the
analysis knows of it (what it requires, the ranges of its results, how its result reads) is said
once per written form. Whether equal applications of an operation are one value is a separate
part: a shared operation is a value, and every other operation is kept in order; both have
requirements. A dialect says how its operations are written, which are shared, which written
operations commute, where the table places them, the range of a natural of each of its types,
and which of its types have no value (`FactRules`). The value form reads a part of it, the
written forms of the shared operations (`FactRules.values`).
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
  /-- How an application of an operation reads: its written form, for every operation. What
  the operation requires is said of it (`ops.requires`). -/
  written : ∀ {ins res : List D.Ty}, D.Op ins res → Raw
  /-- Whether equal applications of the operation are one value: it gives the same results on
  the same operands, asks nothing of the world, and stops only `undefined`. Such an operation
  has no place of its own in the order of a term. An operation that is not shared is kept in
  order: one whose results are new each time, that asks for a reply, or that can stop with a
  reason. -/
  shared : ∀ {ins res : List D.Ty}, D.Op ins res → Bool
  /-- Whether the table places the two operands of a written operation in one order. It may be
  said only of an operation whose result does not depend on their order; an analysis that
  learns the operands in order does not say it of every such operation. -/
  commutes : Raw → Bool
  /-- What the type alone says of a natural of the type. -/
  range : D.Ty → Option Range
  /-- Whether a type has no value. -/
  noValue : D.Ty → Bool
  /-- What the analysis knows of the written operations: what each requires, the ranges of its
  results, how its result reads. -/
  ops : OpFacts Raw
  /-- A number for a written operation, by which the table places its applications. -/
  place : Raw → Nat

/-- The rules as the value form reads them: the written form of an operation that is shared. -/
def FactRules.values {D : Dialect} {Raw : Type} (rules : FactRules D Raw) : ValueRules D Raw where
  written := fun o => if rules.shared o then some (rules.written o) else none
  place := rules.place
  commutes := rules.commutes

section
variable {D : Dialect} {Raw : Type} (rules : FactRules D Raw) {ins res : List D.Ty}
  {o : D.Op ins res}

/-- The value form reads a shared operation by its written form. -/
theorem FactRules.values_written_shared (shared : rules.shared o = true) :
    rules.values.written o = some (rules.written o) := by
  simp only [FactRules.values, shared, ↓reduceIte]

/-- The value form reads nothing of an operation that is kept in order. -/
theorem FactRules.values_written_kept (kept : rules.shared o = false) :
    rules.values.written o = none := by
  simp only [FactRules.values, kept, Bool.false_eq_true, ↓reduceIte]

end

end Zkc.Core
