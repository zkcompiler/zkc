module

public import Zkc.Core.Meaning.Requirement

@[expose] public section

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
  /-- What holds of the operands followed by the results of an application, by position, when
  its requirements hold; nothing for an operation that guarantees nothing. -/
  ensures : Raw → List (Requirement Raw)
  /-- What is known of each result from what is known of each operand, beyond what the
  result's type says: a range for a natural, nothing otherwise. -/
  ranges : Raw → List (Option Range) → List (Option Range)
  /-- How the first result reads. -/
  form : Raw → Option ResultForm

namespace FactCheck
variable {Val : Type}

/-- How a value reads, by the form of the operation that gave it, from its operands. -/
def FormHolds (R : Reading Val) : ResultForm → List Val → Val → Prop
  | .sum, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      R.nat r = some (x + y)
  | .difference, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      y ≤ x ∧ R.nat r = some (x - y)
  | .less, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      R.bool r = some (decide (x < y))
  | .equal, args, r => ∃ a b x y, args = [a, b] ∧ R.nat a = some x ∧ R.nat b = some y ∧
      R.bool r = some (decide (x = y))
  | .negation, args, r => ∃ a x, args = [a] ∧ R.bool a = some x ∧ R.bool r = some (!x)
  | .conjunction, args, r => ∃ a b x y, args = [a, b] ∧ R.bool a = some x ∧
      R.bool b = some y ∧ R.bool r = some (x && y)
  | .disjunction, args, r => ∃ a b x y, args = [a, b] ∧ R.bool a = some x ∧
      R.bool b = some y ∧ R.bool r = some (x || y)
  | .truth value, _, r => R.bool r = some value

end FactCheck

end Zkc.Core
