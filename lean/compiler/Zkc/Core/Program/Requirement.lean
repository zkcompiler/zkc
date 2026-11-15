module

@[expose] public section

/-!
What an operation with a domain asks of an application, as data. The same requirement is what
an operation asks, what the check of facts decides, and what a refusal says when it is not
known.
-/

namespace Zkc.Core

/-- What is known of a natural: it is at least `lo` and, when `hi` is there, at most `hi`. -/
structure Range where
  lo : Nat
  hi : Option Nat
deriving DecidableEq, Repr

/-- A value that a requirement speaks of: an operand of the application by its position, or the
first result of a written operation applied to operands of the application (a length, the truth
value of the row that decides a domain). -/
inductive Operand (Raw : Type) where
  | arg (position : Nat)
  | apply (written : Raw) (positions : List Nat)
deriving DecidableEq

/-- What an application must satisfy to be inside the domain of its operation. -/
inductive Requirement (Raw : Type) where
  /-- The first is at most the second. -/
  | le (first second : Operand Raw)
  /-- The first is less than the second. -/
  | lt (first second : Operand Raw)
  /-- The value is at least a number. -/
  | atLeast (value : Operand Raw) (number : Nat)
  /-- The value is below a number. -/
  | below (value : Operand Raw) (number : Nat)
  /-- The value is a number. -/
  | exactly (value : Operand Raw) (number : Nat)
  /-- The first less the second is a number. -/
  | difference (first second : Operand Raw) (number : Nat)
  /-- The value is true. -/
  | holds (value : Operand Raw)
  /-- The value has an upper bound. -/
  | bounded (value : Operand Raw)
deriving DecidableEq

/-- The values that a requirement names, in its order. -/
def Requirement.operands {Raw : Type} : Requirement Raw → List (Operand Raw)
  | .le t u => [t, u]
  | .lt t u => [t, u]
  | .atLeast t _ => [t]
  | .below t _ => [t]
  | .exactly t _ => [t]
  | .difference t u _ => [t, u]
  | .holds t => [t]
  | .bounded t => [t]

end Zkc.Core
