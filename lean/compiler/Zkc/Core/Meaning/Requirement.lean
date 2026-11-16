module

public import Zkc.Core.Program.Requirement

@[expose] public section

/-!
What a requirement says of values.

A requirement (`Program/Requirement.lean`) names values: operands of an application by their
positions, or the first result of a written operation applied to some of them. How a value
reads, as a natural or as a truth value, is a `Reading`; what a written operation gives on
operands is a relation `Run`. Both are given by the dialect. A requirement holds of the values of
an application's operands when the values that it names are there and it says of them what is
true (`Requirement.Holds`). Nothing here depends on an analysis: this is the language in which an
operation states its domain, and in which a definition states what it requires and what it
guarantees (`Summary`, `Evidence/Summary.lean`).
-/

namespace Zkc.Core

/-- How a value reads: as a natural, as a truth value; nothing for a value that is not one. -/
structure Reading (Val : Type) where
  nat : Val → Option Nat
  bool : Val → Option Bool

section
variable {Val : Type} {Raw : Type}

/-- The value that an operand of a requirement names, among the operands' values. -/
def Operand.Denotes (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    Operand Raw → Val → Prop
  | .arg position, v => args[position]? = some v
  | .apply written positions, v => ∃ operands rs, atPositions args positions = some operands ∧
      Run written operands rs ∧ rs.head? = some v

/-- The values that operands name, in order. -/
def DenotesAll (Run : Raw → List Val → List Val → Prop) (args : List Val) :
    List (Operand Raw) → List Val → Prop
  | [], [] => True
  | o :: os, v :: vs => Operand.Denotes Run args o v ∧ DenotesAll Run args os vs
  | _, _ => False

/-- What a requirement says of the values it names: an order, a bound, a number, a truth
value. -/
def Requirement.Relation (R : Reading Val) : Requirement Raw → List Val → Prop
  | .le .., [a, b] => ∀ x y, R.nat a = some x → R.nat b = some y → x ≤ y
  | .lt .., [a, b] => ∀ x y, R.nat a = some x → R.nat b = some y → x < y
  | .atLeast _ n, [a] => ∀ x, R.nat a = some x → n ≤ x
  | .below _ n, [a] => ∀ x, R.nat a = some x → x < n
  | .exactly _ n, [a] => ∀ x, R.nat a = some x → x = n
  | .difference _ _ n, [b, a] => ∀ x y, R.nat b = some x → R.nat a = some y → x - y = n
  | .holds _, [a] => R.bool a = some true
  | .bounded _, [a] => ∃ x, R.nat a = some x
  | _, _ => False

/-- A requirement holds of the operands' values: the values it names are there, and it says
of them what is true. -/
def Requirement.Holds (Run : Raw → List Val → List Val → Prop) (R : Reading Val)
    (args : List Val) (requirement : Requirement Raw) : Prop :=
  ∃ vs, DenotesAll Run args requirement.operands vs ∧ requirement.Relation R vs

end

end Zkc.Core
