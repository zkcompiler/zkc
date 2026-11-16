module

public import Zkc.Core.Facts.State
public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
What the analysis knows of the written operations of a function, and what the local dialect
tells it.

Per written operation: what it requires (the table of requirements), the ranges of its natural
results from those of its operands (the table of ranges of arithmetic), and how its result
reads. One value for `LocalRaw V`: a role program's computations are local operations and read
it too. Every operation of a function is a value, by its written form, except a call of a
function that can stop with a reason, which is kept in order. The sum and the product of
naturals and the equalities commute (`OwnedName.commutes`); the conjunction and the disjunction,
whose meaning is symmetric too, keep the order written, since the check of facts learns their
operands in that order; a row of the vocabulary and a call do not commute (`localFactRules`).
What following decides for a function is what the rules of its elaboration give
(`(localRules fns).skel`, `Rules.skel`): types and performers by equality, and two operations by
their written forms.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The written length of a sequence of the type. -/
def lengthOfType (τ : V.Ty) : LocalRaw V := .owned .seqLength [τ] []

/-- What an operation that the core owns requires of an application, by its operands'
positions. -/
def ownedRequires : OwnedName → List V.Ty → List (Requirement (LocalRaw V))
  | .natSub, _ => [.le (.arg 1) (.arg 0)]
  | .natDiv, _ => [.atLeast (.arg 1) 1]
  | .natRem, _ => [.atLeast (.arg 1) 1]
  | .seqAt, [.seq _ (some size)] => [.below (.arg 1) size]
  | .seqAt, [.seq item none] => [.lt (.arg 1) (.apply (lengthOfType (.seq item none)) [0])]
  | .seqSlice, [.seq item size, .seq _ result] =>
      [.le (.arg 1) (.arg 2), .le (.arg 2) (.apply (lengthOfType (.seq item size)) [0])] ++
        (match result with
          | some count => [.difference (.arg 2) (.arg 1) count]
          | none => [])
  | .seqSized, [.seq item (some size)] =>
      [.exactly (.apply (lengthOfType (.seq item none)) [0]) size]
  | .natBelow, [.fin bound] => [.below (.arg 0) bound]
  | _, _ => []

/-- What a row requires: a restricted one, its domain row at the same operands known true. -/
def rowRequires (key : V.RowKey) : List (Requirement (LocalRaw V)) :=
  match V.row key with
  | some signature =>
      match signature.kind with
      | .pure => []
      | .restricted domain => [.holds (.apply (.row domain) (List.range signature.ins.length))]
  | none => []

/-- The ranges of the natural results of an operation that the core owns, from those of its
operands. -/
def ownedRanges : OwnedName → List V.Ty → List (Option Range) → List (Option Range)
  | .natAdd, _ => Range.onTwo Range.add
  | .natSub, _ => Range.onTwo Range.sub
  | .natMul, _ => Range.onTwo Range.mul
  | .natDiv, _ => Range.onTwo Range.div
  | .natRem, _ => Range.onTwo Range.rem
  | .natPow, _ => Range.onTwo Range.pow
  | .seqLength, [.seq _ (some size)] => fun _ => [some (Range.point size)]
  | .seqLength, [.seq _ none] => fun _ => [some ⟨0, none⟩]
  | .natBelow, _ => Range.onOne
  | .finToNat, _ => Range.onOne
  | .finWiden, _ => Range.onOne
  | _, _ => fun _ => []

/-- What the data of a literal says of its natural. -/
def literalRanges : V.Ty → List Nat → List (Option Range)
  | .nat, [n] => [some (Range.point n)]
  | .fin _, [n] => [some (Range.point n)]
  | _, _ => []

/-- How the first result of a written operation reads. -/
def localForm : LocalRaw V → Option ResultForm
  | .owned .natAdd _ _ => some .sum
  | .owned .natSub _ _ => some .difference
  | .owned .natLess _ _ => some .less
  | .owned .natEqual _ _ => some .equal
  | .owned .boolNot _ _ => some .negation
  | .owned .boolAnd _ _ => some .conjunction
  | .owned .boolOr _ _ => some .disjunction
  | .literal .bool [0] => some (.truth false)
  | .literal .bool [1] => some (.truth true)
  | _ => none

variable (V) in
/-- What the check of facts knows of the written operations of a function. -/
def localOpFacts : OpFacts (LocalRaw V) where
  requires
    | .owned name types _ => ownedRequires name types
    | .row key => rowRequires key
    | _ => []
  ranges
    | .owned name types _, operands => ownedRanges name types operands
    | .literal τ data, _ => literalRanges τ data
    | _, _ => []
  form := localForm

/-- What the type of a natural says of it. -/
def localRange : V.Ty → Option Range
  | .nat => some ⟨0, none⟩
  | .fin bound => some (if bound = 0 then Range.nothing else ⟨0, some (bound - 1)⟩)
  | _ => none

/-- The number by which the table places the applications of a written operation of a function:
it tells apart the literals by their data, the operations that the core owns by their name and
numbers, and the calls by their callee; the rows share one. -/
def localPlace : LocalRaw V → Nat
  | .row _ => 0
  | .owned name _ numbers => FactCheck.mixNumbers (4 * name.ctorIdx + 1) numbers
  | .literal _ data => FactCheck.mixNumbers 2 data
  | .call callee => 4 * callee.number + 3

/-- Whether the table places the two operands of an operation that the core owns in one order,
the smaller identifier first, whichever way they were written: the sum and the product of
naturals, and the equality of naturals and of truth values, each of which gives, on two operands
of one type, a result that does not depend on their order, for all values (`Meaning/Local.lean`).
An equality of naturals, learned true or false, teaches the check of facts the same in either
order, since both sides are read before either is learned (`Known.pushEqual`,
`Known.pushDifferent`); the equality of truth values has no form, and teaches nothing. Not the
conjunction and the disjunction of truth values: their meaning is symmetric, but the check of
facts learns the operands of a conjunction learned true, and of a disjunction learned false, one
after the other in the order of the table's entry (`assume`, `Facts/State.lean`), and what the
second teaches can depend on what the first taught (`Known.pushLess` reads the number of the
other side when it learns); so their operands are placed, and learned, in the order written, as
the source's `and` and `or` are. Not the difference, the quotient, the remainder, the power or
the order of naturals; not a concatenation, nor a sequence, a tuple or a record made of two
values of one type, whose order is in the result. -/
def OwnedName.commutes : OwnedName → Bool
  | .natAdd | .natMul | .natEqual | .boolEqual => true
  | .boolAnd | .boolOr => false
  | .natSub | .natDiv | .natRem | .natPow | .natLess | .boolNot => false
  | .seqLength | .seqAt | .seqSlice | .seqConcat | .seqFill | .seqSized | .natBelow => false
  | .seqUnsized | .finToNat | .finWiden | .make | .get | .take | .variant => false

/-- Whether a written operation of a function commutes: an operation that the core owns, as it
is written (with no types and no numbers), when `OwnedName.commutes` says so. A row of the
vocabulary does not commute here, whatever a model does: that a row commutes would be a law that
every model must satisfy, which needs the model and is a later piece. A call does not commute:
nothing says that the callee's result does not depend on the order of its inputs. -/
def LocalRaw.commutes : LocalRaw V → Bool
  | .owned name [] [] => name.commutes
  | .owned _ (_ :: _) _ => false
  | .owned _ [] (_ :: _) => false
  | .row _ => false
  | .literal _ _ => false
  | .call _ => false

variable (V) in
/-- What the local dialect tells the analysis: every operation of a function is a value, by its
written form, except a call of a function that can stop with a reason, which is kept in order;
the sum and the product of naturals and the equalities commute (`LocalRaw.commutes`). -/
def localFactRules (fns : List (FnHeader V)) : FactRules (localDialect V fns) (LocalRaw V) where
  written := fun o => bif LocalOp.canStop o then none else some (LocalOp.print o)
  commutes := LocalRaw.commutes
  range := localRange
  noValue := Ty.noValue
  ops := localOpFacts V
  place := localPlace

end

end Zkc.Core
