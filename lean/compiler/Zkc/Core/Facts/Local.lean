module

public import Zkc.Core.Facts.State
public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
What the check of facts knows of the written operations of a function, and what the local
dialect tells it.

Per written operation: what it requires (the table of requirements), the ranges of its natural
results from those of its operands (the table of ranges of arithmetic), and how its result
reads. One value for `LocalRaw V`: a role program's computations are local operations and read
it too. Every operation of a function computes, by its written form.
-/

namespace Zkc.Core

namespace Range

/-- The ranges of a sum. -/
def add : Option Range → Option Range → Option Range
  | some a, some b => some ⟨a.lo + b.lo, match a.hi, b.hi with
      | some x, some y => some (x + y)
      | _, _ => none⟩
  | _, _ => none

/-- The ranges of a difference, not below zero. -/
def sub : Option Range → Option Range → Option Range
  | some a, some b => some ⟨match b.hi with | some y => a.lo - y | none => 0, a.hi.map (· - b.lo)⟩
  | _, _ => none

/-- The ranges of a product. -/
def mul : Option Range → Option Range → Option Range
  | some a, some b => some ⟨a.lo * b.lo, match a.hi, b.hi with
      | some x, some y => some (x * y)
      | _, _ => none⟩
  | _, _ => none

/-- The ranges of a quotient rounded down, where the divisor is at least one. -/
def div : Option Range → Option Range → Option Range
  | some a, some b => some ⟨match b.hi with | some y => a.lo / y | none => 0,
      a.hi.map (· / max b.lo 1)⟩
  | _, _ => none

/-- The ranges of a remainder, where the divisor is at least one. -/
def rem : Option Range → Option Range → Option Range
  | some a, some b => some ⟨0, match a.hi, b.hi with
      | some x, some y => some (min x (y - 1))
      | some x, none => some x
      | none, some y => some (y - 1)
      | none, none => none⟩
  | _, _ => none

/-- The ranges of a power: a number to the power zero is one. -/
def pow : Option Range → Option Range → Option Range
  | some a, some b =>
      some ⟨if 1 ≤ a.lo then a.lo ^ b.lo else if b.hi = some 0 then 1 else 0,
        match a.hi, b.hi with
        | some x, some y => some (max (x ^ y) (if b.lo = 0 then 1 else 0))
        | _, _ => none⟩
  | _, _ => none

end Range

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

/-- The range of the result of an operation on two naturals, from those of its operands. -/
def Range.onTwo (f : Option Range → Option Range → Option Range) :
    List (Option Range) → List (Option Range)
  | [a, b] => [f a b]
  | _ => []

/-- The range of the result of an operation that returns its one operand. -/
def Range.onOne : List (Option Range) → List (Option Range)
  | [a] => [a]
  | _ => []

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

variable (V) in
/-- What the local dialect tells the check of facts: every operation of a function computes, by
its written form. -/
def localFactRules (fns : List (FnHeader V)) : FactRules (localDialect V fns) (LocalRaw V) where
  written := fun o => some (LocalOp.print o)
  range := localRange
  ops := localOpFacts V

end

end Zkc.Core
