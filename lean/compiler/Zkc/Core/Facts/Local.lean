module

public import Zkc.Core.Facts.State
public import Zkc.Core.Program.LocalRules

@[expose] public section

/-!
What the analysis knows of the written operations of a function, and what the local dialect
tells it.

Per written operation: what it requires (the table of requirements), what it guarantees of its
operands and results, the ranges of its natural results from those of its operands (the table of
ranges of arithmetic), and how its result reads. One value for `LocalRaw V` against the headers
of the callees: a role program's computations are local operations and read it too. An operation
that the core owns is described by one table, from its name to the parts of its contract
(`ownedContract`): what it requires, what it guarantees, the ranges of its results, how its first
result reads, and whether the table places its operands in one order; the analysis reads every
part of it there (`localOpFacts`, `LocalRaw.commutes`). No operation that the core owns guarantees
anything yet. A call requires and guarantees what the summary of its callee's header says
(`summaryOf`), so that the analysis decides the callee's requirements at the call and learns its
guarantees. Every operation of a function is written as it is printed, and has the requirements
of that written form; every one is shared, a value, except a call of a function that can stop
with a reason, which is kept in order. The sum and the product of naturals and the equalities
commute; the conjunction and the disjunction, whose meaning is symmetric too, keep the order
written, since the check of facts learns their operands in that order; a row of the vocabulary
and a call do not commute (`localFactRules`).
What following decides for a function is what the rules of its elaboration give
(`(localRules fns).skel`, `Rules.skel`): types and performers by equality, and two operations by
their written forms.
-/

namespace Zkc.Core

section
variable {V : Vocabulary}

/-- The written length of a sequence of the type. -/
def lengthOfType (τ : V.Ty) : LocalRaw V := .owned .seqLength [τ] []

/-- What a row requires: a restricted one, its domain row at the same operands known true. -/
def rowRequires (key : V.RowKey) : List (Requirement (LocalRaw V)) :=
  match V.row key with
  | some signature =>
      match signature.kind with
      | .pure => []
      | .restricted domain => [.holds (.apply (.row domain) (List.range signature.ins.length))]
  | none => []

/-- What the data of a literal says of its natural. -/
def literalRanges : V.Ty → List Nat → List (Option Range)
  | .nat, [n] => [some (Range.point n)]
  | .fin _, [n] => [some (Range.point n)]
  | _, _ => []

variable (V) in
/-- The parts of the contract of an operation that the core owns, as the analysis reads them. -/
structure OwnedContract where
  /-- What an application requires, by its operands' positions, from the types written with the
  name. -/
  requires : List V.Ty → List (Requirement (LocalRaw V))
  /-- What holds of its operands followed by its results where its requirements hold, by
  position, from the types written with the name. -/
  ensures : List V.Ty → List (Requirement (LocalRaw V))
  /-- The ranges of its natural results from those of its operands, from the types written with
  the name. -/
  ranges : List V.Ty → List (Option Range) → List (Option Range)
  /-- How its first result reads. -/
  form : Option ResultForm
  /-- Whether the table places its two operands in one order, the smaller identifier first,
  whichever way they were written. -/
  commutes : Bool

/-- The contract of each operation that the core owns: what an application requires (the table of
requirements), what it guarantees of its operands and results (nothing yet, for every one), the
ranges of its natural results from those of its operands (the table of ranges of arithmetic), how
its first result reads, and whether the table places its operands in one order.

The operands are placed in one order for the sum and the product of naturals, and the equality of
naturals and of truth values, each of which gives, on two operands of one type, a result that does
not depend on their order, for all values (`Meaning/Local.lean`). An equality of naturals, learned
true or false, teaches the check of facts the same in either order, since both sides are read
before either is learned (`Known.pushEqual`, `Known.pushDifferent`); the equality of truth values
has no form, and teaches nothing. Not the conjunction and the disjunction of truth values: their
meaning is symmetric, but the check of facts learns the operands of a conjunction learned true,
and of a disjunction learned false, one after the other in the order of the table's entry
(`assume`, `Facts/State.lean`), and what the second teaches can depend on what the first taught
(`Known.pushLess` reads the number of the other side when it learns); so their operands are
placed, and learned, in the order written, as the source's `and` and `or` are. Not the
difference, the quotient, the remainder, the power or the order of naturals; not a
concatenation, nor a sequence, a tuple or a record made of two values of one type, whose order is
in the result. -/
def ownedContract : OwnedName → OwnedContract V
  | .natAdd =>
      { requires := fun _ => [], ensures := fun _ => [],
        ranges := fun _ => Range.onTwo Range.add, form := some .sum, commutes := true }
  | .natSub =>
      { requires := fun _ => [.le (.arg 1) (.arg 0)], ensures := fun _ => [],
        ranges := fun _ => Range.onTwo Range.sub, form := some .difference, commutes := false }
  | .natMul =>
      { requires := fun _ => [], ensures := fun _ => [],
        ranges := fun _ => Range.onTwo Range.mul, form := none, commutes := true }
  | .natDiv =>
      { requires := fun _ => [.atLeast (.arg 1) 1], ensures := fun _ => [],
        ranges := fun _ => Range.onTwo Range.div, form := none, commutes := false }
  | .natRem =>
      { requires := fun _ => [.atLeast (.arg 1) 1], ensures := fun _ => [],
        ranges := fun _ => Range.onTwo Range.rem, form := none, commutes := false }
  | .natPow =>
      { requires := fun _ => [], ensures := fun _ => [],
        ranges := fun _ => Range.onTwo Range.pow, form := none, commutes := false }
  | .natEqual =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [],
        form := some .equal, commutes := true }
  | .natLess =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [],
        form := some .less, commutes := false }
  | .boolAnd =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [],
        form := some .conjunction, commutes := false }
  | .boolOr =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [],
        form := some .disjunction, commutes := false }
  | .boolNot =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [],
        form := some .negation, commutes := false }
  | .boolEqual =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := true }
  | .seqLength =>
      { requires := fun _ => []
        ensures := fun _ => []
        ranges := fun
          | [.seq _ (some size)] => fun _ => [some (Range.point size)]
          | [.seq _ none] => fun _ => [some ⟨0, none⟩]
          | _ => fun _ => []
        form := none, commutes := false }
  | .seqAt =>
      { requires := fun
          | [.seq _ (some size)] => [.below (.arg 1) size]
          | [.seq item none] => [.lt (.arg 1) (.apply (lengthOfType (.seq item none)) [0])]
          | _ => []
        ensures := fun _ => [], ranges := fun _ _ => [], form := none, commutes := false }
  | .seqSlice =>
      { requires := fun
          | [.seq item size, .seq _ result] =>
              [.le (.arg 1) (.arg 2), .le (.arg 2) (.apply (lengthOfType (.seq item size)) [0])] ++
                (match result with
                  | some count => [.difference (.arg 2) (.arg 1) count]
                  | none => [])
          | _ => []
        ensures := fun _ => [], ranges := fun _ _ => [], form := none, commutes := false }
  | .seqConcat =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }
  | .seqFill =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }
  | .seqSized =>
      { requires := fun
          | [.seq item (some size)] => [.exactly (.apply (lengthOfType (.seq item none)) [0]) size]
          | _ => []
        ensures := fun _ => [], ranges := fun _ _ => [], form := none, commutes := false }
  | .natBelow =>
      { requires := fun
          | [.fin bound] => [.below (.arg 0) bound]
          | _ => []
        ensures := fun _ => [], ranges := fun _ => Range.onOne, form := none, commutes := false }
  | .seqUnsized =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }
  | .finToNat =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ => Range.onOne,
        form := none, commutes := false }
  | .finWiden =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ => Range.onOne,
        form := none, commutes := false }
  | .make =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }
  | .get =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }
  | .take =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }
  | .variant =>
      { requires := fun _ => [], ensures := fun _ => [], ranges := fun _ _ => [], form := none,
        commutes := false }

/-- The summary of the first header with the key; the empty summary when no header has it. -/
def summaryOf (key : Key) : List (FnHeader V) → Summary (LocalRaw V)
  | [] => Summary.empty
  | hdr :: rest => if hdr.key = key then hdr.summary else summaryOf key rest

/-- Among headers with distinct keys, the summary with the key of a header is that header's. -/
theorem summaryOf_member : ∀ {fns : List (FnHeader V)} {hdr : FnHeader V},
    (fns.map (·.key)).Nodup → Member fns hdr → summaryOf hdr.key fns = hdr.summary
  | _ :: _, _, _, .head => by simp only [summaryOf, ↓reduceIte]
  | other :: rest, hdr, distinct, .tail callee => by
      have notIn : other.key ∉ rest.map (·.key) := (List.nodup_cons.mp distinct).1
      have listed : hdr.key ∈ rest.map (·.key) := Member.key_mem (·.key) callee
      have apart : other.key ≠ hdr.key := fun same => notIn (same ▸ listed)
      simp only [summaryOf, apart, ↓reduceIte]
      exact summaryOf_member (List.nodup_cons.mp distinct).2 callee

/-- What the check of facts knows of the written operations of a function, against the headers
of its callees: of an operation that the core owns, what its contract says (`ownedContract`); of a
row, what its domain row says (`rowRequires`); of a call, what the summary of the header with the
callee's key requires and guarantees (`summaryOf`), nothing when no header has it; of a literal,
its natural (`literalRanges`), and a written truth value reads as itself. A row and a literal
guarantee nothing. -/
def localOpFacts (fns : List (FnHeader V)) : OpFacts (LocalRaw V) where
  requires
    | .owned name types _ => (ownedContract name).requires types
    | .row key => rowRequires key
    | .call key => (summaryOf key fns).requires
    | .literal .. => []
  ensures
    | .owned name types _ => (ownedContract name).ensures types
    | .call key => (summaryOf key fns).ensures
    | .row _ => []
    | .literal .. => []
  ranges
    | .owned name types _, operands => (ownedContract name).ranges types operands
    | .literal τ data, _ => literalRanges τ data
    | _, _ => []
  form
    | .owned name _ _ => (ownedContract (V := V) name).form
    | .literal .bool [0] => some (.truth false)
    | .literal .bool [1] => some (.truth true)
    | _ => none

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

/-- Whether a written operation of a function commutes: an operation that the core owns, as it
is written (with no types and no numbers), when its contract says so (`ownedContract`). A row of
the vocabulary does not commute here, whatever a model does: that a row commutes would be a law
that every model must satisfy, which needs the model and is a later piece. A call does not
commute: nothing says that the callee's result does not depend on the order of its inputs. -/
def LocalRaw.commutes : LocalRaw V → Bool
  | .owned name [] [] => (ownedContract (V := V) name).commutes
  | .owned _ (_ :: _) _ => false
  | .owned _ [] (_ :: _) => false
  | .row _ => false
  | .literal _ _ => false
  | .call _ => false

variable (V) in
/-- What the local dialect tells the analysis: every operation of a function is written as it is
printed; every one is shared, a value, except a call of a function that can stop with a reason,
which is kept in order; the sum and the product of naturals and the equalities commute
(`LocalRaw.commutes`). -/
def localFactRules (fns : List (FnHeader V)) : FactRules (localDialect V fns) (LocalRaw V) where
  written := fun o => LocalOp.print o
  shared := fun o => !LocalOp.canStop o
  commutes := LocalRaw.commutes
  range := localRange
  noValue := Ty.noValue
  ops := localOpFacts fns
  place := localPlace

end

end Zkc.Core
