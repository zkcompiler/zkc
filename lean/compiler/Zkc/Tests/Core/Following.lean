import Zkc.Core.Transform.StepSound
import Zkc.Tests.Core.Facts

/-!
Following: whether a function follows the analysis of another, on functions written by names,
elaborated and walked by the kernel.

Each pair is two bodies of a function with the key 1, one header, over the same callees, each
typed against them (`typeFn`); the second follows the analysis of the first (`TypedFn.follows`):
`decided` says whether the second follows with no place that differs, and `safelyFollows` gives
the whole verdict, no place that differs and no refusal. Accepted: a repeated computation shared;
two computations between guards in the other order, with one computation that nothing uses;
computations moved around guards that stay in their order; a computation moved out of a loop; the
same program with other names for its values; a call of a function that cannot stop, shared;
`x + y` against `y + x`, since addition commutes, and `x == y` against `y == x`, of naturals and
of truth values, since an equality commutes; a product and a sum with their operands exchanged
inside a loop after a guard. Refused: `x - y` against `y - x`; `(x + y) + z` against
`x + (y + z)` (associativity is not a law that following knows); a row of the vocabulary with its
operands exchanged; a conjunction with its operands exchanged, since the check of facts learns
them in the order written; two guards in the other order; one of two guards dropped; a call of a
function that can stop moved across a guard; two loops against one loop that computes the same; a
different key on a guard.

Then each instruction that following keeps in order, accepted: a choice, a case analysis, a
block, a loop as often as a value says and a call of a function that can stop, each the same
program with other names; a value moved out of a region of a choice and one moved into it; a
value moved across a call of a function that can stop. And refused, each pair differing in one
thing and refused by the comparison of that thing: a guard's condition, a guard's reason, a
choice's condition, the subject of a case analysis, a loop's initial values, a loop's count, a
block's number, a block's key, the operand of a call of a function that can stop, its callee and
its key. Then the theorem for functions, applied to two pairs, the second of them `x + y` and
`y + x`: the two processes are equal on valid inputs.

Last, on the walk of the analysis over a toy dialect, which has attempts: an attempt followed by
the same attempt with other names, accepted, and by one with another key, which differs at the
attempt. Two controls distinguish the input leaf from a fresh reply and show why the
continuation of an attempt runs only after a settlement that can return (`Skel.Runs.attempt`).
-/
namespace Zkc.Core.FollowingTests

open FactsTests (field F plus minus times natural less equal conjunction fieldRow natOrTruth)

-- What the check of facts returns is compared whole.
deriving instance DecidableEq for Except

/-! ## Following -/

/-- Following on two bodies of a function with the key 1, the input and result types, whether it
can stop and the callees given, each typed against the callees (`typeFn`): whether the second
follows the analysis of the first with no place that differs (`TypedFn.follows`); nothing when
one of them does not elaborate. -/
def decided (fns : List (FnHeader field)) (ins outs : List field.Ty) (stops : Bool)
    (body body' : Region (LocalRaw field) Unit) : Option Bool :=
  match typeFn fns ⟨⟨1⟩, ins, outs, stops, none, Summary.empty⟩ body,
      typeFn fns ⟨⟨1⟩, ins, outs, stops, none, Summary.empty⟩ body' with
  | .ok source, .ok target =>
      some (match source.follows target with
        | .ok _ => true
        | .error (_, places) => places.isEmpty)
  | _, _ => none

/-- The whole verdict of following on two bodies, as `decided`: whether the second follows the
analysis of the first with no place that differs and no refusal (`TypedFn.follows`); nothing
when one of them does not elaborate. -/
def safelyFollows (fns : List (FnHeader field)) (ins outs : List field.Ty) (stops : Bool)
    (body body' : Region (LocalRaw field) Unit) : Option Bool :=
  match typeFn fns ⟨⟨1⟩, ins, outs, stops, none, Summary.empty⟩ body,
      typeFn fns ⟨⟨1⟩, ins, outs, stops, none, Summary.empty⟩ body' with
  | .ok source, .ok target =>
      some (match source.follows target with
        | .ok _ => true
        | .error _ => false)
  | _, _ => none

/-- A callee with the key 9 from a natural to a natural, which can stop or cannot. -/
def callee (canStop : Bool) : FnHeader field := ⟨⟨9⟩, [.nat], [.nat], canStop, none, Summary.empty⟩

/-- Two naturals and two truth values. -/
abbrev guarded : List field.Ty := [.nat, .nat, .bool, .bool]

/-! ## Accepted -/

/-- A repeated computation is one value. -/
example : decided [] [.nat, .nat] [.nat, .nat] false
    (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1], .op ⟨2⟩ [11] plus [0, 1]] [10, 11])
    (.mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10, 10]) = some true := by
  decide +kernel

/-- Two computations between guards in the other order, with a computation that nothing uses. -/
example : decided [] guarded [.nat, .nat] true
    (.mk [0, 1, 2, 3] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨2⟩ [10] plus [0, 1],
      .op ⟨3⟩ [11] times [0, 1],
      .guard ⟨4⟩ () 3 .reject] [10, 11])
    (.mk [0, 1, 2, 3] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨3⟩ [11] times [0, 1],
      .op ⟨2⟩ [10] plus [0, 1],
      .op ⟨5⟩ [12] times [0, 0],
      .guard ⟨4⟩ () 3 .reject] [10, 11]) = some true := by
  decide +kernel

/-- Computations before, between and after guards, and the same computations after both guards:
the guards stay in their order. -/
def aroundGuards : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .op ⟨1⟩ [10] plus [0, 1],
  .guard ⟨2⟩ () 2 .reject,
  .op ⟨3⟩ [11] times [0, 1],
  .guard ⟨4⟩ () 3 .reject] [10, 11]

/-- The same computations, after both guards. -/
def afterGuards : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .guard ⟨2⟩ () 2 .reject,
  .guard ⟨4⟩ () 3 .reject,
  .op ⟨3⟩ [11] times [0, 1],
  .op ⟨1⟩ [10] plus [0, 1]] [10, 11]

example : decided [] guarded [.nat, .nat] true aroundGuards afterGuards = some true := by
  decide +kernel

/-- A sum of a computation that does not depend on the loop, inside the loop. -/
def insideLoop : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
    .op ⟨3⟩ [22] plus [0, 1],
    .op ⟨4⟩ [23] plus [21, 22]] [23])] [11]

/-- A computation moved out of a loop. -/
example : decided [] [.nat, .nat] [.nat] false insideLoop
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (natural 0) [],
      .op ⟨3⟩ [12] plus [0, 1],
      .loop ⟨2⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
        .op ⟨4⟩ [23] plus [21, 12]] [23])] [11]) = some true := by
  decide +kernel

/-- The same program with other names for its values, the inputs and those of the loop's region
among them. -/
example : decided [] [.nat, .nat] [.nat] false insideLoop
    (.mk [7, 8] [
      .op ⟨1⟩ [40] (natural 0) [],
      .loop ⟨2⟩ () (.fixed 3) [40] [41] (.mk [50, 51] [
        .op ⟨3⟩ [52] plus [7, 8],
        .op ⟨4⟩ [53] plus [51, 52]] [53])] [41]) = some true := by
  decide +kernel

/-- A call of a function that cannot stop is a value: two calls on one operand are one. -/
example : decided [callee false] [.nat] [.nat] false
    (.mk [0] [
      .op ⟨1⟩ [10] (.call ⟨9⟩) [0],
      .op ⟨2⟩ [11] (.call ⟨9⟩) [0],
      .op ⟨3⟩ [12] plus [10, 11]] [12])
    (.mk [0] [
      .op ⟨1⟩ [10] (.call ⟨9⟩) [0],
      .op ⟨3⟩ [12] plus [10, 10]] [12]) = some true := by
  decide +kernel

/-- `x + y`. -/
def sum : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] plus [0, 1]] [10]

/-- `y + x`. -/
def commutedSum : Region (LocalRaw field) Unit := .mk [0, 1] [.op ⟨1⟩ [10] plus [1, 0]] [10]

/-- `x + y` against `y + x`: accepted, since addition commutes; the table places `y + x` with its
operands in the order of `x + y`, so the two are one value. -/
example : decided [] [.nat, .nat] [.nat] false sum commutedSum = some true := by
  decide +kernel

/-- The equality of truth values. -/
abbrev sameTruth : LocalRaw field := .owned .boolEqual [] []

/-- `x == y` against `y == x`, of naturals: the whole verdict accepts it, since the equality
commutes. -/
example : safelyFollows [] [.nat, .nat] [.bool] false
    (.mk [0, 1] [.op ⟨1⟩ [10] equal [0, 1]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] equal [1, 0]] [10]) = some true := by
  decide +kernel

/-- `x == y` against `y == x`, of truth values: accepted too. -/
example : safelyFollows [] [.bool, .bool] [.bool] false
    (.mk [0, 1] [.op ⟨1⟩ [10] sameTruth [0, 1]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] sameTruth [1, 0]] [10]) = some true := by
  decide +kernel

/-- A product and a sum with their operands exchanged, inside a loop that comes after a guard,
and the product again after the loop: each is the value of the first. -/
example : decided [] [.nat, .nat, .bool] [.nat, .nat] true
    (.mk [0, 1, 2] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨2⟩ [10] (natural 0) [],
      .loop ⟨3⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
        .op ⟨4⟩ [22] times [0, 1],
        .op ⟨5⟩ [23] plus [21, 22]] [23]),
      .op ⟨6⟩ [12] times [0, 1]] [11, 12])
    (.mk [0, 1, 2] [
      .guard ⟨1⟩ () 2 .reject,
      .op ⟨2⟩ [10] (natural 0) [],
      .loop ⟨3⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [
        .op ⟨4⟩ [22] times [1, 0],
        .op ⟨5⟩ [23] plus [22, 21]] [23]),
      .op ⟨6⟩ [12] times [1, 0]] [11, 12]) = some true := by
  decide +kernel

/-! ## Refused -/

/-- `x - y` against `y - x`: a difference does not commute. -/
example : decided [] [.nat, .nat] [.nat] false
    (.mk [0, 1] [.op ⟨1⟩ [10] minus [0, 1]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] minus [1, 0]] [10]) = some false := by
  decide +kernel

/-- `(x + y) + z` against `x + (y + z)`: the same value only by the associativity of addition,
which is not a law that following knows; only the order of two operands is. -/
example : decided [] [.nat, .nat, .nat] [.nat] false
    (.mk [0, 1, 2] [.op ⟨1⟩ [10] plus [0, 1], .op ⟨2⟩ [11] plus [10, 2]] [11])
    (.mk [0, 1, 2] [.op ⟨1⟩ [10] plus [1, 2], .op ⟨2⟩ [11] plus [0, 10]] [11]) = some false := by
  decide +kernel

/-- A row of the vocabulary with its operands exchanged: the addition of field elements does not
commute for the analysis, whatever a model does; that a row commutes would be a law of the
model. -/
example : decided [] [F, F] [F] false
    (.mk [0, 1] [.op ⟨1⟩ [10] (fieldRow .add) [0, 1]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] (fieldRow .add) [1, 0]] [10]) = some false := by
  decide +kernel

/-- `t := a < b; f := 5; e := b == f`, then `c := e && t` (or `c := t && e`) and `guard c`. -/
def conjunctionOf (equalityFirst : Bool) : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] less [0, 1],
  .op ⟨2⟩ [11] (natural 5) [],
  .op ⟨3⟩ [12] equal [1, 11],
  .op ⟨4⟩ [13] conjunction (if equalityFirst then [12, 10] else [10, 12]),
  .guard ⟨5⟩ () 13 .reject] [0]

/-- `c := e && t` against `c := t && e`: refused. The conjunction does not commute for the table,
since the check of facts learns its operands in the order written (`FactsTests.learnedInOrder`):
the two are other values, and the guard of the second is not the skeleton's entry. -/
example : decided [] [.nat, .nat] [.nat] true (conjunctionOf true) (conjunctionOf false) =
    some false := by
  decide +kernel

/-- Two guards in the other order: which one stops first is kept. -/
example : decided [] [.bool, .bool] [] true
    (.mk [0, 1] [.guard ⟨1⟩ () 0 .reject, .guard ⟨2⟩ () 1 .reject] [])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject, .guard ⟨1⟩ () 0 .reject] []) = some false := by
  decide +kernel

/-- A guard dropped, the other kept: the function can still stop, with the same header. -/
example : decided [] [.nat, .bool, .bool] [.nat] true
    (.mk [0, 1, 2] [.guard ⟨1⟩ () 1 .reject, .guard ⟨2⟩ () 2 .reject] [0])
    (.mk [0, 1, 2] [.guard ⟨2⟩ () 2 .reject] [0]) = some false := by
  decide +kernel

/-- A call of a function that can stop, moved across a guard: such a call is kept in order. -/
example : decided [callee true] [.nat, .bool] [.nat] true
    (.mk [0, 1] [.op ⟨1⟩ [10] (.call ⟨9⟩) [0], .guard ⟨2⟩ () 1 .reject] [10])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject, .op ⟨1⟩ [10] (.call ⟨9⟩) [0]] [10]) = some false := by
  decide +kernel

/-- Two loops against one loop that computes the same: following keeps every loop in order, as an
entry of the skeleton, and does not decide the fusion of loops. -/
example : decided [] [.nat, .nat] [.nat, .nat] false
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (natural 0) [],
      .loop ⟨2⟩ () (.fixed 3) [10] [11] (.mk [20, 21] [.op ⟨3⟩ [22] plus [21, 0]] [22]),
      .loop ⟨4⟩ () (.fixed 3) [10] [12] (.mk [30, 31] [.op ⟨5⟩ [32] plus [31, 1]] [32])]
      [11, 12])
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (natural 0) [],
      .loop ⟨2⟩ () (.fixed 3) [10, 10] [11, 12] (.mk [20, 21, 31] [
        .op ⟨3⟩ [22] plus [21, 0],
        .op ⟨5⟩ [32] plus [31, 1]] [22, 32])] [11, 12]) = some false := by
  decide +kernel

/-- A different key on a guard: where it stops is part of what it does. -/
example : decided [] [.nat, .bool] [.nat] true
    (.mk [0, 1] [.guard ⟨1⟩ () 1 .reject] [0])
    (.mk [0, 1] [.guard ⟨2⟩ () 1 .reject] [0]) = some false := by
  decide +kernel

/-! ## Each form of control, followed

Each instruction that following keeps in order, reached with a pair that it accepts: a choice, a
case analysis, a block, a loop as often as a value says, and a call of a function that can stop. -/

/-- A choice on a truth value whose regions give the sum and the product of two naturals, and the
sum of what it gives with the first natural. -/
def chosen : Region (LocalRaw field) Unit := .mk [0, 1, 2] [
  .choose ⟨1⟩ () 0 [10]
    (.mk [] [.op ⟨2⟩ [20] plus [1, 2]] [20])
    (.mk [] [.op ⟨3⟩ [30] times [1, 2]] [30]),
  .op ⟨4⟩ [11] plus [10, 1]] [11]

/-- A choice: the same program with other names for its inputs, the values of its regions and
its result. -/
example : decided [] [.bool, .nat, .nat] [.nat] false chosen
    (.mk [5, 6, 7] [
      .choose ⟨1⟩ () 5 [40]
        (.mk [] [.op ⟨2⟩ [50] plus [6, 7]] [50])
        (.mk [] [.op ⟨3⟩ [60] times [6, 7]] [60]),
      .op ⟨4⟩ [41] plus [40, 6]] [41]) = some true := by
  decide +kernel

/-- A value moved out of a region of a choice, to before the choice: the sum, which has no
domain, so that computing it where the region does not run is safe. The first region gives it.
-/
example : decided [] [.bool, .nat, .nat] [.nat] false chosen
    (.mk [0, 1, 2] [
      .op ⟨2⟩ [20] plus [1, 2],
      .choose ⟨1⟩ () 0 [10]
        (.mk [] [] [20])
        (.mk [] [.op ⟨3⟩ [30] times [1, 2]] [30]),
      .op ⟨4⟩ [11] plus [10, 1]] [11]) = some true := by
  decide +kernel

/-- A value moved into a region of a choice: the product computed before the choice and given
by its second region, against the product computed in that region. -/
example : decided [] [.bool, .nat, .nat] [.nat] false
    (.mk [0, 1, 2] [
      .op ⟨3⟩ [30] times [1, 2],
      .choose ⟨1⟩ () 0 [10]
        (.mk [] [.op ⟨2⟩ [20] plus [1, 2]] [20])
        (.mk [] [] [30]),
      .op ⟨4⟩ [11] plus [10, 1]] [11])
    chosen = some true := by
  decide +kernel

/-- A case analysis of a natural or a truth value: the natural plus the second input, or the
second input; then what it gives times the second input. -/
def analysed : Region (LocalRaw field) Unit := .mk [0, 1] [
  .cases ⟨1⟩ () 0 [10]
    [.mk [20] [.op ⟨2⟩ [21] plus [20, 1]] [21],
     .mk [30] [] [1]],
  .op ⟨3⟩ [11] times [10, 1]] [11]

/-- A case analysis: the same program with other names for its inputs, the payloads of its arms,
their values and its result. -/
example : decided [] [natOrTruth, .nat] [.nat] false analysed
    (.mk [3, 4] [
      .cases ⟨1⟩ () 3 [40]
        [.mk [50] [.op ⟨2⟩ [51] plus [50, 4]] [51],
         .mk [60] [] [4]],
      .op ⟨3⟩ [41] times [40, 4]] [41]) = some true := by
  decide +kernel

/-- A block whose body gives the sum of two naturals, and what it gives times the first. -/
def blocked : Region (LocalRaw field) Unit := .mk [0, 1] [
  .block ⟨1⟩ 0 [10] (.mk [] [.op ⟨2⟩ [20] plus [0, 1]] [20]),
  .op ⟨3⟩ [11] times [10, 0]] [11]

/-- A block: the same program with other names. -/
example : decided [] [.nat, .nat] [.nat] false blocked
    (.mk [5, 6] [
      .block ⟨1⟩ 0 [40] (.mk [] [.op ⟨2⟩ [50] plus [5, 6]] [50]),
      .op ⟨3⟩ [41] times [40, 5]] [41]) = some true := by
  decide +kernel

/-- A loop as often as the second natural says, which adds the iteration number to what it
carries from the first. -/
def counted : Region (LocalRaw field) Unit := .mk [0, 1] [
  .loop ⟨1⟩ () (.count 1) [0] [10] (.mk [20, 21] [.op ⟨2⟩ [22] plus [21, 20]] [22])] [10]

/-- A loop as often as a value says: the same program with other names, the count's among them.
-/
example : decided [] [.nat, .nat] [.nat] false counted
    (.mk [5, 6] [
      .loop ⟨1⟩ () (.count 6) [5] [40] (.mk [50, 51] [.op ⟨2⟩ [52] plus [51, 50]] [52])] [40]) =
    some true := by
  decide +kernel

/-- A call of a function that can stop, on a sum, followed by a product. -/
def calling : Region (LocalRaw field) Unit := .mk [0, 1] [
  .op ⟨1⟩ [10] plus [0, 1],
  .op ⟨2⟩ [11] (.call ⟨9⟩) [10],
  .op ⟨3⟩ [12] times [0, 1]] [11, 12]

/-- A call of a function that can stop, an effect kept in order: the same program with other
names. -/
example : decided [callee true] [.nat, .nat] [.nat, .nat] true calling
    (.mk [5, 6] [
      .op ⟨1⟩ [40] plus [5, 6],
      .op ⟨2⟩ [41] (.call ⟨9⟩) [40],
      .op ⟨3⟩ [42] times [5, 6]] [41, 42]) = some true := by
  decide +kernel

/-- A value moved across a call of a function that can stop: the product, before the call. -/
example : decided [callee true] [.nat, .nat] [.nat, .nat] true calling
    (.mk [0, 1] [
      .op ⟨1⟩ [10] plus [0, 1],
      .op ⟨3⟩ [12] times [0, 1],
      .op ⟨2⟩ [11] (.call ⟨9⟩) [10]] [11, 12]) = some true := by
  decide +kernel

/-! ## Refused by one comparison

Each pair differs in one part of one instruction that following keeps in order, and is refused
by the comparison of that part. -/

/-- Only a guard's condition differs, with the same key and the same reason: refused by the
comparison of the condition's identifier. -/
example : decided [] [.bool, .bool] [] true
    (.mk [0, 1] [.guard ⟨1⟩ () 0 .reject] [])
    (.mk [0, 1] [.guard ⟨1⟩ () 1 .reject] []) = some false := by
  decide +kernel

/-- Only a guard's reason differs, with the same key and the same condition: refused by the
comparison of the reasons, since the reason is what the guard stops with. -/
example : decided [] [.bool] [] true
    (.mk [0] [.guard ⟨1⟩ () 0 .reject] [])
    (.mk [0] [.guard ⟨1⟩ () 0 .refused] []) = some false := by
  decide +kernel

/-- A choice on the truth value given, among two, whose regions give the sum and the product of
two naturals. -/
def choiceOn (condition : Nat) : Region (LocalRaw field) Unit := .mk [0, 1, 2, 3] [
  .choose ⟨1⟩ () condition [10]
    (.mk [] [.op ⟨2⟩ [20] plus [2, 3]] [20])
    (.mk [] [.op ⟨3⟩ [30] times [2, 3]] [30])] [10]

/-- Only a choice's condition differs: refused by the comparison of the condition's identifier. -/
example : decided [] [.bool, .bool, .nat, .nat] [.nat] false (choiceOn 0) (choiceOn 1) =
    some false := by
  decide +kernel

/-- A case analysis of the value given, among two of a natural or a truth value: the natural plus
the third input, or the third input. -/
def casesOn (subject : Nat) : Region (LocalRaw field) Unit := .mk [0, 1, 2] [
  .cases ⟨1⟩ () subject [10]
    [.mk [20] [.op ⟨2⟩ [21] plus [20, 2]] [21],
     .mk [30] [] [2]]] [10]

/-- Only the subject of a case analysis differs: refused by the comparison of the subject's
identifier. -/
example : decided [] [natOrTruth, natOrTruth, .nat] [.nat] false (casesOn 0) (casesOn 1) =
    some false := by
  decide +kernel

/-- Only a loop's initial values differ: refused by the comparison of the identifiers of the
initial values. -/
example : decided [] [.nat, .nat] [.nat] false
    (.mk [0, 1] [
      .loop ⟨1⟩ () (.fixed 2) [0] [10] (.mk [20, 21] [.op ⟨2⟩ [22] plus [21, 21]] [22])] [10])
    (.mk [0, 1] [
      .loop ⟨1⟩ () (.fixed 2) [1] [10] (.mk [20, 21] [.op ⟨2⟩ [22] plus [21, 21]] [22])] [10]) =
    some false := by
  decide +kernel

/-- A loop as often as the natural given says, among two, which adds the iteration number to what
it carries from the first input. -/
def countedBy (count : Nat) : Region (LocalRaw field) Unit := .mk [0, 1, 2] [
  .loop ⟨1⟩ () (.count count) [0] [10] (.mk [20, 21] [.op ⟨2⟩ [22] plus [21, 20]] [22])] [10]

/-- Only a loop's count differs: refused by the comparison of the count's identifier. -/
example : decided [] [.nat, .nat, .nat] [.nat] false (countedBy 1) (countedBy 2) =
    some false := by
  decide +kernel

/-- Only a block's number differs: refused by the comparison of the numbers. -/
example : decided [] [.nat, .nat] [.nat] false blocked
    (.mk [0, 1] [
      .block ⟨1⟩ 1 [10] (.mk [] [.op ⟨2⟩ [20] plus [0, 1]] [20]),
      .op ⟨3⟩ [11] times [10, 0]] [11]) = some false := by
  decide +kernel

/-- Only a block's key differs: refused by the comparison of the keys. -/
example : decided [] [.nat, .nat] [.nat] false blocked
    (.mk [0, 1] [
      .block ⟨4⟩ 0 [10] (.mk [] [.op ⟨2⟩ [20] plus [0, 1]] [20]),
      .op ⟨3⟩ [11] times [10, 0]] [11]) = some false := by
  decide +kernel

/-- Only the operand of a call of a function that can stop differs: refused by the comparison of
the identifiers of the effect's operands. -/
example : decided [callee true] [.nat, .nat] [.nat] true
    (.mk [0, 1] [.op ⟨1⟩ [10] (.call ⟨9⟩) [0]] [10])
    (.mk [0, 1] [.op ⟨1⟩ [10] (.call ⟨9⟩) [1]] [10]) = some false := by
  decide +kernel

/-- A second callee, with the key 8, from a natural to a natural, which can stop too. -/
def otherCallee : FnHeader field := ⟨⟨8⟩, [.nat], [.nat], true, none, Summary.empty⟩

/-- Only the callee of a call of a function that can stop differs, between two callees of one
header but their keys: refused by the comparison of the effects' written operations. -/
example : decided [callee true, otherCallee] [.nat] [.nat] true
    (.mk [0] [.op ⟨1⟩ [10] (.call ⟨9⟩) [0]] [10])
    (.mk [0] [.op ⟨1⟩ [10] (.call ⟨8⟩) [0]] [10]) = some false := by
  decide +kernel

/-- Only the key of a call of a function that can stop differs: refused by the comparison of the
effects' keys, since where it stops is part of what it does. -/
example : decided [callee true] [.nat] [.nat] true
    (.mk [0] [.op ⟨1⟩ [10] (.call ⟨9⟩) [0]] [10])
    (.mk [0] [.op ⟨2⟩ [10] (.call ⟨9⟩) [0]] [10]) = some false := by
  decide +kernel

/-! ## The theorem for functions -/

/-- No callee. -/
def noCallees (M : Model field) : FnTable M [] := fun _ callee _ => nomatch callee

/-- No callee is a table of callees that a statement about a function can be made against. -/
theorem noCallees_callees (M : Model field) : Callees M (noCallees M) :=
  ⟨List.nodup_nil, (fun _ callee => nomatch callee), (fun _ callee => nomatch callee),
    (fun _ callee => nomatch callee)⟩

/-- The whole verdict on the two bodies: the second follows the first with no place that differs
and no refusal. -/
example : safelyFollows [] guarded [.nat, .nat] true aroundGuards afterGuards = some true := by
  decide +kernel

/-- The header of the two bodies: the key 1, no callee, and it can stop. -/
def guardedHeader : FnHeader field := ⟨⟨1⟩, guarded, [.nat, .nat], true, none, Summary.empty⟩

/-- A stored function typed against no callee; nothing when it does not elaborate. -/
def typed (hdr : FnHeader field) (body : Region (LocalRaw field) Unit) :
    Option (TypedFn field [] hdr) :=
  match typeFn [] hdr body with
  | .ok f => some f
  | .error _ => none

/-- Computations around guards, as a typed function. -/
def aroundGuardsFn := (typed guardedHeader aroundGuards).get (by decide +kernel)

/-- The same computations after the guards, as a typed function. -/
def afterGuardsFn := (typed guardedHeader afterGuards).get (by decide +kernel)

/-- The second is assured and the two have the same meaning on every valid input, in every
model: the first is safe, here because the check of facts accepts it
(`TypedFn.check_assured`), and the second follows its analysis with no place that differs and no
refusal (`TypedFn.follows_assured`). -/
example : afterGuardsFn.Assured [] ∧ aroundGuardsFn.SameAs afterGuardsFn :=
  TypedFn.follows_assured (aroundGuardsFn.check_assured (bounds := []) (by decide +kernel)).safe
    (by decide +kernel)

/-- So the two processes are equal, in a model and on valid inputs, of which the empty summary
requires nothing. -/
example (M : Model field) (ins : HList M.Val guarded) (valid : ins.All M.Valid) :
    aroundGuardsFn.meaning M (noCallees M) ins = afterGuardsFn.meaning M (noCallees M) ins :=
  (TypedFn.follows_assured (aroundGuardsFn.check_assured (bounds := []) (by decide +kernel)).safe
    (bounds := []) (by decide +kernel)).2 M (noCallees M) (noCallees_callees M) ins valid
    (fun _ listed => nomatch listed)

/-- The whole verdict on `x + y` and `y + x`: accepted. -/
example : safelyFollows [] [.nat, .nat] [.nat] false sum commutedSum = some true := by
  decide +kernel

/-- The header of the sum: the key 1, no callee, and it cannot stop. -/
def sumHeader : FnHeader field := ⟨⟨1⟩, [.nat, .nat], [.nat], false, none, Summary.empty⟩

/-- `x + y`, as a typed function. -/
def sumFn := (typed sumHeader sum).get (by decide +kernel)

/-- `y + x`, as a typed function. -/
def commutedSumFn := (typed sumHeader commutedSum).get (by decide +kernel)

/-- `x + y` and `y + x` have equal processes on every valid input, in every model: following
accepts the pair, and the law `commutative` of the local operations makes that sound. -/
example (M : Model field) (ins : HList M.Val [.nat, .nat]) (valid : ins.All M.Valid) :
    sumFn.meaning M (noCallees M) ins = commutedSumFn.meaning M (noCallees M) ins :=
  (TypedFn.follows_assured (sumFn.check_assured (bounds := []) (by decide +kernel)).safe
    (bounds := []) (by decide +kernel)).2 M (noCallees M) (noCallees_callees M) ins valid
    (fun _ listed => nomatch listed)

/-! ## Controls on the definitions of the value form -/

/-- The operations of the dialect of the controls: one asks for a reply and returns it, one
stops with `true`, which stands for `undefined`. -/
inductive ToyOp : List Unit → List Unit → Type where
  | ask : ToyOp [] [()]
  | fail : ToyOp [] [()]

/-- A dialect of one type whose attempts anyone may own, with no condition, variant or count. -/
@[reducible] def toy : Dialect where
  Ty := Unit
  Op := ToyOp
  Who := Unit
  Condition _ _ := False
  Alternatives _ _ _ := False
  Count _ _ := False
  index _ := ()
  Attempt _ := True
  Gives _ _ := True
  collected _ _ := ()

/-- Its semantics: values are truth values; asking calls for a reply and returns it; failing
stops with `true`; the end of an attempt calls for a reply. -/
def toySem : Semantics toy where
  Val _ := Bool
  S := ⟨Unit, fun _ => Bool⟩
  H := Bool
  op := fun {_ _} _ o _ _ => match o with
    | .ask => .call () fun reply => .done (.cons reply .nil)
    | .fail => .halt true
  holds := fun {_ _} ok _ => nomatch ok
  stop := fun _ _ _ => false
  pick := fun {_ _ _} ok _ => nomatch ok
  count := fun {_ _} ok _ => nomatch ok
  index := fun _ _ => false
  begin := fun _ _ _ => .done false
  settle := fun _ _ _ => .call () fun _ => .done ()
  collect := fun _ _ _ => false

open BodyAnalysis

def toyWritten : {ins outs : List Unit} → ToyOp ins outs → Bool
  | _, _, .ask => false
  | _, _, .fail => true

/-- Asking is an ordered effect. Failing is a shared operation that stops undefined. -/
def toyConfig : Config toy Bool where
  rules := {
    written := toyWritten
    shared := toyWritten
    commutes _ := false
    place := Bool.toNat
    results _ := 1
    contract _ := ⟨[], []⟩
    assertable _ := false
    numbered _ := false
    indexAt _ _ := none
    indexFromCount ok := nomatch ok
    indexNext _ := none }
  domain := Knowledge.domain ⟨fun _ => none, fun _ => false⟩ { ranges := fun _ _ => [], form := fun _ => none }
  assertions := ⟨fun _ _ => none, fun _ => false⟩
  lemmas := []
  definition := ⟨1⟩
  role := none

def toyChecks : SkelRules toy where
  sameTy := inferInstanceAs (DecidableEq Unit)
  sameWho := inferInstanceAs (DecidableEq Unit)
  sameOp := fun o o' => toyWritten o == toyWritten o'

/-! ### An attempt followed

A function has no attempt, so following an attempt is exercised in the toy dialect: the analysis
of a term with an attempt, and a second term that follows it (`followChecked`). -/

/-- An attempt with the key 1 whose body asks and gives the reply, with the names `0` for its
number, `1` for the reply and `2` for what it gives, which is returned. -/
def attempted : Term toy Ctx.empty [()] :=
  .attempt ⟨1⟩ () trivial (.cons 0 .nil)
    (.op ⟨2⟩ ToyOp.ask .nil (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil)))
    (.cons 2 .nil) (.ret (.cons ⟨2, rfl⟩ .nil))

/-- The same attempt with other names: `5`, `6` and `7`. -/
def attemptedOtherNames : Term toy Ctx.empty [()] :=
  .attempt ⟨1⟩ () trivial (.cons 5 .nil)
    (.op ⟨2⟩ ToyOp.ask .nil (.cons 6 .nil) (.ret (.cons ⟨6, rfl⟩ .nil)))
    (.cons 7 .nil) (.ret (.cons ⟨7, rfl⟩ .nil))

/-- The same attempt with the key 3. -/
def attemptedOtherKey : Term toy Ctx.empty [()] :=
  .attempt ⟨3⟩ () trivial (.cons 0 .nil)
    (.op ⟨2⟩ ToyOp.ask .nil (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil)))
    (.cons 2 .nil) (.ret (.cons ⟨2, rfl⟩ .nil))

example : followChecked toyConfig toyChecks ⟨1⟩ [] [] ⟨[],[]⟩ .nil .nil
    attempted attemptedOtherNames = .ok [] := rfl

example : followChecked toyConfig toyChecks ⟨1⟩ [] [] ⟨[],[]⟩ .nil .nil
    attempted attemptedOtherKey =
      .error (.body [] [⟨⟨1⟩, [], some ⟨3⟩, none⟩]) := rfl

/-! ### Leaves made in order -/

/-- The context of the name `0`. -/
abbrev oneName : Ctx Unit := Ctx.empty.insert 0 ()

/-- Ask, and return the reply. -/
def returnsReply : Term toy oneName [()] :=
  .op ⟨1⟩ ToyOp.ask .nil (.cons 1 .nil) (.ret (.cons ⟨1, rfl⟩ .nil))

/-- Ask, and return the value of the name `0`. -/
def returnsInput : Term toy oneName [()] :=
  .op ⟨1⟩ ToyOp.ask .nil (.cons 1 .nil) (.ret (.cons ⟨0, rfl⟩ .nil))

/-- The input is leaf zero. The effect allocates a distinct reply leaf. Comparison
detects which one is returned, even though both bodies ask exactly the same question. -/
example : followChecked toyConfig toyChecks ⟨1⟩ [] [] ⟨[],[]⟩
    (.cons 0 .nil : Names [()]) (.cons 0 .nil) returnsReply returnsInput =
      .error (.body [] [⟨⟨1⟩, [], none, none⟩]) := rfl

/-- On the reply false, the first returns false and the second returns the true input. -/
example : ¬ Process.SameWhen (fun _ _ => True)
    (returnsReply.denote toySem [] fun _ _ _ => true)
    (returnsInput.denote toySem [] fun _ _ _ => true) := by
  intro same
  cases same with
  | call _ next => cases next false trivial

/-! ### What follows an attempt -/

/-- An attempt whose body gives nothing, then failing, then nothing. -/
def failsAfterAttempt : Term toy Ctx.empty [] :=
  .attempt ⟨1⟩ () trivial (.cons 0 .nil) (.ret .nil) .nil
    (.op ⟨2⟩ ToyOp.fail .nil (.cons 1 .nil) (.ret .nil))

/-- No reply is permitted, and the end of the attempt calls for one: the run never stops, and in
particular never `undefined`. -/
theorem failsAfterAttempt_safe : (failsAfterAttempt.denote toySem [] Env.empty).Every
    (fun _ _ => False) (fun _ => True) (fun stop => ¬ stop = true) :=
  fun _ never => never.elim

private def exitAfterAttempt :=
  analyse toyConfig [] ⟨[],[]⟩ .nil failsAfterAttempt

private def toyReading : Reading toySem.Dyn := ⟨fun _ => none, fun v => some v.2⟩

/-- The actual skeleton of this body runs: the body returns, but the settlement requires
an unavailable reply, so the failing continuation is never reached. -/
example : Skel.Runs toySem (fun _ _ => False) (fun (_ : Bool) _ _ => False) toyReading
    exitAfterAttempt.state.values.table [] (fun _ => none) exitAfterAttempt.skel .nil
    (failsAfterAttempt.denote toySem [] Env.empty) := by
  change Skel.Runs toySem (fun _ _ => False) (fun (_ : Bool) _ _ => False) toyReading
    exitAfterAttempt.state.values.table [] (fun _ => none)
    (.step ⟨1⟩ (.attempt (mid := []) () 0 (.ret []) 1) (.ret [])) .nil _
  apply Skel.Runs.attempt (sem := toySem) (w := ()) (region := [])
    (bodyOf := fun _ => .done .nil) (k := fun _ => .halt true)
  · intro n _
    exact .ret .nil .nil (.done .nil)
  · intro _ _ _ _ settled
    cases settled with
    | call _ _ impossible _ => exact impossible.elim

/-- The failing continuation cannot run its return skeleton by itself. -/
example : ¬ Skel.Runs toySem (fun _ _ => False) (fun (_ : Bool) _ _ => False) toyReading
    exitAfterAttempt.state.values.table [] (fun _ => none) (.ret [] : Skel toy []) .nil
    ((Term.op ⟨2⟩ ToyOp.fail .nil (.cons 1 .nil) (.ret .nil) : Term toy Ctx.empty []).denote
      toySem [] Env.empty) := by
  intro runs
  cases runs with
  | ret _ _ resume => cases resume

end Zkc.Core.FollowingTests
