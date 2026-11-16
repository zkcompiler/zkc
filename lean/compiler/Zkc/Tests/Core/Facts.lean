import Zkc.Core.Facts.Local
import Zkc.Core.Facts.Walk
import Zkc.Core.Program.ElaborateLocal

/-!
The check of facts on functions written by names, elaborated and walked by the kernel.

The conformance cases of the reference that a function can express are named by their
identifiers: each is accepted or refused as the case says, and a refusal is compared whole;
`T-Z8` and `I-4e-total` are also accepted with the operands of a sum exchanged. One case is
accepted against the reference, and named for what it shows (`facts-commutativity-recovered`):
a fact on `i + 1` holds of `1 + i`, since the table places the operands of a sum in one order. Then, for each
operation with a domain and for a restricted row, an application that is accepted and one that
is refused; then what sharing and the scope of facts must do in sibling regions, in loops, after
a choice, and for a new name bound where a program would bind a name again, which elaboration
refuses by the rule `assignment`; a loop over a range whose end is a run-time value, its index
written as a sum in either order; a power too large to compute; what the calculus of facts does
not conclude; then which code does not run: only what is written says so, never what is known;
and, for each rule of the calculus, a case that only it decides: what a condition teaches, the
operands of a conjunction learned in the order written, whose verdict depends on that order, an
equality learned false, whose verdict does not depend on the order of its operands, what regions
give of a natural, the ranges of arithmetic, code that does not run after an operation
or a loop, places and the order of bounds, and which types have no value.
-/

namespace Zkc.Core.FactsTests

/-! ## A vocabulary with a field -/

/-- The rows of a field: equality, addition, multiplication, whether an element is not zero, and
the inverse, restricted to elements that are not zero. -/
inductive FieldRow where
  | equal | add | mul | isNonzero | inverse
deriving DecidableEq

/-- A field element. -/
def fieldElement : Ty Unit := .nominal ()

/-- A vocabulary with one nominal type, a field, whose every natural is a literal. -/
def field : Vocabulary where
  TypeKey := Unit
  RowKey := FieldRow
  LawKey := Empty
  row r := some <| match r with
    | .equal => ⟨[fieldElement, fieldElement], [.bool], .pure⟩
    | .add => ⟨[fieldElement, fieldElement], [fieldElement], .pure⟩
    | .mul => ⟨[fieldElement, fieldElement], [fieldElement], .pure⟩
    | .isNonzero => ⟨[fieldElement], [.bool], .pure⟩
    | .inverse => ⟨[fieldElement], [fieldElement], .restricted .isNonzero⟩
  law r := nomatch r
  literal _ _ := true
  decided key _ _ found kind := by cases key <;> cases found <;> cases kind <;> rfl

/-! ## Types and written operations -/

abbrev F : field.Ty := fieldElement
/-- A sequence of field elements of any length. -/
abbrev elements : field.Ty := .seq F none
/-- A sequence of field elements of a size. -/
abbrev sizedElements (size : Nat) : field.Ty := .seq F (some size)
abbrev byte : field.Ty := .fin 256
abbrev bytes (size : Nat) : field.Ty := .seq byte (some size)
abbrev naturals (size : Nat) : field.Ty := .seq .nat (some size)

abbrev length (τ : field.Ty) : LocalRaw field := .owned .seqLength [τ] []
abbrev item (τ : field.Ty) : LocalRaw field := .owned .seqAt [τ] []
abbrev slice (τ result : field.Ty) : LocalRaw field := .owned .seqSlice [τ, result] []
abbrev sizedAs (size : Nat) : LocalRaw field := .owned .seqSized [sizedElements size] []
abbrev natural (n : Nat) : LocalRaw field := .literal .nat [n]
abbrev element (n : Nat) : LocalRaw field := .literal F [n]
abbrev truth (value : Bool) : LocalRaw field := .literal .bool [if value then 1 else 0]
abbrev plus : LocalRaw field := .owned .natAdd [] []
abbrev minus : LocalRaw field := .owned .natSub [] []
abbrev times : LocalRaw field := .owned .natMul [] []
abbrev quotient : LocalRaw field := .owned .natDiv [] []
abbrev remainder : LocalRaw field := .owned .natRem [] []
abbrev power : LocalRaw field := .owned .natPow [] []
abbrev less : LocalRaw field := .owned .natLess [] []
abbrev equal : LocalRaw field := .owned .natEqual [] []
abbrev negation : LocalRaw field := .owned .boolNot [] []
abbrev toNat (bound : Nat) : LocalRaw field := .owned .finToNat [.fin bound] []
abbrev narrowTo (bound : Nat) : LocalRaw field := .owned .natBelow [.fin bound] []
abbrev fieldRow (r : FieldRow) : LocalRaw field := .row r

/-! ## The verdict -/

/-- What the check of facts says of the body of a function against the headers before it: its
refusals, or the bounds of its loops; nothing when the body does not elaborate. -/
def verdict (fns : List (FnHeader field)) (hdr : FnHeader field)
    (body : Region (LocalRaw field) Unit) :
    Option (List (ProgramRefusal field) ⊕ List (Place × Nat)) :=
  match elabFn fns hdr body with
  | .ok ⟨inputs, fn, _⟩ =>
      match checkFacts (localFactRules field fns) (localSkelRules field fns) hdr.key none
          inputs fn with
      | .ok bounds => some (.inr bounds)
      | .error refusals => some (.inl refusals)
  | .error _ => none

/-- The verdict on a function with the key 1 and no callee. -/
def check (ins outs : List field.Ty) (canStop : Bool) (body : Region (LocalRaw field) Unit) :
    Option (List (ProgramRefusal field) ⊕ List (Place × Nat)) :=
  verdict [] ⟨⟨1⟩, ins, outs, canStop, none⟩ body

/-- The refusal of elaboration of the body of a function with the key 1 and no callee; nothing
when it elaborates. -/
def elaborationRefusal (ins outs : List field.Ty) (canStop : Bool)
    (body : Region (LocalRaw field) Unit) : Option (ProgramRefusal field) :=
  match elabFn [] ⟨⟨1⟩, ins, outs, canStop, none⟩ body with
  | .ok _ => none
  | .error refusal => some refusal

/-- Accepted, with no loop as often as a count that has a bound. -/
abbrev accepted : Option (List (ProgramRefusal field) ⊕ List (Place × Nat)) := some (.inr [])

/-- The place of an instruction of the function with the key 1. -/
def place (instruction : Nat) : Place := ⟨⟨1⟩, [], some ⟨instruction⟩, none⟩

/-- An application refused at an instruction. -/
def unjustified (instruction : Nat) (written : LocalRaw field)
    (requirement : Requirement (LocalRaw field)) (known : List (Option Range)) :
    ProgramRefusal field :=
  ⟨.domain, place instruction, .unjustified written requirement known⟩

/-- What an unsized sequence's length requires to be known of, by its first operand. -/
abbrev lengthOf : Operand (LocalRaw field) := .apply (length elements) [0]

abbrev anyNat : Option Range := some ⟨0, none⟩

/-! ## What sharing must and must not do; the cases that pin the strength -/

/-- A guard gives the fact `i < length(xs)`. -/
def «T-Z7» := check [elements, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .reject,
  .op ⟨4⟩ [12] (item elements) [0, 1]] [12]

/-- `t - u < t` with `1 <= u` and `u <= t` known. -/
def «V-F16» := check [elements, .fin 3] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (toNat 3) [1],
  .op ⟨2⟩ [11] (natural 1) [],
  .op ⟨3⟩ [12] less [10, 11],
  .op ⟨4⟩ [13] negation [12],
  .guard ⟨5⟩ () 13 .refused,
  .op ⟨6⟩ [14] (length elements) [0],
  .op ⟨7⟩ [15] less [14, 10],
  .op ⟨8⟩ [16] negation [15],
  .guard ⟨9⟩ () 16 .refused,
  .op ⟨10⟩ [17] (length elements) [0],
  .op ⟨11⟩ [18] minus [17, 10],
  .op ⟨12⟩ [19] (item elements) [0, 18]] [19]

/-- The condition of a choice gives its facts to the first region: `head`. -/
def «R-TY9a-head» := check [elements] [.variant ⟨7⟩ (.cons F (.cons (.tuple .nil) .nil))] false <|
  .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [
      .op ⟨5⟩ [20] (natural 0) [],
      .op ⟨6⟩ [21] (item elements) [0, 20],
      .op ⟨7⟩ [22] (.owned .variant [.variant ⟨7⟩ (.cons F (.cons (.tuple .nil) .nil))] [0])
        [21]] [22])
    (.mk [] [
      .op ⟨8⟩ [30] (.owned .make [.tuple .nil] []) [],
      .op ⟨9⟩ [31] (.owned .variant [.variant ⟨7⟩ (.cons F (.cons (.tuple .nil) .nil))] [1])
        [30]] [31])] [13]

/-- The negation of the condition goes to the second region: `last`. -/
def «R-TY9a-last» := check [elements] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (element 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] (natural 1) [],
  .op ⟨4⟩ [13] less [11, 12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [] [10])
    (.mk [] [
      .op ⟨6⟩ [20] (length elements) [0],
      .op ⟨7⟩ [21] (natural 1) [],
      .op ⟨8⟩ [22] minus [20, 21],
      .op ⟨9⟩ [23] (item elements) [0, 22]] [23])] [14]

/-- A fact about an arithmetic expression, by its text. -/
def «R-TY4a» := check [elements, .nat, .nat] [elements] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] plus [1, 2],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [11, 10],
  .op ⟨4⟩ [13] negation [12],
  .guard ⟨5⟩ () 13 .refused,
  .op ⟨6⟩ [14] plus [1, 2],
  .op ⟨7⟩ [15] (slice elements elements) [0, 1, 14]] [15]

/-- A range fact on an arithmetic text is intersected with its computed range. -/
def «V-G2» := check [.fin 10, .fin 5, .fin 5] [.nat] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 5) [2],
  .op ⟨2⟩ [11] (toNat 5) [1],
  .op ⟨3⟩ [12] less [11, 10],
  .op ⟨4⟩ [13] negation [12],
  .guard ⟨5⟩ () 13 .refused,
  .op ⟨6⟩ [14] minus [11, 10],
  .op ⟨7⟩ [15] (natural 1) [],
  .op ⟨8⟩ [16] less [14, 15],
  .op ⟨9⟩ [17] negation [16],
  .guard ⟨10⟩ () 17 .refused,
  .op ⟨11⟩ [18] (toNat 10) [0],
  .op ⟨12⟩ [19] (toNat 5) [1],
  .op ⟨13⟩ [20] (toNat 5) [2],
  .op ⟨14⟩ [21] minus [19, 20],
  .op ⟨15⟩ [22] quotient [18, 21]] [22]

/-- A range fact on an arithmetic term bounds an index written with the same text. -/
def «N-TY8d» := check [bytes 8, .fin 128, .fin 8] [.nat] false <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (toNat 128) [1],
  .op ⟨2⟩ [11] (toNat 8) [2],
  .op ⟨3⟩ [12] plus [10, 11],
  .op ⟨4⟩ [13] (natural 8) [],
  .op ⟨5⟩ [14] less [12, 13],
  .choose ⟨6⟩ () 14 [15]
    (.mk [] [
      .op ⟨7⟩ [20] (toNat 128) [1],
      .op ⟨8⟩ [21] (toNat 8) [2],
      .op ⟨9⟩ [22] plus [20, 21],
      .op ⟨10⟩ [23] (item (bytes 8)) [0, 22],
      .op ⟨11⟩ [24] (toNat 256) [23]] [24])
    (.mk [] [.op ⟨12⟩ [30] (natural 0) []] [30])] [15]

/-- A strided slice after a guard. -/
def «T-Z8» := check [sizedElements 16, .nat] [sizedElements 4] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 4) [],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .reject,
  .op ⟨4⟩ [12] (natural 4) [],
  .op ⟨5⟩ [13] times [12, 1],
  .op ⟨6⟩ [14] (natural 4) [],
  .op ⟨7⟩ [15] times [14, 1],
  .op ⟨8⟩ [16] (natural 4) [],
  .op ⟨9⟩ [17] plus [15, 16],
  .op ⟨10⟩ [18] (slice (sizedElements 16) (sizedElements 4)) [0, 13, 17]] [18]

/-- `T-Z8` with the end of the slice written `4 + 4 * r`: the sum is read with its operands in
either order. -/
def stridedSliceExchanged := check [sizedElements 16, .nat] [sizedElements 4] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 4) [],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .reject,
  .op ⟨4⟩ [12] (natural 4) [],
  .op ⟨5⟩ [13] times [12, 1],
  .op ⟨6⟩ [14] (natural 4) [],
  .op ⟨7⟩ [15] times [14, 1],
  .op ⟨8⟩ [16] (natural 4) [],
  .op ⟨9⟩ [17] plus [16, 15],
  .op ⟨10⟩ [18] (slice (sizedElements 16) (sizedElements 4)) [0, 13, 17]] [18]

/-- The minimal dynamic read. -/
def «I-4» := check [elements] [F] true <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .guard ⟨4⟩ () 12 .reject,
  .op ⟨5⟩ [13] (natural 0) [],
  .op ⟨6⟩ [14] (item elements) [0, 13]] [14]

/-- The length known equal to a number gives the sized type. -/
def «N-TY4b» := check [elements] [sizedElements 8] true <| .mk [0] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] (natural 8) [],
  .op ⟨3⟩ [12] equal [10, 11],
  .guard ⟨4⟩ () 12 .refused,
  .op ⟨5⟩ [13] (sizedAs 8) [0]] [13]

/-- An element known not to be zero is in the domain of the inverse. -/
def «N-TY4c» := check [F] [F] true <| .mk [0] [
  .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
  .guard ⟨2⟩ () 10 .refused,
  .op ⟨3⟩ [11] (element 1) [],
  .op ⟨4⟩ [12] (fieldRow .inverse) [0],
  .op ⟨5⟩ [13] (fieldRow .mul) [11, 12]] [13]

/-- An index that is a natural of no known range. -/
def «T-Z6» := check [sizedElements 8, .nat] [F] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (item (sizedElements 8)) [0, 1]] [10]

/-- A read without the guard. -/
def «I-4b» := check [elements] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (item elements) [0, 10]] [11]

/-- The fact is about one sequence, not another. -/
def «I-4c» := check [elements, elements] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .guard ⟨4⟩ () 12 .reject,
  .op ⟨5⟩ [13] (natural 0) [],
  .op ⟨6⟩ [14] (item elements) [1, 13]] [14]

/-- `length(xs) - 1` needs `1 <= length(xs)`. -/
def «V-F15» := check [elements] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] (natural 1) [],
  .op ⟨3⟩ [12] minus [10, 11],
  .op ⟨4⟩ [13] (item elements) [0, 12]] [13]

/-- The same value on both sides of a difference. -/
def «V-F6» := check [.nat, .nat] [.nat] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] plus [0, 1],
  .op ⟨2⟩ [11] minus [10, 10]] [11]

/-- The range of a sum fits an index type. -/
def «N-TY8e» := check [.fin 8] [.fin 9] false <| .mk [0] [
  .op ⟨1⟩ [10] (toNat 8) [0],
  .op ⟨2⟩ [11] (natural 1) [],
  .op ⟨3⟩ [12] plus [10, 11],
  .op ⟨4⟩ [13] (narrowTo 9) [12]] [13]

/-- The range of a sum that does not fit. -/
def «N-TY8f» := check [.fin 8] [.fin 8] false <| .mk [0] [
  .op ⟨1⟩ [10] (toNat 8) [0],
  .op ⟨2⟩ [11] (natural 1) [],
  .op ⟨3⟩ [12] plus [10, 11],
  .op ⟨4⟩ [13] (narrowTo 8) [12]] [13]

/-- `xs[i * i - i]` over a loop's index: the difference needs `i <= i * i`. -/
def «N-TY10c» := check [bytes 10] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 4) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] times [20, 20],
      .op ⟨4⟩ [23] minus [22, 20],
      .op ⟨5⟩ [24] (item (bytes 10)) [0, 23],
      .op ⟨6⟩ [25] (toNat 256) [24],
      .op ⟨7⟩ [26] plus [21, 25]] [26])] [11]

/-- `a and b` is `if a then b else false`: `b` has the facts of `a`. -/
def «V-F4» := check [elements] [.bool] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [
      .op ⟨5⟩ [20] (natural 0) [],
      .op ⟨6⟩ [21] (item elements) [0, 20],
      .op ⟨7⟩ [22] (element 0) [],
      .op ⟨8⟩ [23] (fieldRow .equal) [21, 22]] [23])
    (.mk [] [.op ⟨9⟩ [30] (truth false) []] [30])] [13]

/-- `a or b` is `if a then true else b`: `b` has the facts of the negation of `a`. -/
def «V-F4b» := check [elements] [.bool] false <| .mk [0] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] (natural 0) [],
  .op ⟨3⟩ [12] equal [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [.op ⟨5⟩ [20] (truth true) []] [20])
    (.mk [] [
      .op ⟨6⟩ [30] (natural 0) [],
      .op ⟨7⟩ [31] (item elements) [0, 30],
      .op ⟨8⟩ [32] (element 0) [],
      .op ⟨9⟩ [33] (fieldRow .equal) [31, 32]] [33])] [13]

/-- The same idiom as `V-F4`, written as a choice: the program is the same. -/
def «V-F4c» := «V-F4»

/-- The right operand of `or` has the facts of the negation of the left. -/
def «N-TY9b» := check [elements, .nat] [.bool] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .op ⟨3⟩ [12] negation [11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [.op ⟨5⟩ [20] (truth true) []] [20])
    (.mk [] [
      .op ⟨6⟩ [21] (item elements) [0, 1],
      .op ⟨7⟩ [22] (element 0) [],
      .op ⟨8⟩ [23] (fieldRow .equal) [21, 22]] [23])] [13]

/-- The second region of a choice on `not (i < n)` has `i < n`. -/
def «V-F8» := check [elements, .nat] [F] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (element 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [1, 11],
  .op ⟨4⟩ [13] negation [12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [] [10])
    (.mk [] [.op ⟨6⟩ [20] (item elements) [0, 1]] [20])] [14]

/-- `and` gives the facts of its left operand to its right operand, not the reverse. -/
def «N-TY9a» := check [elements] [.bool] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (item elements) [0, 10],
  .op ⟨3⟩ [12] (element 0) [],
  .op ⟨4⟩ [13] (fieldRow .equal) [11, 12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [
      .op ⟨6⟩ [20] (natural 0) [],
      .op ⟨7⟩ [21] (length elements) [0],
      .op ⟨8⟩ [22] less [20, 21]] [22])
    (.mk [] [.op ⟨9⟩ [30] (truth false) []] [30])] [14]

/-- The fact does not hold in the other region. -/
def «R-TY9b» := check [elements] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [.op ⟨5⟩ [20] (element 0) []] [20])
    (.mk [] [
      .op ⟨6⟩ [30] (natural 0) [],
      .op ⟨7⟩ [31] (item elements) [0, 30]] [31])] [13]

/-- The negation of `i != n` is `i == n`, which does not give `i < n`. -/
def «V-F7» := check [elements, .nat] [F] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (element 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] equal [1, 11],
  .op ⟨4⟩ [13] negation [12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [] [10])
    (.mk [] [.op ⟨6⟩ [20] (item elements) [0, 1]] [20])] [14]

/-- No fact from the negation of a conjunction. -/
def «V-F10» := check [elements, .nat, .nat] [F] false <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] (element 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [1, 11],
  .op ⟨4⟩ [13] negation [12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [
      .op ⟨6⟩ [20] (length elements) [0],
      .op ⟨7⟩ [21] less [2, 20],
      .op ⟨8⟩ [22] negation [21]] [22])
    (.mk [] [.op ⟨9⟩ [30] (truth false) []] [30]),
  .choose ⟨10⟩ () 14 [15]
    (.mk [] [] [10])
    (.mk [] [.op ⟨11⟩ [40] (item elements) [0, 1]] [40])] [15]

/-- The fact of a choice's region does not leave it. -/
def «V-F11» := check [elements, .nat] [F] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .choose ⟨3⟩ () 11 [12]
    (.mk [] [.op ⟨4⟩ [20] (natural 0) []] [20])
    (.mk [] [.op ⟨5⟩ [30] (natural 1) []] [30]),
  .op ⟨6⟩ [13] (item elements) [0, 1]] [13]

/-- A fact made in one region does not leave it. -/
def «I-4f» := check [elements, .bool] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (element 0) [],
  .choose ⟨2⟩ () 1 [11]
    (.mk [] [
      .op ⟨3⟩ [20] (natural 0) [],
      .op ⟨4⟩ [21] (length elements) [0],
      .op ⟨5⟩ [22] less [20, 21],
      .guard ⟨6⟩ () 22 .reject,
      .op ⟨7⟩ [23] (item elements) [0, 20]] [23])
    (.mk [] [] [10]),
  .op ⟨8⟩ [12] (natural 0) [],
  .op ⟨9⟩ [13] (item elements) [0, 12],
  .op ⟨10⟩ [14] (fieldRow .add) [11, 13]] [14]

/-- A loop over the rows of a sized sequence of sequences, and inside it a loop over
`0..length(row)`: the count is `length(row) - 0`, and the index is `0 + t` for the loop's
own index `t`. -/
def «I-4e-total» := check [.seq elements (some 3)] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (element 0) [],
  .loop ⟨2⟩ () (.fixed 3) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (item (.seq elements (some 3))) [0, 20],
      .op ⟨4⟩ [23] (natural 0) [],
      .op ⟨5⟩ [24] (length elements) [22],
      .op ⟨6⟩ [25] minus [24, 23],
      .loop ⟨7⟩ () (.count 25) [21] [26]
        (.mk [30, 31] [
          .op ⟨8⟩ [32] plus [23, 30],
          .op ⟨9⟩ [33] (item elements) [22, 32],
          .op ⟨10⟩ [34] (fieldRow .add) [31, 33]] [34])] [26])] [11]

/-- `I-4e-total` with the index written `t + 0`: the sum is read with its operands in either
order. -/
def totalExchanged := check [.seq elements (some 3)] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (element 0) [],
  .loop ⟨2⟩ () (.fixed 3) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (item (.seq elements (some 3))) [0, 20],
      .op ⟨4⟩ [23] (natural 0) [],
      .op ⟨5⟩ [24] (length elements) [22],
      .op ⟨6⟩ [25] minus [24, 23],
      .loop ⟨7⟩ () (.count 25) [21] [26]
        (.mk [30, 31] [
          .op ⟨8⟩ [32] plus [30, 23],
          .op ⟨9⟩ [33] (item elements) [22, 32],
          .op ⟨10⟩ [34] (fieldRow .add) [31, 33]] [34])] [26])] [11]

/-- A slice from a position to the end. -/
def «I-4e-tail» := check [elements, .nat] [elements] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [10, 1],
  .op ⟨3⟩ [12] negation [11],
  .guard ⟨4⟩ () 12 .reject,
  .op ⟨5⟩ [13] (length elements) [0],
  .op ⟨6⟩ [14] (slice elements elements) [0, 1, 13]] [14]

/-- A loop of a written count indexes a sized sequence by its index. -/
def «N-TY10e» := check [bytes 1024] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 1024) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (item (bytes 1024)) [0, 20],
      .op ⟨4⟩ [23] (toNat 256) [22],
      .op ⟨5⟩ [24] plus [21, 23]] [24])] [11]

/-- The carried sum has the range of the sum after the loop. -/
def «N-TY10g» := check [bytes 4] [.fin 1024] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 4) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (item (bytes 4)) [0, 20],
      .op ⟨4⟩ [23] (toNat 256) [22],
      .op ⟨5⟩ [24] plus [21, 23]] [24]),
  .op ⟨6⟩ [12] (narrowTo 1024) [11]] [12]

/-- A sum of weighted bytes, `∑ i ∈ 0..count, units[i] * 256^i`, of `count` terms. The index is
an operand of arithmetic in the element, so the sum is its iterations in sequence, each with the
index a literal, and its range is taken index by index (`LANGUAGE.md`, TY8, the row of `∑`; §7.5,
stepped loops). The sum starts at `0`, named `1999`, and the sum of the first `k + 1` terms is
`2000 + k`. -/
def weighted (count : Nat) : Region (LocalRaw field) Unit :=
  .mk [0] (terms ++ [.op ⟨1000⟩ [3000] (narrowTo (2 ^ 64)) [total]]) [3000]
where
  /-- The name of the sum of the first `k + 1` terms. -/
  total : Nat := 2000 + (count - 1)
  terms : List (Instruction (LocalRaw field) Unit) :=
    (List.range count).flatMap fun k =>
      [.op ⟨10 * k + 1⟩ [100 * k + 10] (natural k) [],
       .op ⟨10 * k + 2⟩ [100 * k + 11] (item (bytes count)) [0, 100 * k + 10],
       .op ⟨10 * k + 3⟩ [100 * k + 12] (toNat 256) [100 * k + 11],
       .op ⟨10 * k + 4⟩ [100 * k + 13] (natural 256) [],
       .op ⟨10 * k + 5⟩ [100 * k + 14] power [100 * k + 13, 100 * k + 10],
       .op ⟨10 * k + 6⟩ [100 * k + 15] times [100 * k + 12, 100 * k + 14]] ++
      (if k = 0 then [.op ⟨10 * k + 7⟩ [1999] (natural 0) [],
          .op ⟨10 * k + 8⟩ [2000] plus [1999, 15]]
        else [.op ⟨10 * k + 7⟩ [2000 + k] plus [2000 + (k - 1), 100 * k + 15]])

/-- Eight bytes weighted by powers of 256 are below `2^64`. -/
def «N-TY8g» := check [bytes 8] [.fin (2 ^ 64)] false (weighted 8)

/-- Nine are not. -/
def «N-TY8h» := check [bytes 9] [.fin (2 ^ 64)] false (weighted 9)

/-- A copy taken before the update keeps its fact. -/
def «V-F1d» := check [elements, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .refused,
  .op ⟨4⟩ [12] (natural 100) [],
  .op ⟨5⟩ [13] plus [1, 12],
  .op ⟨6⟩ [14] (item elements) [0, 1]] [14]

/-- A fact on `i + 1`, then `i` updated: the updated value has its own name, `17`. -/
def «V-F1» := check [elements, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] plus [1, 10],
  .op ⟨3⟩ [12] (length elements) [0],
  .op ⟨4⟩ [13] less [12, 11],
  .op ⟨5⟩ [14] negation [13],
  .guard ⟨6⟩ () 14 .refused,
  .op ⟨7⟩ [15] (natural 100) [],
  .op ⟨8⟩ [17] plus [1, 15],
  .op ⟨9⟩ [16] (item elements) [0, 17]] [16]

/-- A name narrowed by a guard, then updated: the updated value has its own name, `14`. -/
def «V-F1b» := check [elements, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .refused,
  .op ⟨4⟩ [12] (natural 100) [],
  .op ⟨5⟩ [14] plus [1, 12],
  .op ⟨6⟩ [13] (item elements) [0, 14]] [13]

/-- A name with a range from a guard, then updated: the updated value has its own name, `14`. -/
def «V-F1c» := check [sizedElements 8, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 8) [],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .refused,
  .op ⟨4⟩ [12] (natural 100) [],
  .op ⟨5⟩ [14] plus [1, 12],
  .op ⟨6⟩ [13] (item (sizedElements 8)) [0, 14]] [13]

/-- Three guards: the order asked for is one of them. -/
def «facts-direct-order» := check [.nat, .nat, .nat] [.nat] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] less [1, 0],
  .op ⟨2⟩ [11] negation [10],
  .guard ⟨3⟩ () 11 .reject,
  .op ⟨4⟩ [12] less [2, 1],
  .op ⟨5⟩ [13] negation [12],
  .guard ⟨6⟩ () 13 .reject,
  .op ⟨7⟩ [14] less [2, 0],
  .op ⟨8⟩ [15] negation [14],
  .guard ⟨9⟩ () 15 .reject,
  .op ⟨10⟩ [16] minus [2, 0]] [16]

/-- Two guards: the order asked for follows from them only by transitivity. -/
def «facts-no-transitivity» := check [.nat, .nat, .nat] [.nat] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] less [1, 0],
  .op ⟨2⟩ [11] negation [10],
  .guard ⟨3⟩ () 11 .reject,
  .op ⟨4⟩ [12] less [2, 1],
  .op ⟨5⟩ [13] negation [12],
  .guard ⟨6⟩ () 13 .reject,
  .op ⟨7⟩ [14] minus [2, 0]] [14]

/-- A fact on `i + 1` holds of `1 + i`: the table places the operands of a sum in one order, so
the two are one value. (The reference's case `facts-no-commutativity-recovery` refuses this: a
check that keeps the operands in the order written does not recover it.) -/
def «facts-commutativity-recovered» := check [naturals 8, .nat] [.nat] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] plus [1, 10],
  .op ⟨3⟩ [12] (natural 8) [],
  .op ⟨4⟩ [13] less [11, 12],
  .guard ⟨5⟩ () 13 .reject,
  .op ⟨6⟩ [14] (natural 1) [],
  .op ⟨7⟩ [15] plus [14, 1],
  .op ⟨8⟩ [16] (item (naturals 8)) [0, 15]] [16]

/-! ### The verdicts -/

example : «T-Z7» = accepted := by decide +kernel
example : «V-F16» = accepted := by decide +kernel
example : «R-TY9a-head» = accepted := by decide +kernel
example : «R-TY9a-last» = accepted := by decide +kernel
example : «R-TY4a» = accepted := by decide +kernel
example : «V-G2» = accepted := by decide +kernel
example : «N-TY8d» = accepted := by decide +kernel
example : «T-Z8» = accepted := by decide +kernel
example : stridedSliceExchanged = accepted := by decide +kernel
example : «I-4» = accepted := by decide +kernel
example : «N-TY4b» = accepted := by decide +kernel
example : «N-TY4c» = accepted := by decide +kernel
example : «T-Z6» = some (.inl
    [unjustified 1 (item (sizedElements 8)) (.below (.arg 1) 8) [anyNat]]) := by decide +kernel
example : «I-4b» = some (.inl
    [unjustified 2 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide +kernel
example : «I-4c» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide +kernel
/-- One refusal, at the difference: the index is `length(xs) - u` with `1 <= u`. -/
example : «V-F15» = some (.inl
    [unjustified 3 minus (.le (.arg 1) (.arg 0)) [some (Range.point 1), anyNat]]) := by
  decide +kernel
example : «V-F6» = accepted := by decide +kernel
example : «N-TY8e» = accepted := by decide +kernel
example : «N-TY8f» = some (.inl
    [unjustified 4 (narrowTo 8) (.below (.arg 0) 8) [some ⟨1, some 8⟩]]) := by decide +kernel
/-- One refusal, at the difference; the index is then below 10 by its range. -/
example : «N-TY10c» = some (.inl
    [unjustified 4 minus (.le (.arg 1) (.arg 0)) [some ⟨0, some 3⟩, some ⟨0, some 9⟩]]) := by
  decide +kernel
example : «V-F4» = accepted := by decide +kernel
example : «V-F4b» = accepted := by decide +kernel
example : «V-F4c» = accepted := by decide +kernel
example : «N-TY9b» = accepted := by decide +kernel
example : «V-F8» = accepted := by decide +kernel
example : «N-TY9a» = some (.inl
    [unjustified 2 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide +kernel
/-- In the second region the length is at most zero. -/
example : «R-TY9b» = some (.inl
    [unjustified 7 (item elements) (.lt (.arg 1) lengthOf)
      [some (Range.point 0), some ⟨0, some 0⟩]]) := by
  decide +kernel
example : «V-F7» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide +kernel
example : «V-F10» = some (.inl
    [unjustified 11 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide +kernel
example : «V-F11» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide +kernel
example : «I-4f» = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide +kernel
example : «I-4e-total» = accepted := by decide +kernel
example : totalExchanged = accepted := by decide +kernel
example : «I-4e-tail» = accepted := by decide +kernel
example : «N-TY10e» = accepted := by decide +kernel
example : «N-TY10g» = accepted := by decide +kernel
example : «N-TY8g» = accepted := by decide +kernel
example : «N-TY8h» = some (.inl
    [unjustified 1000 (narrowTo (2 ^ 64)) (.below (.arg 0) (2 ^ 64))
      [some ⟨0, some (2 ^ 72 - 1)⟩]]) := by
  decide +kernel
example : «V-F1d» = accepted := by decide +kernel
example : «V-F1» = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf)
      [some ⟨100, none⟩, anyNat]]) := by
  decide +kernel
example : «V-F1b» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf)
      [some ⟨100, none⟩, anyNat]]) := by
  decide +kernel
example : «V-F1c» = some (.inl
    [unjustified 6 (item (sizedElements 8)) (.below (.arg 1) 8) [some ⟨100, some 107⟩]]) := by
  decide +kernel
example : «facts-direct-order» = accepted := by decide +kernel
example : «facts-no-transitivity» = some (.inl
    [unjustified 7 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by decide +kernel
example : «facts-commutativity-recovered» = accepted := by decide +kernel

/-- A restricted operation is shared, and checked again where it is applied again: justified in
one region and applied in the other, it is refused there. -/
example : check [.nat, .nat, .bool] [.nat] true (.mk [0, 1, 2] [
    .choose ⟨1⟩ () 2 [10]
      (.mk [] [
        .op ⟨2⟩ [20] less [0, 1],
        .op ⟨3⟩ [21] negation [20],
        .guard ⟨4⟩ () 21 .reject,
        .op ⟨5⟩ [22] minus [0, 1]] [22])
      (.mk [] [.op ⟨6⟩ [30] minus [0, 1]] [30])] [10]) =
    some (.inl [unjustified 6 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by
  decide +kernel

/-- A call is shared: a fact about its result holds of the same call again. -/
example : verdict [⟨⟨1⟩, [.nat], [.nat], false, none⟩] ⟨⟨2⟩, [elements, .nat], [F], true, none⟩
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (.call ⟨1⟩) [1],
      .op ⟨2⟩ [11] (length elements) [0],
      .op ⟨3⟩ [12] less [10, 11],
      .guard ⟨4⟩ () 12 .reject,
      .op ⟨5⟩ [13] (.call ⟨1⟩) [1],
      .op ⟨6⟩ [14] (item elements) [0, 13]] [14]) = accepted := by
  decide +kernel

/-! ## Each operation with a domain, and a restricted row -/

/-- The difference, after a guard that the second is at most the first. -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] less [0, 1],
    .op ⟨2⟩ [11] negation [10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] minus [0, 1]] [12]) = accepted := by
  decide +kernel

example : check [.nat, .nat] [.nat] false (.mk [0, 1] [.op ⟨1⟩ [10] minus [0, 1]] [10]) =
    some (.inl [unjustified 1 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by
  decide +kernel

/-- The quotient by a sum with one. -/
example : check [.nat, .nat] [.nat] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 1) [],
    .op ⟨2⟩ [11] plus [1, 10],
    .op ⟨3⟩ [12] quotient [0, 11]] [12]) = accepted := by
  decide +kernel

example : check [.nat, .nat] [.nat] false (.mk [0, 1] [.op ⟨1⟩ [10] quotient [0, 1]] [10]) =
    some (.inl [unjustified 1 quotient (.atLeast (.arg 1) 1) [anyNat]]) := by
  decide +kernel

/-- The remainder by a written number. -/
example : check [.nat] [.nat] false (.mk [0] [
    .op ⟨1⟩ [10] (natural 7) [],
    .op ⟨2⟩ [11] remainder [0, 10]] [11]) = accepted := by
  decide +kernel

example : check [.nat, .fin 3] [.nat] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 3) [1],
    .op ⟨2⟩ [11] remainder [0, 10]] [11]) =
    some (.inl [unjustified 2 remainder (.atLeast (.arg 1) 1) [some ⟨0, some 2⟩]]) := by
  decide +kernel

/-- An item of a sized sequence at an index of its size. -/
example : check [sizedElements 8, .fin 8] [F] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 8) [1],
    .op ⟨2⟩ [11] (item (sizedElements 8)) [0, 10]] [11]) = accepted := by
  decide +kernel

example : check [sizedElements 8, .fin 9] [F] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 9) [1],
    .op ⟨2⟩ [11] (item (sizedElements 8)) [0, 10]] [11]) =
    some (.inl [unjustified 2 (item (sizedElements 8)) (.below (.arg 1) 8)
      [some ⟨0, some 8⟩]]) := by
  decide +kernel

/-- A slice with nothing known of its bounds: both orders refused. -/
example : check [elements, .nat, .nat] [elements] false (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (slice elements elements) [0, 1, 2]] [10]) =
    some (.inl [unjustified 1 (slice elements elements) (.le (.arg 1) (.arg 2)) [anyNat, anyNat],
      unjustified 1 (slice elements elements) (.le (.arg 2) lengthOf) [anyNat, anyNat]]) := by
  decide +kernel

/-- A slice of a sized result whose bounds differ by another number. -/
example : check [sizedElements 16, .fin 8] [sizedElements 4] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 8) [1],
    .op ⟨2⟩ [11] (natural 3) [],
    .op ⟨3⟩ [12] plus [10, 11],
    .op ⟨4⟩ [13] (slice (sizedElements 16) (sizedElements 4)) [0, 10, 12]] [13]) =
    some (.inl [unjustified 4 (slice (sizedElements 16) (sizedElements 4))
      (.difference (.arg 2) (.arg 1) 4) [some ⟨3, some 10⟩, some ⟨0, some 7⟩]]) := by
  decide +kernel

/-- A sequence given a size with nothing known of its length. -/
example : check [elements] [sizedElements 8] false (.mk [0] [
    .op ⟨1⟩ [10] (sizedAs 8) [0]] [10]) =
    some (.inl [unjustified 1 (sizedAs 8) (.exactly lengthOf 8) [anyNat]]) := by
  decide +kernel

/-- The inverse of an element known not to be zero is `N-TY4c`; without the guard it is
refused. -/
example : check [F] [F] false (.mk [0] [.op ⟨1⟩ [10] (fieldRow .inverse) [0]] [10]) =
    some (.inl [unjustified 1 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]]) := by
  decide +kernel

/-! ## Regions, loops and names -/

/-- Sibling regions that each compute `length(xs)` and index after their own guard. -/
def siblings (secondIndex : Nat) (secondGuarded : Bool) :=
  check [elements, .bool, .nat, .nat] [F] true <| .mk [0, 1, 2, 3] [
  .choose ⟨1⟩ () 1 [10]
    (.mk [] [
      .op ⟨2⟩ [20] (length elements) [0],
      .op ⟨3⟩ [21] less [2, 20],
      .guard ⟨4⟩ () 21 .reject,
      .op ⟨5⟩ [22] (item elements) [0, 2]] [22])
    (.mk [] ((if secondGuarded then [
      .op ⟨6⟩ [30] (length elements) [0],
      .op ⟨7⟩ [31] less [secondIndex, 30],
      .guard ⟨8⟩ () 31 .reject] else []) ++
      [.op ⟨9⟩ [32] (item elements) [0, secondIndex]]) [32])] [10]

example : siblings 3 true = accepted := by decide +kernel
/-- The second region indexes by another value with no guard. -/
example : siblings 3 false = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide +kernel
/-- The second region indexes by the first region's index with no guard. -/
example : siblings 2 false = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide +kernel

/-- A loop of no iteration whose body guards and indexes; after it the index is refused. -/
example : check [elements, .nat] [F] true (.mk [0, 1] [
    .loop ⟨1⟩ () (.fixed 0) [] []
      (.mk [20] [
        .op ⟨2⟩ [21] (length elements) [0],
        .op ⟨3⟩ [22] less [1, 21],
        .guard ⟨4⟩ () 22 .reject,
        .op ⟨5⟩ [23] (item elements) [0, 1]] []),
    .op ⟨6⟩ [10] (item elements) [0, 1]] [10]) =
    some (.inl [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by
  decide +kernel

/-- The guard before the loop justifies the index in its body. -/
example : check [elements, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (length elements) [0],
    .op ⟨2⟩ [11] less [1, 10],
    .guard ⟨3⟩ () 11 .reject,
    .loop ⟨4⟩ () (.fixed 2) [] []
      (.mk [20] [.op ⟨5⟩ [21] (item elements) [0, 1]] [])] [1]) = accepted := by
  decide +kernel

/-- A loop as often as a length indexes by its index; the count has no upper bound, and a
function's loop is not refused for that. -/
example : check [elements] [.nat] false (.mk [0] [
    .op ⟨1⟩ [10] (length elements) [0],
    .loop ⟨2⟩ () (.count 10) [] []
      (.mk [20] [.op ⟨3⟩ [21] (item elements) [0, 20]] [])] [10]) = accepted := by
  decide +kernel

/-- A loop as often as a natural known below 10 has the bound 9. -/
example : check [.nat] [.nat] true (.mk [0] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [0, 10],
    .guard ⟨3⟩ () 11 .reject,
    .loop ⟨4⟩ () (.count 0) [] [] (.mk [20] [] [])] [0]) = some (.inr [(place 4, 9)]) := by
  decide +kernel

/-- A value carried by a loop, known below the length before it: inside the loop, after it,
and the value it starts from inside it. -/
def carried (inside : Bool) (byCarried : Bool) :=
  check [elements, .nat] [F] true <| .mk [0, 1] ([
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .reject,
  .loop ⟨4⟩ () (.fixed 3) [1] [12]
    (.mk [20, 21] (if inside then
      [.op ⟨5⟩ [22] (item elements) [0, if byCarried then 21 else 1]] else []) [21])] ++
  (if inside then [] else [.op ⟨6⟩ [13] (item elements) [0, 12]]) ++
  [.op ⟨7⟩ [14] (item elements) [0, 1]]) [14]

example : carried true true = some (.inl
    [unjustified 5 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by
  decide +kernel
example : carried true false = accepted := by decide +kernel
example : carried false true = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by
  decide +kernel

/-- `c := (0 < length(xs)) and (xs[0] == 0)`, then `guard c` and `xs[0]` again; without the
guard; and the conjunction reversed. -/
def shortCircuit (guarded reversed : Bool) :=
  check [elements] [F] guarded <| .mk [0] ((if reversed then [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (item elements) [0, 10],
  .op ⟨3⟩ [12] (element 0) [],
  .op ⟨4⟩ [13] (fieldRow .equal) [11, 12],
  .choose ⟨5⟩ () 13 [14]
    (.mk [] [
      .op ⟨6⟩ [20] (length elements) [0],
      .op ⟨7⟩ [21] less [10, 20]] [21])
    (.mk [] [.op ⟨8⟩ [30] (truth false) []] [30])] else [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨5⟩ () 12 [14]
    (.mk [] [
      .op ⟨6⟩ [20] (item elements) [0, 10],
      .op ⟨7⟩ [21] (element 0) [],
      .op ⟨4⟩ [22] (fieldRow .equal) [20, 21]] [22])
    (.mk [] [.op ⟨8⟩ [30] (truth false) []] [30])]) ++
  (if guarded then [.guard ⟨9⟩ () 14 .reject] else []) ++
  [.op ⟨10⟩ [15] (natural 0) [],
   .op ⟨11⟩ [16] (item elements) [0, 15]]) [16]

example : shortCircuit true false = accepted := by decide +kernel
example : shortCircuit false false = some (.inl
    [unjustified 11 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide +kernel
example : shortCircuit true true = some (.inl
    [unjustified 2 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide +kernel

/-- A fact about one sequence does not justify indexing another of the same type. -/
example : check [elements, elements, .nat] [F] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (length elements) [0],
    .op ⟨2⟩ [11] less [2, 10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] (item elements) [1, 2]] [12]) =
    some (.inl [unjustified 4 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by
  decide +kernel

/-- `x := i + 1; guard x < length(xs)`, then the instruction given, and `xs[index]`. -/
def afterGuard (again : List (Instruction (LocalRaw field) Unit)) (index : Nat) :
    Region (LocalRaw field) Unit :=
  .mk [0, 1] ([
  .op ⟨1⟩ [11] (natural 1) [],
  .op ⟨2⟩ [10] plus [1, 11],
  .op ⟨3⟩ [12] (length elements) [0],
  .op ⟨4⟩ [13] less [10, 12],
  .guard ⟨5⟩ () 13 .reject,
  .op ⟨6⟩ [14] (natural 1) []] ++ again ++ [
  .op ⟨8⟩ [15] (item elements) [0, index]]) [15]

/-- `x` bound again, to `x + 1`, to `i + 1` and to `1 + i`: each refused by the rule `assignment`
at the instruction that binds it again, with its name. -/
example : elaborationRefusal [elements, .nat] [F] true (afterGuard [.op ⟨7⟩ [10] plus [10, 14]] 10) =
    some ⟨.assignment, place 7, .name 10⟩ := by
  decide +kernel
example : elaborationRefusal [elements, .nat] [F] true (afterGuard [.op ⟨7⟩ [10] plus [1, 14]] 10) =
    some ⟨.assignment, place 7, .name 10⟩ := by
  decide +kernel
example : elaborationRefusal [elements, .nat] [F] true (afterGuard [.op ⟨7⟩ [10] plus [14, 1]] 10) =
    some ⟨.assignment, place 7, .name 10⟩ := by
  decide +kernel

/-- A new name `16` bound to `x + 1`, to `i + 1` and to `1 + i`, and `xs[16]`: the fact on `x`
says nothing of `x + 1`; it holds of `i + 1`, the same written computation as `x`; and of
`1 + i`, which the table places as `i + 1`. -/
example : check [elements, .nat] [F] true (afterGuard [.op ⟨7⟩ [16] plus [10, 14]] 16) = some (.inl
    [unjustified 8 (item elements) (.lt (.arg 1) lengthOf) [some ⟨2, none⟩, anyNat]]) := by
  decide +kernel
example : check [elements, .nat] [F] true (afterGuard [.op ⟨7⟩ [16] plus [1, 14]] 16) = accepted := by
  decide +kernel
example : check [elements, .nat] [F] true (afterGuard [.op ⟨7⟩ [16] plus [14, 1]] 16) = accepted := by
  decide +kernel


/-! ## A loop over a range whose end is a run-time value -/

/-- `for i in a..b: xs[i]` with `a: index<6>` and `b: index<11>`, after `guard a <= b`: a loop as
often as `b - a`, whose index is `a` plus the iteration number. The order that the loop makes
for the iteration number, below `b - a`, gives `a + t` the range below `b`'s, `0..9` (TY10), and
the read of `xs` of the size given is decided by it. -/
def runtimeEnd (size : Nat) := check [sizedElements size, .fin 6, .fin 11] [.nat] true <|
  .mk [0, 1, 2] [
    .op ⟨1⟩ [10] (toNat 6) [1],
    .op ⟨2⟩ [11] (toNat 11) [2],
    .op ⟨3⟩ [12] less [11, 10],
    .op ⟨4⟩ [13] negation [12],
    .guard ⟨5⟩ () 13 .refused,
    .op ⟨6⟩ [14] minus [11, 10],
    .loop ⟨7⟩ () (.count 14) [] []
      (.mk [20] [
        .op ⟨8⟩ [21] plus [10, 20],
        .op ⟨9⟩ [22] (item (sizedElements size)) [0, 21]] [])] [10]

/-- On `[F; 10]` the read is accepted; the loop runs at most `hi(b - a) = 10` times. -/
example : runtimeEnd 10 = some (.inr [(place 7, 10)]) := by decide +kernel
/-- On `[F; 9]` it is refused: the index is known in `0..9` only. -/
example : runtimeEnd 9 = some (.inl
    [unjustified 9 (item (sizedElements 9)) (.below (.arg 1) 9) [some ⟨0, some 9⟩]]) := by
  decide +kernel

/-- The same loop with the index written `t + a`: the sum is read with its operands in either
order, and gets the same range. -/
def runtimeEndExchanged (size : Nat) :=
  check [sizedElements size, .fin 6, .fin 11] [.nat] true <| .mk [0, 1, 2] [
    .op ⟨1⟩ [10] (toNat 6) [1],
    .op ⟨2⟩ [11] (toNat 11) [2],
    .op ⟨3⟩ [12] less [11, 10],
    .op ⟨4⟩ [13] negation [12],
    .guard ⟨5⟩ () 13 .refused,
    .op ⟨6⟩ [14] minus [11, 10],
    .loop ⟨7⟩ () (.count 14) [] []
      (.mk [20] [
        .op ⟨8⟩ [21] plus [20, 10],
        .op ⟨9⟩ [22] (item (sizedElements size)) [0, 21]] [])] [10]

/-- On `[F; 10]` the read is accepted, as with `a + t`. -/
example : runtimeEndExchanged 10 = some (.inr [(place 7, 10)]) := by decide +kernel
/-- On `[F; 9]` it is refused with the same range, `0..9`, as with `a + t`. -/
example : runtimeEndExchanged 9 = some (.inl
    [unjustified 9 (item (sizedElements 9)) (.below (.arg 1) 9) [some ⟨0, some 9⟩]]) := by
  decide +kernel

/-- The same order written by hand, `guard t < r - x`, is no loop's: `x + t` gets no range from
it, and the read of `xs[x + t]` on `[F; 10]` is refused with what the sum's operands give. -/
example : check [sizedElements 10, .fin 6, .nat, .fin 11] [F] true (.mk [0, 1, 2, 3] [
    .op ⟨1⟩ [10] (toNat 6) [1],
    .op ⟨2⟩ [11] (toNat 11) [3],
    .op ⟨3⟩ [12] less [11, 10],
    .op ⟨4⟩ [13] negation [12],
    .guard ⟨5⟩ () 13 .refused,
    .op ⟨6⟩ [14] minus [11, 10],
    .op ⟨7⟩ [15] less [2, 14],
    .guard ⟨8⟩ () 15 .refused,
    .op ⟨9⟩ [16] plus [10, 2],
    .op ⟨10⟩ [17] (item (sizedElements 10)) [0, 16]] [17]) = some (.inl
    [unjustified 10 (item (sizedElements 10)) (.below (.arg 1) 10) [anyNat]]) := by
  decide +kernel

/-! ## A power too large to compute -/

/-- `base ^ exponent`, then the result as an `index<bound>`. -/
def powerBelow (base : LocalRaw field) (exponent : LocalRaw field) (bound : Nat) :=
  check [] [.fin bound] false (.mk [] [
    .op ⟨1⟩ [10] base [],
    .op ⟨2⟩ [11] exponent [],
    .op ⟨3⟩ [12] power [10, 11],
    .op ⟨4⟩ [13] (narrowTo bound) [12]] [13])

/-- `2 ^ e` with `e: index<2^64>`: the upper end, `2 ^ (2^64 - 1)`, is not computed (TY8), so
the conversion to `index<5>` is decided at once and refused, the power known from 1. -/
example : check [.fin (2 ^ 64)] [.fin 5] false (.mk [0] [
    .op ⟨1⟩ [10] (natural 2) [],
    .op ⟨2⟩ [11] (toNat (2 ^ 64)) [0],
    .op ⟨3⟩ [12] power [10, 11],
    .op ⟨4⟩ [13] (narrowTo 5) [12]] [13]) = some (.inl
    [unjustified 4 (narrowTo 5) (.below (.arg 0) 5) [some ⟨1, none⟩]]) := by
  decide +kernel

/-- At the limit: `1 ^ 65536` is computed (one binary digit times 65536), and is below 2. -/
example : powerBelow (natural 1) (natural 65536) 2 = accepted := by decide +kernel
/-- Past it: `1 ^ 65537` is not computed, and the power is known from 1 only. -/
example : powerBelow (natural 1) (natural 65537) 2 = some (.inl
    [unjustified 4 (narrowTo 2) (.below (.arg 0) 2) [some ⟨1, none⟩]]) := by
  decide +kernel
/-- At the limit with two binary digits: `2 ^ 32768` is computed, at both ends. -/
example : powerBelow (natural 2) (natural 32768) 5 = some (.inl
    [unjustified 4 (narrowTo 5) (.below (.arg 0) 5) [some (Range.point (2 ^ 32768))]]) := by
  decide +kernel
/-- Past it: `2 ^ 32769` is not computed. -/
example : powerBelow (natural 2) (natural 32769) 5 = some (.inl
    [unjustified 4 (narrowTo 5) (.below (.arg 0) 5) [some ⟨1, none⟩]]) := by
  decide +kernel
/-- A base of `index<1>`, zero, to an exponent of `index<2^64>`: zero is written with one binary
digit, so the upper end is not computed, and the power is known from 0. -/
example : check [.fin 1, .fin (2 ^ 64)] [.fin 5] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 1) [0],
    .op ⟨2⟩ [11] (toNat (2 ^ 64)) [1],
    .op ⟨3⟩ [12] power [10, 11],
    .op ⟨4⟩ [13] (narrowTo 5) [12]] [13]) = some (.inl
    [unjustified 4 (narrowTo 5) (.below (.arg 0) 5) [some ⟨0, none⟩]]) := by
  decide +kernel
/-- A base of `index<2^64>` squared: 64 binary digits twice, so both ends are computed. -/
example : check [.fin (2 ^ 64)] [.fin 5] false (.mk [0] [
    .op ⟨1⟩ [10] (toNat (2 ^ 64)) [0],
    .op ⟨2⟩ [11] (natural 2) [],
    .op ⟨3⟩ [12] power [10, 11],
    .op ⟨4⟩ [13] (narrowTo 5) [12]] [13]) = some (.inl
    [unjustified 4 (narrowTo 5) (.below (.arg 0) 5) [some ⟨0, some ((2 ^ 64 - 1) ^ 2)⟩]]) := by
  decide +kernel

/-! ## What the calculus of facts does not conclude -/

/-- `guard i < n` with `n : index<10>`, then `xs[i]` on `[F; 9]`: the range of `n` is not one
number, so the comparison gives the order only (TY9), and nothing says `i < 9` (TY7). -/
example : check [sizedElements 9, .nat, .fin 10] [F] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (toNat 10) [2],
    .op ⟨2⟩ [11] less [1, 10],
    .guard ⟨3⟩ () 11 .refused,
    .op ⟨4⟩ [12] (item (sizedElements 9)) [0, 1]] [12]) = some (.inl
    [unjustified 4 (item (sizedElements 9)) (.below (.arg 1) 9) [anyNat]]) := by
  decide +kernel

/-- `guard x <= length(xs)`, `guard t < length(xs) - x`, then `xs[x + t]`: the guard on
`t < length(xs) - x` is no loop's order for its index, and nothing concludes `x + t < length(xs)`
(TY4: no arithmetic on both sides). -/
example : check [elements, .nat, .nat] [F] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (length elements) [0],
    .op ⟨2⟩ [11] less [10, 1],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .refused,
    .op ⟨5⟩ [13] minus [10, 1],
    .op ⟨6⟩ [14] less [2, 13],
    .guard ⟨7⟩ () 14 .refused,
    .op ⟨8⟩ [15] plus [1, 2],
    .op ⟨9⟩ [16] (item elements) [0, 15]] [16]) = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by
  decide +kernel

/-- `z / (∑ i ∈ 0..4, 1)`: the sum starts where its initial value starts, at 0 (TY8), so the
divisor is not known to be at least one. -/
example : check [.nat] [.nat] false (.mk [0] [
    .op ⟨1⟩ [10] (natural 0) [],
    .loop ⟨2⟩ () (.fixed 4) [10] [11]
      (.mk [20, 21] [.op ⟨3⟩ [22] (natural 1) [], .op ⟨4⟩ [23] plus [21, 22]] [23]),
    .op ⟨5⟩ [12] quotient [0, 11]] [12]) = some (.inl
    [unjustified 5 quotient (.atLeast (.arg 1) 1) [some ⟨0, some 4⟩]]) := by
  decide +kernel

/-! ## Code that does not run -/

/-- A condition on a loop's index is not decided at the instance: both arms are checked, and
the read in the arm that the index never takes is refused (`N-TY9e`). -/
def «N-TY9e» := check [bytes 4] [.nat] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .loop ⟨2⟩ () (.fixed 1) [10] [11]
    (.mk [20, 21] [
      .op ⟨3⟩ [22] (natural 1) [],
      .op ⟨4⟩ [23] equal [20, 22],
      .choose ⟨5⟩ () 23 [24]
        (.mk [] [
          .op ⟨6⟩ [30] (natural 5) [],
          .op ⟨7⟩ [31] (item (bytes 4)) [0, 30],
          .op ⟨8⟩ [32] (toNat 256) [31],
          .op ⟨9⟩ [33] plus [21, 32]] [33])
        (.mk [] [] [21])] [24])] [11]

example : «N-TY9e» = some (.inl
    [unjustified 7 (item (bytes 4)) (.below (.arg 1) 4) [some (Range.point 5)]]) := by
  decide +kernel

/-- A guard that contradicts what is known of a value does not make what follows dead: the
value has the empty range, and the read by it is refused. -/
example : check [elements, .fin 4] [F] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 4) [1],
    .op ⟨2⟩ [11] (natural 9) [],
    .op ⟨3⟩ [12] less [11, 10],
    .guard ⟨4⟩ () 12 .reject,
    .op ⟨5⟩ [13] (item elements) [0, 10]] [13]) = some (.inl
    [unjustified 5 (item elements) (.lt (.arg 1) lengthOf) [some ⟨10, some 3⟩, anyNat]]) := by
  decide +kernel

/-- `guard n == 0`, then a loop as often as `n`: its body is checked, and the read in it is
refused. -/
example : check [elements, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] equal [1, 10],
    .guard ⟨3⟩ () 11 .reject,
    .loop ⟨4⟩ () (.count 1) [] []
      (.mk [20] [.op ⟨5⟩ [21] (item elements) [0, 20]] [])] [1]) = some (.inl
    [unjustified 5 (item elements) (.lt (.arg 1) lengthOf) [some Range.nothing, anyNat]]) := by
  decide +kernel

/-- The body of a loop of the written count zero does not run: nothing in it is refused. -/
example : check [elements, .nat] [.nat] false (.mk [0, 1] [
    .loop ⟨1⟩ () (.fixed 0) [] []
      (.mk [20] [.op ⟨2⟩ [21] (item elements) [0, 1]] [])] [1]) = accepted := by
  decide +kernel

/-- The arm of an alternative whose payload has no value does not run: `fin 0`. -/
example : check [elements, .variant ⟨7⟩ (.cons .nat (.cons (.fin 0) .nil))] [F] false
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (element 0) [],
      .cases ⟨2⟩ () 1 [11]
        [.mk [20] [] [10],
         .mk [30] [.op ⟨3⟩ [31] (toNat 0) [30], .op ⟨4⟩ [32] (item elements) [0, 31]] [32]]]
      [11]) = accepted := by
  decide +kernel

/-- The same of a payload that has no value without being `fin 0`: two items of `fin 0`. -/
example : check [elements, .variant ⟨7⟩ (.cons .nat (.cons (.seq (.fin 0) (some 2)) .nil))]
    [F] false (.mk [0, 1] [
      .op ⟨1⟩ [10] (element 0) [],
      .cases ⟨2⟩ () 1 [11]
        [.mk [20] [] [10],
         .mk [30] [.op ⟨3⟩ [31] (natural 0) [], .op ⟨4⟩ [32] (item elements) [0, 31]] [32]]]
      [11]) = accepted := by
  decide +kernel

/-- A function with an input that has no value never runs. -/
example : check [elements, .fin 0] [F] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 0) [1],
    .op ⟨2⟩ [11] (item elements) [0, 10]] [11]) = accepted := by
  decide +kernel

/-! ## What a condition teaches -/

abbrev conjunction : LocalRaw field := .owned .boolAnd [] []
abbrev disjunction : LocalRaw field := .owned .boolOr [] []

/-- `guard (0 < length(xs)) and (1 < length(xs))`, the `and` applied as `bool.and`, then `xs[0]`
and `xs[1]`: a conjunction learned true gives the facts of both operands (TY9). -/
example : check [elements] [F] true (.mk [0] [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (length elements) [0],
    .op ⟨3⟩ [12] less [10, 11],
    .op ⟨4⟩ [13] (natural 1) [],
    .op ⟨5⟩ [14] less [13, 11],
    .op ⟨6⟩ [15] conjunction [12, 14],
    .guard ⟨7⟩ () 15 .reject,
    .op ⟨8⟩ [16] (item elements) [0, 10],
    .op ⟨9⟩ [17] (item elements) [0, 13],
    .op ⟨10⟩ [18] (fieldRow .add) [16, 17]] [18]) = accepted := by
  decide +kernel

/-- The same with run-time indices: `guard (i < length(xs)) and (j < length(xs))`. -/
example : check [elements, .nat, .nat] [F] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [11] (length elements) [0],
    .op ⟨2⟩ [12] less [1, 11],
    .op ⟨3⟩ [13] less [2, 11],
    .op ⟨4⟩ [14] conjunction [12, 13],
    .guard ⟨5⟩ () 14 .reject,
    .op ⟨6⟩ [15] (item elements) [0, 1],
    .op ⟨7⟩ [16] (item elements) [0, 2],
    .op ⟨8⟩ [17] (fieldRow .add) [15, 16]] [17]) = accepted := by
  decide +kernel

/-- `guard not ((length(xs) <= 0) or (length(xs) <= 1))`, the `or` applied as `bool.or`: a
disjunction learned false gives the negation of both operands (TY9). -/
example : check [elements] [F] true (.mk [0] [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] (length elements) [0],
    .op ⟨3⟩ [12] less [10, 11],
    .op ⟨4⟩ [13] negation [12],
    .op ⟨5⟩ [14] (natural 1) [],
    .op ⟨6⟩ [15] less [14, 11],
    .op ⟨7⟩ [16] negation [15],
    .op ⟨8⟩ [17] disjunction [13, 16],
    .op ⟨9⟩ [18] negation [17],
    .guard ⟨10⟩ () 18 .reject,
    .op ⟨11⟩ [19] (item elements) [0, 10],
    .op ⟨12⟩ [20] (item elements) [0, 14],
    .op ⟨13⟩ [21] (fieldRow .add) [19, 20]] [21]) = accepted := by
  decide +kernel

/-- The same with run-time indices: `guard not ((length(xs) <= i) or (length(xs) <= j))`. -/
example : check [elements, .nat, .nat] [F] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [11] (length elements) [0],
    .op ⟨2⟩ [12] less [1, 11],
    .op ⟨3⟩ [13] negation [12],
    .op ⟨4⟩ [14] less [2, 11],
    .op ⟨5⟩ [15] negation [14],
    .op ⟨6⟩ [16] disjunction [13, 15],
    .op ⟨7⟩ [17] negation [16],
    .guard ⟨8⟩ () 17 .reject,
    .op ⟨9⟩ [18] (item elements) [0, 1],
    .op ⟨10⟩ [19] (item elements) [0, 2],
    .op ⟨11⟩ [20] (fieldRow .add) [18, 19]] [20]) = accepted := by
  decide +kernel

/-- `t := a < b; f := 5; e := b == f`, then `c := e && t` (or `c := t && e`), `guard c` and
`xs[a]` on a sequence of five naturals. The operands of a conjunction learned true are learned
one after the other, in the order written: the conjunction does not commute for the table. -/
def learnedInOrder (equalityFirst : Bool) :=
  check [naturals 5, .nat, .nat] [.nat] true <| .mk [0, 1, 2] [
  .op ⟨1⟩ [10] less [1, 2],
  .op ⟨2⟩ [11] (natural 5) [],
  .op ⟨3⟩ [12] equal [2, 11],
  .op ⟨4⟩ [13] conjunction (if equalityFirst then [12, 10] else [10, 12]),
  .guard ⟨5⟩ () 13 .reject,
  .op ⟨6⟩ [14] (item (naturals 5)) [0, 1]] [14]

/-- `c := e && t`: accepted. `e` is learned first and gives `b` the number 5; then `t` gives `a`
the range below it, `0..4`, which the read needs. -/
example : learnedInOrder true = accepted := by decide +kernel

/-- `c := t && e`: refused at the read, with nothing known of `a`. `t` is learned first, while
nothing is known of `b`, so `a` gets no upper end; that `b` is 5, learned after, does not come
back to `a`. This is the order of learning, as for the source's `and`, whose second operand runs
only where the first is true. -/
example : learnedInOrder false = some (.inl
    [unjustified 6 (item (naturals 5)) (.below (.arg 1) 5) [anyNat]]) := by
  decide +kernel

/-- `z := 0; w := toNat i` for `i : fin 1`, `guard !(z == w)`, then `x / z` or `x / w`. Both
operands of the equality are known to be zero, so nothing after the guard runs. What an equality
learned false teaches does not depend on the order of its operands, which the table places by
their identifiers: each of the two is at least one. -/
def differentFromZero (byLiteral : Bool) :=
  check [.nat, .fin 1] [.nat] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (toNat 1) [1],
  .op ⟨3⟩ [12] equal [10, 11],
  .op ⟨4⟩ [13] negation [12],
  .guard ⟨5⟩ () 13 .reject,
  .op ⟨6⟩ [14] quotient [0, if byLiteral then 10 else 11]] [14]

example : differentFromZero true = accepted := by decide +kernel
example : differentFromZero false = accepted := by decide +kernel

/-- `guard a == b`, then `a - b` and `b - a`: an equality gives both orders (TY9). -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] equal [0, 1],
    .guard ⟨2⟩ () 10 .reject,
    .op ⟨3⟩ [11] minus [0, 1],
    .op ⟨4⟩ [12] minus [1, 0],
    .op ⟨5⟩ [13] plus [11, 12]] [13]) = accepted := by
  decide +kernel

/-- `guard 5 == x`, then `xs[x]` on `[F; 6]`: the number of the first side is the second's. -/
example : check [sizedElements 6, .nat] [F] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 5) [],
    .op ⟨2⟩ [11] equal [10, 1],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] (item (sizedElements 6)) [0, 1]] [12]) = accepted := by
  decide +kernel

/-- `guard 0 != n`, then `z / n`: zero on the first side makes the second at least one. -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 0) [],
    .op ⟨2⟩ [11] equal [10, 1],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .reject,
    .op ⟨5⟩ [13] quotient [0, 1]] [13]) = accepted := by
  decide +kernel

/-- `guard i < n`, then `n - i`: the strict order answers `i <= n` (TY4). -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] less [0, 1],
    .guard ⟨2⟩ () 10 .reject,
    .op ⟨3⟩ [11] minus [1, 0]] [11]) = accepted := by
  decide +kernel

/-- `(u + i) - i`: the value is the second operand of the sum (TY4). -/
example : check [.nat, .nat] [.nat] false (.mk [0, 1] [
    .op ⟨1⟩ [10] plus [0, 1],
    .op ⟨2⟩ [11] minus [10, 1]] [11]) = accepted := by
  decide +kernel

/-- `guard u <= x`, then `x - (x - u)`: a difference is at most what it is taken from (TY4). -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] less [0, 1],
    .op ⟨2⟩ [11] negation [10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] minus [0, 1],
    .op ⟨5⟩ [13] minus [0, 12]] [13]) = accepted := by
  decide +kernel

/-- `c = i < n or j < n`, as a choice whose first region returns `true`; `guard not c`, then
`i - n` and `j - n`: the negation of a disjunction (TY9). -/
example : check [.nat, .nat, .nat] [.nat] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] less [0, 2],
    .choose ⟨2⟩ () 10 [11]
      (.mk [] [.op ⟨3⟩ [20] (truth true) []] [20])
      (.mk [] [.op ⟨4⟩ [30] less [1, 2]] [30]),
    .op ⟨5⟩ [12] negation [11],
    .guard ⟨6⟩ () 12 .reject,
    .op ⟨7⟩ [13] minus [0, 2],
    .op ⟨8⟩ [14] minus [1, 2],
    .op ⟨9⟩ [15] plus [13, 14]] [15]) = accepted := by
  decide +kernel

/-! ## What regions give of a natural -/

/-- A variant of a natural or a truth value. -/
abbrev natOrTruth : field.Ty := .variant ⟨8⟩ (.cons .nat (.cons .bool .nil))
/-- A variant of a natural or a value of the payload type given. -/
abbrev natOr (payload : field.Ty) : field.Ty := .variant ⟨7⟩ (.cons .nat (.cons payload .nil))

/-- `z / (match v: a => 2, b => 3)`: a case analysis gives the hull of its arms, `2..3`. -/
example : check [.nat, natOrTruth] [.nat] false (.mk [0, 1] [
    .cases ⟨1⟩ () 1 [10]
      [.mk [20] [.op ⟨2⟩ [21] (natural 2) []] [21],
       .mk [30] [.op ⟨3⟩ [31] (natural 3) []] [31]],
    .op ⟨4⟩ [11] quotient [0, 10]] [11]) = accepted := by
  decide +kernel

/-- `z / (match v: a => 3, b => 0)` with `b` of no value: the arm that never runs says nothing,
and the divisor is `3`. -/
def deadArm (payload : field.Ty) := check [.nat, natOr payload] [.nat] false (.mk [0, 1] [
    .cases ⟨1⟩ () 1 [10]
      [.mk [20] [.op ⟨2⟩ [21] (natural 3) []] [21],
       .mk [30] [.op ⟨3⟩ [31] (natural 0) []] [31]],
    .op ⟨4⟩ [11] quotient [0, 10]] [11])

example : deadArm (.fin 0) = accepted := by decide +kernel

/-- `z / (if c then 2 else 3)`: the lower end of the hull is the smaller one. -/
example : check [.nat, .bool] [.nat] false (.mk [0, 1] [
    .choose ⟨1⟩ () 1 [10]
      (.mk [] [.op ⟨2⟩ [20] (natural 2) []] [20])
      (.mk [] [.op ⟨3⟩ [30] (natural 3) []] [30]),
    .op ⟨4⟩ [11] quotient [0, 10]] [11]) = accepted := by
  decide +kernel

/-- A block that gives `3`; `z / it`: what is known after a block is what its body gives. -/
example : check [.nat] [.nat] false (.mk [0] [
    .block ⟨1⟩ 0 [10] (.mk [] [.op ⟨2⟩ [20] (natural 3) []] [20]),
    .op ⟨3⟩ [11] quotient [0, 10]] [11]) = accepted := by
  decide +kernel

/-- `match v: a => a`, the payload an `index<4>`, converted to `nat` and back to `index<4>`:
the payload has its type's range. -/
example : check [.variant ⟨7⟩ (.cons (.fin 4) (.cons .nat .nil))] [.fin 4] false (.mk [0] [
    .cases ⟨1⟩ () 0 [10]
      [.mk [20] [.op ⟨2⟩ [21] (toNat 4) [20], .op ⟨3⟩ [22] (narrowTo 4) [21]] [22],
       .mk [30] [.op ⟨4⟩ [31] (natural 0) [], .op ⟨5⟩ [32] (narrowTo 4) [31]] [32]]] [10]) =
    accepted := by
  decide +kernel

/-- `acc = 5; for t in 0..n: acc := toNat(xs[t]) + acc` with `guard n < 10`, then `acc` as an
`index<2306>` and `z / acc`: the carried value is the second operand of the sum, the count's
upper end is the number of iterations, and the sum starts where `acc` starts (TY8, the row of
`∑`: `5 .. 5 + 9 · 255 = 2300`). -/
example : check [bytes 10, .nat, .nat] [.fin 2306, .nat] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [1, 10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] (natural 5) [],
    .loop ⟨5⟩ () (.count 1) [12] [13]
      (.mk [20, 21] [
        .op ⟨6⟩ [22] (item (bytes 10)) [0, 20],
        .op ⟨7⟩ [23] (toNat 256) [22],
        .op ⟨8⟩ [24] plus [23, 21]] [24]),
    .op ⟨9⟩ [14] quotient [2, 13],
    .op ⟨10⟩ [15] (narrowTo 2306) [13]] [15, 14]) = some (.inr [(place 5, 9)]) := by
  decide +kernel

/-- A loop as often as a count known to be `0`, carrying a natural that its body doubles (not a
sum): no iteration ends, so after the loop the carried value has its initial range, `5`, and is
a divisor and an `index<6>`. -/
example : check [.nat, .nat] [.fin 6, .nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 1) [],
    .op ⟨2⟩ [11] less [1, 10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] (natural 5) [],
    .loop ⟨5⟩ () (.count 1) [12] [13]
      (.mk [20, 21] [.op ⟨6⟩ [22] times [21, 21]] [22]),
    .op ⟨7⟩ [14] quotient [0, 13],
    .op ⟨8⟩ [15] (narrowTo 6) [13]] [15, 14]) = some (.inr [(place 5, 0)]) := by
  decide +kernel

/-! ## The ranges of arithmetic -/

/-- A conversion of `index<bound>` to `index<wider>`. -/
abbrev widen (bound wider : Nat) : LocalRaw field := .owned .finWiden [.fin bound, .fin wider] []

/-- `a` in `10..20` and `b` in `1..2` by guards; `z / (a / b)`: the quotient starts at
`10 / 2 = 5`. -/
example : check [.nat, .nat, .nat] [.nat] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [0, 10],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .reject,
    .op ⟨5⟩ [13] (natural 21) [],
    .op ⟨6⟩ [14] less [0, 13],
    .guard ⟨7⟩ () 14 .reject,
    .op ⟨8⟩ [15] (natural 1) [],
    .op ⟨9⟩ [16] less [1, 15],
    .op ⟨10⟩ [17] negation [16],
    .guard ⟨11⟩ () 17 .reject,
    .op ⟨12⟩ [18] (natural 3) [],
    .op ⟨13⟩ [19] less [1, 18],
    .guard ⟨14⟩ () 19 .reject,
    .op ⟨15⟩ [20] quotient [0, 1],
    .op ⟨16⟩ [21] quotient [2, 20]] [21]) = accepted := by
  decide +kernel

/-- `a: nat` and `b` in `1..4`: `a % b` is an `index<4>`, by the upper end of `b` alone. -/
example : check [.nat, .nat] [.fin 4] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 1) [],
    .op ⟨2⟩ [11] less [1, 10],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .reject,
    .op ⟨5⟩ [13] (natural 5) [],
    .op ⟨6⟩ [14] less [1, 13],
    .guard ⟨7⟩ () 14 .reject,
    .op ⟨8⟩ [15] remainder [0, 1],
    .op ⟨9⟩ [16] (narrowTo 4) [15]] [16]) = accepted := by
  decide +kernel

/-- `a: index<6>` and `b: nat` with `guard 1 <= b`: `a % b` is an `index<6>`, by the upper end of
`a` alone. -/
example : check [.fin 6, .nat] [.fin 6] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 1) [],
    .op ⟨2⟩ [11] less [1, 10],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .reject,
    .op ⟨5⟩ [13] (toNat 6) [0],
    .op ⟨6⟩ [14] remainder [13, 1],
    .op ⟨7⟩ [15] (narrowTo 6) [14]] [15]) = accepted := by
  decide +kernel

/-- `x: index<1>` and `y` in `1..3`: `x ^ y` is `0`, an `index<1>`, since the exponent is at
least one. -/
example : check [.fin 1, .fin 4] [.fin 1] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 4) [1],
    .op ⟨2⟩ [11] (natural 1) [],
    .op ⟨3⟩ [12] less [10, 11],
    .op ⟨4⟩ [13] negation [12],
    .guard ⟨5⟩ () 13 .reject,
    .op ⟨6⟩ [14] (toNat 1) [0],
    .op ⟨7⟩ [15] power [14, 10],
    .op ⟨8⟩ [16] (narrowTo 1) [15]] [16]) = accepted := by
  decide +kernel

/-- `x` in `2..5` by guards, as an `index<8>`, then `z / toNat(it)`: the result of `nat.below`
has its operand's range. -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 2) [],
    .op ⟨2⟩ [11] less [0, 10],
    .op ⟨3⟩ [12] negation [11],
    .guard ⟨4⟩ () 12 .reject,
    .op ⟨5⟩ [13] (natural 6) [],
    .op ⟨6⟩ [14] less [0, 13],
    .guard ⟨7⟩ () 14 .reject,
    .op ⟨8⟩ [15] (narrowTo 8) [0],
    .op ⟨9⟩ [16] (toNat 8) [15],
    .op ⟨10⟩ [17] quotient [1, 16]] [17]) = accepted := by
  decide +kernel

/-- An `index<4>` widened to `index<8>`, then narrowed back to `index<4>`: the widened value has
its operand's range. -/
example : check [.fin 4] [.fin 4] false (.mk [0] [
    .op ⟨1⟩ [10] (widen 4 8) [0],
    .op ⟨2⟩ [11] (toNat 8) [10],
    .op ⟨3⟩ [12] (narrowTo 4) [11]] [12]) = accepted := by
  decide +kernel

/-- `z / toNat(2)` with `2` a literal of `index<4>`: a literal of `fin` has its number. -/
example : check [.nat] [.nat] false (.mk [0] [
    .op ⟨1⟩ [10] (.literal (.fin 4) [2]) [],
    .op ⟨2⟩ [11] (toNat 4) [10],
    .op ⟨3⟩ [12] quotient [0, 11]] [12]) = accepted := by
  decide +kernel

/-! ## Code that does not run after an operation or a loop; places; the order of bounds -/

/-- Both regions of a choice convert `0` to `index<0>`, refused, and then give a natural: the
result of the conversion has no value, so the rest of each region never runs, nothing runs
after the choice, and the read there is not checked. -/
example : check [elements, .bool] [F] false (.mk [0, 1] [
    .choose ⟨1⟩ () 1 [10]
      (.mk [] [
        .op ⟨2⟩ [20] (natural 0) [],
        .op ⟨3⟩ [21] (narrowTo 0) [20],
        .op ⟨8⟩ [22] (natural 7) []] [22])
      (.mk [] [
        .op ⟨4⟩ [30] (natural 0) [],
        .op ⟨5⟩ [31] (narrowTo 0) [30],
        .op ⟨9⟩ [32] (natural 7) []] [32]),
    .op ⟨6⟩ [11] (natural 0) [],
    .op ⟨7⟩ [12] (item elements) [0, 11]] [12]) = some (.inl
    [unjustified 3 (narrowTo 0) (.below (.arg 0) 0) [some (Range.point 0)],
     unjustified 5 (narrowTo 0) (.below (.arg 0) 0) [some (Range.point 0)]]) := by
  decide +kernel

/-- A loop that collects the conversion of `0` to `index<0>`, refused: the collected values have
no value, so nothing runs after the loop, and the read there is not checked. -/
example : check [elements] [F] false (.mk [0] [
    .loop ⟨1⟩ () (.fixed 2) [] [10]
      (.mk [20] [.op ⟨2⟩ [21] (natural 0) [], .op ⟨3⟩ [22] (narrowTo 0) [21]] [22]),
    .op ⟨4⟩ [11] (natural 0) [],
    .op ⟨5⟩ [12] (item elements) [0, 11]] [12]) = some (.inl
    [unjustified 3 (narrowTo 0) (.below (.arg 0) 0) [some (Range.point 0)]]) := by
  decide +kernel

/-- An unguarded `xs[0]` inside a block: the place of the refusal has the block. -/
example : check [elements] [F] false (.mk [0] [
    .block ⟨1⟩ 0 [10] (.mk [] [
      .op ⟨2⟩ [20] (natural 0) [],
      .op ⟨3⟩ [21] (item elements) [0, 20]] [21])] [10]) = some (.inl
    [⟨.domain, ⟨⟨1⟩, [(⟨1⟩, 0)], some ⟨3⟩, none⟩,
      .unjustified (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]⟩]) := by
  decide +kernel

/-- A loop as often as a bounded count inside a block: the place of its bound has the block. -/
example : check [.nat] [.nat] true (.mk [0] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [0, 10],
    .guard ⟨3⟩ () 11 .reject,
    .block ⟨4⟩ 0 [] (.mk [] [.loop ⟨5⟩ () (.count 0) [] [] (.mk [20] [] [])] [])] [0]) =
    some (.inr [(⟨⟨1⟩, [(⟨4⟩, 0)], some ⟨5⟩, none⟩, 9)]) := by
  decide +kernel

/-- Two loops as often as bounded counts: their bounds in the order of the walk. -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [0, 10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] (natural 5) [],
    .op ⟨5⟩ [13] less [1, 12],
    .guard ⟨6⟩ () 13 .reject,
    .loop ⟨7⟩ () (.count 0) [] [] (.mk [20] [] []),
    .loop ⟨8⟩ () (.count 1) [] [] (.mk [30] [] [])] [0]) =
    some (.inr [(place 7, 9), (place 8, 4)]) := by
  decide +kernel

/-! ## Which types have no value -/

/-- A payload of a tuple with a component of no value makes its arm dead. -/
example : deadArm (.tuple (.cons .nat (.cons (.fin 0) .nil))) = accepted := by decide +kernel
/-- So does a record with a field of no value. -/
example : deadArm (.record ⟨9⟩ false (.cons (.fin 0) .nil)) = accepted := by decide +kernel
/-- So does a variant all of whose alternatives have no value. -/
example : deadArm (.variant ⟨9⟩ (.cons (.fin 0) (.cons (.fin 0) .nil))) = accepted := by
  decide +kernel
/-- So does a variant without alternatives. -/
example : deadArm (.variant ⟨9⟩ .nil) = accepted := by decide +kernel

end Zkc.Core.FactsTests
