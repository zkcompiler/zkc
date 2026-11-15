import Zkc.Core.Facts.Walk
import Zkc.Core.Facts.Local
import Zkc.Core.Program.ElaborateLocal

/-!
The check of facts on functions written by names, elaborated and walked by the kernel.

The conformance cases of the reference that a function can express are named by their
identifiers: each is accepted or refused as the case says, and a refusal is compared whole. Then,
for each operation with a domain and for a restricted row, an application that is accepted and
one that is refused; then what sharing and the scope of facts must do in sibling regions, in
loops, after a choice and when a name is bound again.
-/

namespace Zkc.Core.FactsTests

/-! ## A vocabulary with a field -/

/-- The rows of a field: equality, addition, multiplication, whether an element is not zero, the
inverse (restricted to elements that are not zero) and a restricted row whose domain row has
other inputs, so that nothing decides it. -/
inductive FieldRow where
  | equal | add | mul | isNonzero | inverse | lopsided
deriving DecidableEq

/-- A field element. -/
def fieldElement : Ty Unit := .nominal () []

/-- A vocabulary with one nominal type, a field, whose every natural is a literal. -/
def field : Vocabulary where
  TypeKey := Unit
  RowKey := FieldRow
  LawKey := Empty
  row r _ := some <| match r with
    | .equal => ⟨[fieldElement, fieldElement], [.bool], .pure⟩
    | .add => ⟨[fieldElement, fieldElement], [fieldElement], .pure⟩
    | .mul => ⟨[fieldElement, fieldElement], [fieldElement], .pure⟩
    | .isNonzero => ⟨[fieldElement], [.bool], .pure⟩
    | .inverse => ⟨[fieldElement], [fieldElement], .restricted .isNonzero⟩
    | .lopsided => ⟨[fieldElement], [fieldElement], .restricted .equal⟩
  law r _ := nomatch r
  type _ _ := true
  literal _ _ _ := true

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
abbrev fieldRow (r : FieldRow) : LocalRaw field := .row r []

/-! ## The verdict -/

/-- What the check of facts says of the body of a function against the headers before it: its
refusals, or the bounds of its loops; nothing when the body does not elaborate. -/
def verdict (fns : List (FnHeader field)) (hdr : FnHeader field)
    (body : Region (LocalRaw field) Unit) :
    Option (List (ProgramRefusal field) ⊕ List (Place × Nat)) :=
  match elabFn fns hdr body with
  | .ok ⟨fn, _⟩ =>
      match checkFacts (localFactRules field fns) hdr.key none fn with
      | .ok bounds => some (.inr bounds)
      | .error refusals => some (.inl refusals)
  | .error _ => none

/-- The verdict on a function with the key 1 and no callee. -/
def check (ins outs : List field.Ty) (canStop : Bool) (body : Region (LocalRaw field) Unit) :
    Option (List (ProgramRefusal field) ⊕ List (Place × Nat)) :=
  verdict [] ⟨⟨1⟩, ins, outs, canStop, none⟩ body

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
      .op ⟨8⟩ [20] (.owned .make [.tuple .nil] []) [],
      .op ⟨9⟩ [21] (.owned .variant [.variant ⟨7⟩ (.cons F (.cons (.tuple .nil) .nil))] [1])
        [20]] [21])] [13]

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
    (.mk [] [.op ⟨12⟩ [20] (natural 0) []] [20])] [15]

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
    (.mk [] [.op ⟨9⟩ [20] (truth false) []] [20])] [13]

/-- `a or b` is `if a then true else b`: `b` has the facts of the negation of `a`. -/
def «V-F4b» := check [elements] [.bool] false <| .mk [0] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] (natural 0) [],
  .op ⟨3⟩ [12] equal [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [.op ⟨5⟩ [20] (truth true) []] [20])
    (.mk [] [
      .op ⟨6⟩ [20] (natural 0) [],
      .op ⟨7⟩ [21] (item elements) [0, 20],
      .op ⟨8⟩ [22] (element 0) [],
      .op ⟨9⟩ [23] (fieldRow .equal) [21, 22]] [23])] [13]

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
    (.mk [] [.op ⟨9⟩ [20] (truth false) []] [20])] [14]

/-- The fact does not hold in the other region. -/
def «R-TY9b» := check [elements] [F] false <| .mk [0] [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨4⟩ () 12 [13]
    (.mk [] [.op ⟨5⟩ [20] (element 0) []] [20])
    (.mk [] [
      .op ⟨6⟩ [20] (natural 0) [],
      .op ⟨7⟩ [21] (item elements) [0, 20]] [21])] [13]

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
    (.mk [] [.op ⟨9⟩ [20] (truth false) []] [20]),
  .choose ⟨10⟩ () 14 [15]
    (.mk [] [] [10])
    (.mk [] [.op ⟨11⟩ [20] (item elements) [0, 1]] [20])] [15]

/-- The fact of a choice's region does not leave it. -/
def «V-F11» := check [elements, .nat] [F] false <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .choose ⟨3⟩ () 11 [12]
    (.mk [] [.op ⟨4⟩ [20] (natural 0) []] [20])
    (.mk [] [.op ⟨5⟩ [20] (natural 1) []] [20]),
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

/-- A sum of weighted bytes, unrolled as the frontend writes it, of `count` terms. -/
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
      (if k = 0 then [.op ⟨10 * k + 7⟩ [2000] (natural 0) [],
          .op ⟨10 * k + 8⟩ [2000] plus [2000, 15]]
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

/-- A fact on `i + 1`, then `i` updated. -/
def «V-F1» := check [elements, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] plus [1, 10],
  .op ⟨3⟩ [12] (length elements) [0],
  .op ⟨4⟩ [13] less [12, 11],
  .op ⟨5⟩ [14] negation [13],
  .guard ⟨6⟩ () 14 .refused,
  .op ⟨7⟩ [15] (natural 100) [],
  .op ⟨8⟩ [1] plus [1, 15],
  .op ⟨9⟩ [16] (item elements) [0, 1]] [16]

/-- A name narrowed by a guard, then updated. -/
def «V-F1b» := check [elements, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (length elements) [0],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .refused,
  .op ⟨4⟩ [12] (natural 100) [],
  .op ⟨5⟩ [1] plus [1, 12],
  .op ⟨6⟩ [13] (item elements) [0, 1]] [13]

/-- A name with a range from a guard, then updated. -/
def «V-F1c» := check [sizedElements 8, .nat] [F] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 8) [],
  .op ⟨2⟩ [11] less [1, 10],
  .guard ⟨3⟩ () 11 .refused,
  .op ⟨4⟩ [12] (natural 100) [],
  .op ⟨5⟩ [1] plus [1, 12],
  .op ⟨6⟩ [13] (item (sizedElements 8)) [0, 1]] [13]

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

/-- A fact on `i + 1` says nothing of `1 + i`. -/
def «facts-no-commutativity-recovery» := check [naturals 8, .nat] [.nat] true <| .mk [0, 1] [
  .op ⟨1⟩ [10] (natural 1) [],
  .op ⟨2⟩ [11] plus [1, 10],
  .op ⟨3⟩ [12] (natural 8) [],
  .op ⟨4⟩ [13] less [11, 12],
  .guard ⟨5⟩ () 13 .reject,
  .op ⟨6⟩ [14] (natural 1) [],
  .op ⟨7⟩ [15] plus [14, 1],
  .op ⟨8⟩ [16] (item (naturals 8)) [0, 15]] [16]

/-! ### The verdicts -/

example : «T-Z7» = accepted := by decide
example : «V-F16» = accepted := by decide
example : «R-TY9a-head» = accepted := by decide
example : «R-TY9a-last» = accepted := by decide
example : «R-TY4a» = accepted := by decide
example : «V-G2» = accepted := by decide
example : «N-TY8d» = accepted := by decide
example : «T-Z8» = accepted := by decide
example : «I-4» = accepted := by decide
example : «N-TY4b» = accepted := by decide
example : «N-TY4c» = accepted := by decide
example : «T-Z6» = some (.inl
    [unjustified 1 (item (sizedElements 8)) (.below (.arg 1) 8) [anyNat]]) := by decide
example : «I-4b» = some (.inl
    [unjustified 2 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide
example : «I-4c» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide
/-- One refusal, at the difference: the index is `length(xs) - u` with `1 <= u`. -/
example : «V-F15» = some (.inl
    [unjustified 3 minus (.le (.arg 1) (.arg 0)) [some (Range.point 1), anyNat]]) := by decide
example : «V-F6» = accepted := by decide
example : «N-TY8e» = accepted := by decide
example : «N-TY8f» = some (.inl
    [unjustified 4 (narrowTo 8) (.below (.arg 0) 8) [some ⟨1, some 8⟩]]) := by decide
/-- One refusal, at the difference; the index is then below 10 by its range. -/
example : «N-TY10c» = some (.inl
    [unjustified 4 minus (.le (.arg 1) (.arg 0)) [some ⟨0, some 3⟩, some ⟨0, some 9⟩]]) := by
  decide
example : «V-F4» = accepted := by decide
example : «V-F4b» = accepted := by decide
example : «V-F4c» = accepted := by decide
example : «N-TY9b» = accepted := by decide
example : «V-F8» = accepted := by decide
example : «N-TY9a» = some (.inl
    [unjustified 2 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide
/-- In the second region the length is at most zero. -/
example : «R-TY9b» = some (.inl
    [unjustified 7 (item elements) (.lt (.arg 1) lengthOf)
      [some (Range.point 0), some ⟨0, some 0⟩]]) := by
  decide
example : «V-F7» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide
example : «V-F10» = some (.inl
    [unjustified 11 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide
example : «V-F11» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide
example : «I-4f» = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide
example : «I-4e-total» = accepted := by decide
example : «I-4e-tail» = accepted := by decide
example : «N-TY10e» = accepted := by decide
example : «N-TY10g» = accepted := by decide
example : «N-TY8g» = accepted := by decide +kernel
example : «N-TY8h» = some (.inl
    [unjustified 1000 (narrowTo (2 ^ 64)) (.below (.arg 0) (2 ^ 64))
      [some ⟨0, some (2 ^ 72 - 1)⟩]]) := by
  decide +kernel
example : «V-F1d» = accepted := by decide
example : «V-F1» = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf)
      [some ⟨100, none⟩, some ⟨1, none⟩]]) := by
  decide
example : «V-F1b» = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf)
      [some ⟨100, none⟩, some ⟨1, none⟩]]) := by
  decide
example : «V-F1c» = some (.inl
    [unjustified 6 (item (sizedElements 8)) (.below (.arg 1) 8) [some ⟨100, some 107⟩]]) := by
  decide
example : «facts-direct-order» = accepted := by decide
example : «facts-no-transitivity» = some (.inl
    [unjustified 7 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by decide
example : «facts-no-commutativity-recovery» = some (.inl
    [unjustified 8 (item (naturals 8)) (.below (.arg 1) 8) [some ⟨1, none⟩]]) := by decide

/-- A restricted operation is shared, and checked again where it is applied again: justified in
one region and applied in the other, it is refused there. -/
example : check [.nat, .nat, .bool] [.nat] true (.mk [0, 1, 2] [
    .choose ⟨1⟩ () 2 [10]
      (.mk [] [
        .op ⟨2⟩ [20] less [0, 1],
        .op ⟨3⟩ [21] negation [20],
        .guard ⟨4⟩ () 21 .reject,
        .op ⟨5⟩ [22] minus [0, 1]] [22])
      (.mk [] [.op ⟨6⟩ [20] minus [0, 1]] [20])] [10]) =
    some (.inl [unjustified 6 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by
  decide

/-- A call is shared: a fact about its result holds of the same call again. -/
example : verdict [⟨⟨1⟩, [.nat], [.nat], false, none⟩] ⟨⟨2⟩, [elements, .nat], [F], true, none⟩
    (.mk [0, 1] [
      .op ⟨1⟩ [10] (.call ⟨1⟩) [1],
      .op ⟨2⟩ [11] (length elements) [0],
      .op ⟨3⟩ [12] less [10, 11],
      .guard ⟨4⟩ () 12 .reject,
      .op ⟨5⟩ [13] (.call ⟨1⟩) [1],
      .op ⟨6⟩ [14] (item elements) [0, 13]] [14]) = accepted := by
  decide

/-! ## Each operation with a domain, and a restricted row -/

/-- The difference, after a guard that the second is at most the first. -/
example : check [.nat, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] less [0, 1],
    .op ⟨2⟩ [11] negation [10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] minus [0, 1]] [12]) = accepted := by
  decide

example : check [.nat, .nat] [.nat] false (.mk [0, 1] [.op ⟨1⟩ [10] minus [0, 1]] [10]) =
    some (.inl [unjustified 1 minus (.le (.arg 1) (.arg 0)) [anyNat, anyNat]]) := by
  decide

/-- The quotient by a sum with one. -/
example : check [.nat, .nat] [.nat] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (natural 1) [],
    .op ⟨2⟩ [11] plus [1, 10],
    .op ⟨3⟩ [12] quotient [0, 11]] [12]) = accepted := by
  decide

example : check [.nat, .nat] [.nat] false (.mk [0, 1] [.op ⟨1⟩ [10] quotient [0, 1]] [10]) =
    some (.inl [unjustified 1 quotient (.atLeast (.arg 1) 1) [anyNat]]) := by
  decide

/-- The remainder by a written number. -/
example : check [.nat] [.nat] false (.mk [0] [
    .op ⟨1⟩ [10] (natural 7) [],
    .op ⟨2⟩ [11] remainder [0, 10]] [11]) = accepted := by
  decide

example : check [.nat, .fin 3] [.nat] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 3) [1],
    .op ⟨2⟩ [11] remainder [0, 10]] [11]) =
    some (.inl [unjustified 2 remainder (.atLeast (.arg 1) 1) [some ⟨0, some 2⟩]]) := by
  decide

/-- An item of a sized sequence at an index of its size. -/
example : check [sizedElements 8, .fin 8] [F] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 8) [1],
    .op ⟨2⟩ [11] (item (sizedElements 8)) [0, 10]] [11]) = accepted := by
  decide

example : check [sizedElements 8, .fin 9] [F] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 9) [1],
    .op ⟨2⟩ [11] (item (sizedElements 8)) [0, 10]] [11]) =
    some (.inl [unjustified 2 (item (sizedElements 8)) (.below (.arg 1) 8)
      [some ⟨0, some 8⟩]]) := by
  decide

/-- A slice with nothing known of its bounds: both orders refused. -/
example : check [elements, .nat, .nat] [elements] false (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (slice elements elements) [0, 1, 2]] [10]) =
    some (.inl [unjustified 1 (slice elements elements) (.le (.arg 1) (.arg 2)) [anyNat, anyNat],
      unjustified 1 (slice elements elements) (.le (.arg 2) lengthOf) [anyNat, anyNat]]) := by
  decide

/-- A slice of a sized result whose bounds differ by another number. -/
example : check [sizedElements 16, .fin 8] [sizedElements 4] false (.mk [0, 1] [
    .op ⟨1⟩ [10] (toNat 8) [1],
    .op ⟨2⟩ [11] (natural 3) [],
    .op ⟨3⟩ [12] plus [10, 11],
    .op ⟨4⟩ [13] (slice (sizedElements 16) (sizedElements 4)) [0, 10, 12]] [13]) =
    some (.inl [unjustified 4 (slice (sizedElements 16) (sizedElements 4))
      (.difference (.arg 2) (.arg 1) 4) [some ⟨3, some 10⟩, some ⟨0, some 7⟩]]) := by
  decide

/-- A sequence given a size with nothing known of its length. -/
example : check [elements] [sizedElements 8] false (.mk [0] [
    .op ⟨1⟩ [10] (sizedAs 8) [0]] [10]) =
    some (.inl [unjustified 1 (sizedAs 8) (.exactly lengthOf 8) [anyNat]]) := by
  decide

/-- The inverse of an element known not to be zero is `N-TY4c`; without the guard it is
refused, and so is a restricted row whose domain row takes other inputs, guarded or not. -/
example : check [F] [F] false (.mk [0] [.op ⟨1⟩ [10] (fieldRow .inverse) [0]] [10]) =
    some (.inl [unjustified 1 (fieldRow .inverse)
      (.holds (.apply (fieldRow .isNonzero) [0])) [none]]) := by
  decide

example : check [F] [F] true (.mk [0] [
    .op ⟨1⟩ [10] (fieldRow .isNonzero) [0],
    .guard ⟨2⟩ () 10 .refused,
    .op ⟨3⟩ [11] (fieldRow .lopsided) [0]] [11]) =
    some (.inl [unjustified 3 (fieldRow .lopsided) (.holds (.arg 1)) [none]]) := by
  decide

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
      .op ⟨6⟩ [20] (length elements) [0],
      .op ⟨7⟩ [21] less [secondIndex, 20],
      .guard ⟨8⟩ () 21 .reject] else []) ++
      [.op ⟨9⟩ [22] (item elements) [0, secondIndex]]) [22])] [10]

example : siblings 3 true = accepted := by decide
/-- The second region indexes by another value with no guard. -/
example : siblings 3 false = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide
/-- The second region indexes by the first region's index with no guard. -/
example : siblings 2 false = some (.inl
    [unjustified 9 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by decide

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
  decide

/-- The guard before the loop justifies the index in its body. -/
example : check [elements, .nat] [.nat] true (.mk [0, 1] [
    .op ⟨1⟩ [10] (length elements) [0],
    .op ⟨2⟩ [11] less [1, 10],
    .guard ⟨3⟩ () 11 .reject,
    .loop ⟨4⟩ () (.fixed 2) [] []
      (.mk [20] [.op ⟨5⟩ [21] (item elements) [0, 1]] [])] [1]) = accepted := by
  decide

/-- A loop as often as a length indexes by its index; the count has no upper bound, and a
function's loop is not refused for that. -/
example : check [elements] [.nat] false (.mk [0] [
    .op ⟨1⟩ [10] (length elements) [0],
    .loop ⟨2⟩ () (.count 10) [] []
      (.mk [20] [.op ⟨3⟩ [21] (item elements) [0, 20]] [])] [10]) = accepted := by
  decide

/-- A loop as often as a natural known below 10 has the bound 9. -/
example : check [.nat] [.nat] true (.mk [0] [
    .op ⟨1⟩ [10] (natural 10) [],
    .op ⟨2⟩ [11] less [0, 10],
    .guard ⟨3⟩ () 11 .reject,
    .loop ⟨4⟩ () (.count 0) [] [] (.mk [20] [] [])] [0]) = some (.inr [(place 4, 9)]) := by
  decide

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
    [unjustified 5 (item elements) (.lt (.arg 1) lengthOf) [anyNat, some ⟨1, none⟩]]) := by
  decide
example : carried true false = accepted := by decide
example : carried false true = some (.inl
    [unjustified 6 (item elements) (.lt (.arg 1) lengthOf) [anyNat, some ⟨1, none⟩]]) := by
  decide

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
    (.mk [] [.op ⟨8⟩ [20] (truth false) []] [20])] else [
  .op ⟨1⟩ [10] (natural 0) [],
  .op ⟨2⟩ [11] (length elements) [0],
  .op ⟨3⟩ [12] less [10, 11],
  .choose ⟨5⟩ () 12 [14]
    (.mk [] [
      .op ⟨6⟩ [20] (item elements) [0, 10],
      .op ⟨7⟩ [21] (element 0) [],
      .op ⟨4⟩ [22] (fieldRow .equal) [20, 21]] [22])
    (.mk [] [.op ⟨8⟩ [20] (truth false) []] [20])]) ++
  (if guarded then [.guard ⟨9⟩ () 14 .reject] else []) ++
  [.op ⟨10⟩ [15] (natural 0) [],
   .op ⟨11⟩ [16] (item elements) [0, 15]]) [16]

example : shortCircuit true false = accepted := by decide
example : shortCircuit false false = some (.inl
    [unjustified 11 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide
example : shortCircuit true true = some (.inl
    [unjustified 2 (item elements) (.lt (.arg 1) lengthOf) [some (Range.point 0), anyNat]]) := by
  decide

/-- A fact about one sequence does not justify indexing another of the same type. -/
example : check [elements, elements, .nat] [F] true (.mk [0, 1, 2] [
    .op ⟨1⟩ [10] (length elements) [0],
    .op ⟨2⟩ [11] less [2, 10],
    .guard ⟨3⟩ () 11 .reject,
    .op ⟨4⟩ [12] (item elements) [1, 2]] [12]) =
    some (.inl [unjustified 4 (item elements) (.lt (.arg 1) lengthOf) [anyNat, anyNat]]) := by
  decide

/-- `x := i + 1; guard x < length(xs)`, then `x` bound again to `x + 1`, to `i + 1` and to
`1 + i`, and `xs[x]`. -/
def rebound (again : List (Instruction (LocalRaw field) Unit)) :=
  check [elements, .nat] [F] true <| .mk [0, 1] ([
  .op ⟨1⟩ [11] (natural 1) [],
  .op ⟨2⟩ [10] plus [1, 11],
  .op ⟨3⟩ [12] (length elements) [0],
  .op ⟨4⟩ [13] less [10, 12],
  .guard ⟨5⟩ () 13 .reject,
  .op ⟨6⟩ [14] (natural 1) []] ++ again ++ [
  .op ⟨8⟩ [15] (item elements) [0, 10]]) [15]

example : rebound [.op ⟨7⟩ [10] plus [10, 14]] = some (.inl
    [unjustified 8 (item elements) (.lt (.arg 1) lengthOf) [some ⟨2, none⟩, some ⟨2, none⟩]]) := by
  decide
example : rebound [.op ⟨7⟩ [10] plus [1, 14]] = accepted := by decide
example : rebound [.op ⟨7⟩ [10] plus [14, 1]] = some (.inl
    [unjustified 8 (item elements) (.lt (.arg 1) lengthOf) [some ⟨1, none⟩, some ⟨2, none⟩]]) := by
  decide

end Zkc.Core.FactsTests
