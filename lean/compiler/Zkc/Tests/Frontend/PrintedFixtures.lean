import Zkc.Frontend.Emit.Reports

/-!
Programs by names that no example reaches: every constructor of a definition, of an instruction,
of the operations of a function and of a protocol, of a type, of a header summary and of an
annotation, every owned operation, every constructor of a key of the standard vocabulary and of
a parameter of a project primitive, and an association that is not empty. They are data for the
printer of the program by names; they need not be admitted.

The check of printed packages prints these values, has Lean read the text, and compares what
Lean read with the values here. `PrintedFixtureCoverage` checks that no constructor is left
out.
-/

namespace Zkc.Tests.Frontend.PrintedFixtures
open Zkc.Core Zkc.Frontend

/-- A project type and a project primitive that takes a natural and gives a value of it. The
static arguments of the primitive have every form of a parameter. -/
abbrev projectType : Zkc.Vocabulary.Project.Parameter := .type (.nominal "fixture.type") (.cons (.natural 3) .nil)

abbrev projectRow : Zkc.Vocabulary.Project.PrimitiveName :=
  ⟨"fixture.row", .cons (.natural 2) <| .cons (.moduleRef 5) <|
    .cons (.type (.seq (some 4)) (.cons (.type .bool .nil) .nil)) <|
    .cons (.type (.seq none) (.cons (.type .nat .nil) .nil)) <|
    .cons (.type .tuple (.cons (.type .rational .nil) (.cons (.type (.index 7) .nil) .nil))) <|
    .cons (.type .nonzero .nil) <| .cons (.type (.record 11) .nil) <|
    .cons (.type (.variant 12) .nil) <| .cons (.type (.specification 13) .nil) <|
    .cons (.type (.opaqueMember 14 "member") .nil) .nil⟩

/-- Every form of a type over the keys of the standard vocabulary and a project type, with every
kind of nominal type, every field and every group. -/
abbrev everyLinkedType : List Zkc.Vocabulary.Project.LinkedType :=
  [.bool, .nat, .fin 5, .seq (.nominal (.inl (.field .bls12381Fr))) (some 2),
    .seq (.nominal (.inr projectType)) none,
    .tuple (.cons .nat (.cons (.nominal (.inl (.field .koalaBear4))) .nil)),
    .record ⟨31⟩ true (.cons .bool .nil), .record ⟨33⟩ false .nil,
    .variant ⟨32⟩ (.cons .nat (.cons (.tuple .nil) .nil)),
    .nominal (.inl (.nonzero .koalaBear)), .nominal (.inl (.group .g1)),
    .nominal (.inl (.group .g2)), .nominal (.inl (.group .gt))]

abbrev bindings : Zkc.Vocabulary.Project.Bindings :=
  ⟨[(projectRow, ⟨everyLinkedType, [.nominal (.inr projectType)]⟩)], by decide⟩

/-- The rows that the project binds, as the printer of a vocabulary reads them. -/
def bindingRows : List (Zkc.Vocabulary.Project.PrimitiveName × Zkc.Vocabulary.Project.PrimitiveSignature) := bindings.rows

abbrev V : Vocabulary := bindings.vocabulary

abbrev field : V.Ty := .nominal (.inl (.field .bls12381Fr))
abbrev project : V.Ty := .nominal (.inr projectType)

/-- Every form of a type, as a type of the vocabulary. -/
abbrev everyType : List V.Ty := everyLinkedType

/-- Every owned operation. -/
def ownedNames : List OwnedName :=
  [.natAdd, .natSub, .natMul, .natDiv, .natRem, .natPow, .natEqual, .natLess,
    .boolAnd, .boolOr, .boolNot, .boolEqual,
    .seqLength, .seqAt, .seqSlice, .seqConcat, .seqFill, .seqSized, .natBelow,
    .seqUnsized, .finToNat, .finWiden, .make, .get, .take, .variant]

/-- Rows of the standard vocabulary with every constructor of a key of a row. -/
def standardRows : List Zkc.Vocabulary.RowKey :=
  ([.add, .sub, .mul, .neg, .inverse, .pow, .equal, .isNonzero, .nonzero, .fromNonzero, .fromNat,
      .toNat, .components, .fromComponents, .embed, .coefficients, .fromCoefficients, .root].map
    fun row => .field row .koalaBear .all) ++
  [.field .inverse .koalaBear4 .nonzero] ++
  ([.zero, .add, .sub, .neg, .scale, .equal, .generator].map fun row => .group row (.field .koalaBear)) ++
  [.group .add (.group .g1), .group .add (.group .g2), .group .add (.group .gt)] ++
  ([.add, .sub, .scale, .sum, .product, .inner, .equal].map
    fun row => .seq row (.atom (.field .koalaBear4)) (some 4)) ++
  [.seq .add (.sized (.atom (.group .g1)) 3) none,
    .hash .sha256, .hash .keccak256, .hash (.shake128 32), .hash (.shake256 64), .pair]

/-- One operation of a function for each owned operation and for each of the rows above. -/
def everyOperation : List (Instruction (LocalRaw V) Unit) :=
  (ownedNames.zipIdx.map fun (name, i) => .op ⟨100 + i⟩ [100 + i] (.owned name [] []) []) ++
  (standardRows.zipIdx.map fun (row, i) => .op ⟨200 + i⟩ [200 + i] (.row (.inl row)) [])

/-- A function with a kernel, a summary of every kind of clause, every kind of annotation at
every kind of site, and a body with every instruction and every operation of a function. -/
def function : Definition V :=
  .fn ⟨40⟩ everyType [.nat, project] true (some ⟨41⟩)
    ⟨[.positional (.le (.arg 0) (.arg 1)), .positional (.lt (.arg 1) (.arg 0)),
        .positional (.atLeast (.arg 0) 1), .positional (.below (.arg 0) 9),
        .positional (.exactly (.arg 1) 4), .positional (.difference (.arg 1) (.arg 0) 2),
        .positional (.holds (.arg 2)), .positional (.bounded (.arg 3))],
      [.assertion ⟨.apply (.owned .natLess [] []) (.cons (.arg 0) (.cons (.arg 1) .nil)) 0,
          some (.apply (.literal .nat [7]) .nil 0)⟩,
        .assertion ⟨.arg 2, none⟩]⟩
    (.mk [0, 1, 2, 3, 4, 5, 6, 7, 8, 9] ([
      .op ⟨0⟩ [10] (.row (.inl (.field .add .bls12381Fr .all))) [8, 8],
      .op ⟨1⟩ [11] (.row (.inr projectRow)) [1],
      .op ⟨2⟩ [12] (.owned .seqAt [.seq field (some 2)] []) [3, 1],
      .op ⟨3⟩ [13] (.owned .get [.tuple (.cons .nat (.cons field .nil))] [1]) [5],
      .op ⟨4⟩ [14] (.literal (.fin 5) [3]) [],
      .op ⟨5⟩ [15] (.call ⟨41⟩) [1],
      .guard ⟨6⟩ () 0 .reject,
      .guard ⟨7⟩ () 0 .abort,
      .guard ⟨8⟩ () 0 .exhausted,
      .guard ⟨9⟩ () 0 .refused,
      .choose ⟨10⟩ () 0 [16] (.mk [] [] [1]) (.mk [] [.op ⟨11⟩ [17] (.literal .nat [0]) []] [17]),
      .cases ⟨12⟩ () 7 [18] [.mk [19] [] [19], .mk [20] [] [1]],
      .loop ⟨13⟩ () (.fixed 3) [1] [21, 22] (.mk [23, 24] [] [24, 23]),
      .loop ⟨14⟩ () (.count 1) [] [] (.mk [25] [] []),
      .block ⟨15⟩ 2 [26] (.mk [] [.op ⟨16⟩ [27] (.literal .nat [1]) []] [27]),
      .attempt ⟨17⟩ () [28] (.mk [29] [] [29])] ++ everyOperation) [1, 11])
    [(.instruction ⟨.root, 0⟩ ⟨0⟩, .invariant [0, 1] [.arg 0, .apply (.call ⟨41⟩) (.cons (.arg 1) .nil) 0]),
      (.instruction ⟨.body .root 12 ⟨13⟩, 1⟩ ⟨5⟩, .step 2 [1, 10]),
      (.block ⟨.otherwise (.arm (.block .root 3 ⟨15⟩ 2) 4) 5 ⟨10⟩, 6⟩ ⟨15⟩ 2, .fact [0] (.arg 0))]

/-- A protocol with every operation of a protocol and every class of event, and an instruction
of each kind performed by roles. -/
def protocol : Definition V :=
  .protocol ⟨42⟩ 3 [⟨field, [0, 1]⟩, ⟨.nat, [2]⟩] [⟨project, [0]⟩]
    (.mk [0, 1] [
      .op ⟨0⟩ [2] (.compute [0, 1] (.row (.inl (.field .add .bls12381Fr .all)))) [0, 0],
      .op ⟨1⟩ [3] (.event (.flow .message 0 [1, 2]) field) [2],
      .op ⟨2⟩ [4] (.event (.flow .rows 1 [0]) (.seq field none)) [3],
      .op ⟨3⟩ [5] (.event (.flow .opening 2 []) .bool) [4],
      .op ⟨4⟩ [6] (.event (.given (.coin (.uniform (.nominal (.field .bls12381Fr)))) 1 [0]) field) [],
      .op ⟨5⟩ [7] (.event (.given (.coin (.uniform (.seq (.fin 8) (some 2)))) 2 []) (.seq (.fin 8) (some 2))) [],
      .op ⟨6⟩ [8] (.event (.given (.request ⟨43⟩) 0 [1]) project) [1],
      .op ⟨7⟩ [9] (.narrow [0]) [6],
      .op ⟨8⟩ [10, 11] (.apply ⟨44⟩ [2, 0]) [9, 1],
      .guard ⟨9⟩ [1, 2] 5 .reject,
      .choose ⟨10⟩ [0] 5 [] (.mk [] [] []) (.mk [] [] []),
      .cases ⟨11⟩ [2] 1 [12] [.mk [13] [] [13]],
      .loop ⟨12⟩ [0, 1] (.count 1) [0] [14] (.mk [15, 16] [] [16]),
      .block ⟨13⟩ 0 [] (.mk [] [] []),
      .attempt ⟨14⟩ [1] [17] (.mk [18] [] [18])] [8])

def definitions : List (Definition V) := [function, protocol]

/-- An association with an entry of every kind. -/
def association : Association :=
  ⟨[⟨⟨50⟩, [.nat 8, .key ⟨51⟩], ⟨40⟩⟩], [⟨⟨52⟩, [⟨53⟩], [⟨54⟩, ⟨55⟩], [⟨56⟩]⟩], [(⟨57⟩, ⟨58⟩)],
    [⟨59⟩], [⟨60⟩, ⟨61⟩]⟩

end Zkc.Tests.Frontend.PrintedFixtures
