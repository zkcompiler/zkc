import Zkc.Tests.Core.Check
import Zkc.Core.Package
import Zkc.Core.VocabularyModel
import Zkc.Core.Execute

/-! Checks of the vocabulary and of its model.

- The kernel: the type of rows at static arguments, among them a restricted row with its
  domain row, a row of the units of a field, a function member of a sort whose type reads a
  member of the type, a collection row, and a row at static arguments of another sort, which
  the table does not have. Every row of the table has a type at the representatives of the
  sorts it takes, and every domain row is a pure row of the table with the inputs of its
  restricted row and one `bool`.
- Lean's interpreter: the arithmetic of the model. In `koala-bear`, `bls12-381.fr` and
  `koala-bear.ext4` a product with an inverse is 1; the root of order `2^k` of `koala-bear` has
  that order; in `bls12-381.g1` the order times the generator and the sum of a point and its
  negation are the point at infinity; the collection rows are the folds of the element rows.
- The domain law of `field.nonzero`: on the values tried, it has a value exactly where
  `field.is_nonzero` gives `true`.
- The laws: `law.uniform` has a type at a tuple, a collection and an empty collection of a type
  that is not a law, and none at `index<0>`, an unsized collection or a tuple with a `nat`; its
  model samples a tuple and a collection component by component, each a value of its type.
- A run: a function that guards `field.is_nonzero` and then inverts its unit returns the
  inverse, and stops `reject` at 0; a package that applies `field.root` to `bls12-381.fr`, whose
  generator the catalogue does not give, does not run, with a message that names the row.
- The suite `suite.merlin3.bls12-381.fr64be/0` and the layout `zkc::layout::canonical`: the
  kernel computes the types of their rows; in Lean's interpreter, Keccak-f[1600] gives SHA3-256
  of the empty message and Merlin its published conformance vector; the layout writes a scalar
  least significant first and a natural in groups of seven bits; the layout reads what it writes
  and refuses what it does not write; a value is absorbed as the bytes that the layout writes
  for it. The checks of the formats, of the widths, of the encoding of G1 and of the limit are
  in `Zkc.Tests.Core.CanonicalLayout`.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Vocabulary Zkc.Core.Concrete

namespace VocabularyChecks

def koalaBear : Closed := .row "koala-bear"
def ext4 : Closed := .row "koala-bear.ext4"
def scalar : Closed := .row "bls12-381.fr"
def g1 : Closed := .row "bls12-381.g1"

/-! ## Types of rows -/

kernel_refl add : table.signature? "field.add" [.type koalaBear] equals
  some { kind := .pure, inputs := [koalaBear, koalaBear], outputs := [koalaBear] }
kernel_refl nonzero : table.signature? "field.nonzero" [.type koalaBear] equals
  some { kind := .restricted (some "field.is_nonzero"), inputs := [koalaBear],
         outputs := [.nonzero koalaBear] }
kernel_refl units : table.signature? "field.mul" [.type (.nonzero scalar)] equals
  some { kind := .pure, inputs := [.nonzero scalar, .nonzero scalar], outputs := [.nonzero scalar] }
kernel_refl to_nat : table.signature? "field.to_nat" [.type koalaBear] equals
  some { kind := .pure, inputs := [koalaBear], outputs := [.index 2130706433] }
kernel_refl coefficients : table.signature? "field.coefficients" [.type ext4] equals
  some { kind := .pure, inputs := [ext4], outputs := [.seq koalaBear (some 4)] }
kernel_refl root : table.signature? "field.root" [.type koalaBear] equals
  some { kind := .pure, inputs := [.index 25], outputs := [.nonzero koalaBear] }
kernel_refl inner : table.signature? "seq.inner" [.type g1, .natural 3] equals
  some { kind := .pure, inputs := [.seq g1 (some 3), .seq scalar (some 3)], outputs := [g1] }
kernel_refl not_a_field : table.signature? "field.add" [.type g1] equals none

/-! ## Laws -/

kernel_refl law_tuple : table.signature? "law.uniform" [.type (.tuple [.bool, .index 3, g1])] equals
  some { kind := .sampling, inputs := [], outputs := [.tuple [.bool, .index 3, g1]] }
kernel_refl law_collection : table.signature? "law.uniform" [.type (.seq (.nonzero koalaBear) (some 4))] equals
  some { kind := .sampling, inputs := [], outputs := [.seq (.nonzero koalaBear) (some 4)] }
kernel_refl law_empty_collection : table.signature? "law.uniform" [.type (.seq (.index 0) (some 0))] equals
  some { kind := .sampling, inputs := [], outputs := [.seq (.index 0) (some 0)] }
kernel_refl law_no_value : table.signature? "law.uniform" [.type (.index 0)] equals none
kernel_refl law_unsized : table.signature? "law.uniform" [.type (.seq .bool none)] equals none
kernel_refl law_nat_inside : table.signature? "law.uniform" [.type (.tuple [.bool, .nat])] equals none

/-- The static arguments of a row at the representatives of the sorts it takes. -/
def representativeArguments (entry : RowEntry) : Option (List Value) :=
  entry.parameters.mapM fun
    | .type none => some (.type koalaBear)
    | .type (some sort) => (table.representative? sort).map fun row => .type (.row row)
    | .units sort => (table.representative? sort).map fun row => .type (.nonzero (.row row))
    | .natural => some (.natural 3)
    | .law => some (.type (.tuple [.bool, koalaBear]))

kernel_refl every_row_typed :
    table.rows.all (fun entry =>
      match representativeArguments entry with
      | some arguments => (table.signature? entry.name arguments).isSome
      | none => false) equals true

kernel_refl domain_rows :
    table.rows.all (fun entry =>
      match entry.kind, representativeArguments entry with
      | .restricted (some domain), some arguments =>
        match table.signature? entry.name arguments, table.signature? domain arguments with
        | some restricted, some decides =>
          decides.kind == .pure && decides.inputs == restricted.inputs && decides.outputs == [.bool]
        | _, _ => false
      | _, _ => true) equals true

/-! ## Arithmetic -/

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"vocabulary model: {label}")

def applied (name : String) (arguments : List Value) (inputs : List Datum) : Option (List Datum) :=
  match applyRow table name arguments inputs with
  | .ok results => some results
  | .error _ => none

#eval show IO Unit from do
  let p := koalaBearOrder
  -- a product with an inverse is 1
  for (type, values) in [(koalaBear, [Datum.number 2, .number 7, .number (p - 1)]),
      (scalar, [Datum.number 3, .number (bls12381Order - 5)]),
      (ext4, [Datum.sequence [.number 1, .number 2, .number 3, .number 4],
        Datum.sequence [.number 0, .number 0, .number 0, .number 9]])] do
    for value in values do
      let some [inverse] := applied "field.inverse" [.type type] [value] | check "inverse" false
      let some [product] := applied "field.mul" [.type type] [value, inverse] | check "product" false
      let some [one] := applied "field.from_nat" [.type type] [.number 1] | check "one" false
      check s!"{reprStr type}: {reprStr value} times its inverse" (product == one)
  -- the root of order 2^k has that order
  for k in [1:25] do
    let some [root] := applied "field.root" [.type koalaBear] [.number k] | check "root" false
    let order (exponent : Nat) := Vocabulary.powerModulo root.toNat exponent p
    check s!"the root of order 2^{k}" (order (2 ^ k) == 1 && order (2 ^ (k - 1)) != 1)
  -- the group of BLS12-381
  let some [generator] := applied "group.generator" [.type g1] [] | check "generator" false
  let some [multiple] := applied "group.scale" [.type g1] [generator, .number bls12381Order]
    | check "scale" false
  let some [zero] := applied "group.zero" [.type g1] [] | check "zero" false
  check "the order times the generator" (multiple == zero)
  -- a law makes a tuple and a collection component by component, each a value of its type
  let coins (k : Nat) : Nat := 1000003 * k + bls12381Order - 1
  let law : Closed := .tuple [.bool, .index 3, .seq (.nonzero koalaBear) (some 2), ext4]
  match Vocabulary.lawValue table bls12381Order coins law 0 with
  | .ok (value, used) =>
    check "a sampled tuple" (used == 1 + 1 + 2 + 4)
    match value with
    | .sequence [flag, small, .sequence [first, second], .sequence coefficients] =>
      check "a sampled bool" (flag.toNat < 2)
      check "a sampled index" (small.toNat < 3)
      check "sampled units" (first.toNat != 0 && first.toNat < p && second.toNat != 0 && second.toNat < p)
      check "a sampled extension" (coefficients.length == 4 && coefficients.all (·.toNat < p))
    | _ => check "the shape of a sampled tuple" false
  | .error reason => check s!"a sampled tuple: {reason}" false
  check "an empty collection of no law"
    ((Vocabulary.lawValue table bls12381Order coins (.seq (.index 0) (some 0)) 0).toOption.map (·.1) ==
      some (.sequence []))
  -- a unit of an extension is its coefficients, and the element one when every number is zero
  check "a unit of an extension"
    ((Vocabulary.lawValue table bls12381Order coins (.nonzero ext4) 0).toOption.map
        (fun (value, used) => (value.items.length, used)) == some (4, 4))
  check "the unit of an extension from zeros"
    ((Vocabulary.lawValue table bls12381Order (fun _ => 0) (.nonzero ext4) 0).toOption.map (·.1) ==
      some (.sequence [.number 1, .number 0, .number 0, .number 0]))
  -- what has no law says so
  for none in [Closed.nat, .index 0, .seq koalaBear none, .tuple [koalaBear, .nat],
      .row "bls12-381.g2", .nonzero g1] do
    check s!"no law of {reprStr none}"
      (match Vocabulary.lawValue table bls12381Order coins none 0 with | .error _ => true | .ok _ => false)
  -- for every type of the vocabulary with a law, and the units of it, the value made of the
  -- numbers of the first seeds is a value of the type
  for entry in table.types do
    let some element := elementOf table (.row entry.row) | continue
    for seed in [0:4] do
      let numbers := Execute.coinNumbers [seed] ⟨[], 0, 0⟩ 0
      match Vocabulary.lawValue table bls12381Order numbers (.row entry.row) 0 with
      | .ok (value, _) => check s!"a value of the law of {entry.row}, seed {seed}" (element.valid value)
      | .error reason => check s!"the law of {entry.row}: {reason}" false
      if element == .curve then continue
      match Vocabulary.lawValue table bls12381Order numbers (.nonzero (.row entry.row)) 0 with
      | .ok (value, _) =>
        check s!"a unit of the law of {entry.row}, seed {seed}" (element.valid value && !element.isZero value)
      | .error reason => check s!"the law of the units of {entry.row}: {reason}" false
  let some [negation] := applied "group.neg" [.type g1] [generator] | check "neg" false
  let some [sum] := applied "group.add" [.type g1] [generator, negation] | check "add" false
  check "a point plus its negation" (sum == zero)
  -- collection rows are folds
  let xs := Datum.sequence [.number 2, .number 3, .number 4]
  check "seq.sum" (applied "seq.sum" [.type koalaBear, .natural 3] [xs] == some [.number 9])
  check "seq.product" (applied "seq.product" [.type koalaBear, .natural 3] [xs] == some [.number 24])
  check "seq.inner" (applied "seq.inner" [.type koalaBear, .natural 3] [xs, xs] == some [.number 29])
  check "seq.scale"
    (applied "seq.scale" [.type koalaBear, .natural 3] [xs, .number 2] ==
      some [.sequence [.number 4, .number 6, .number 8]])
  check "field.to_nat of koala-bear" (applied "field.to_nat" [.type koalaBear] [.number 5] == some [.number 5])
  check "field.coefficients of the extension"
    (applied "field.embed" [.type ext4] [.number 5] ==
      some [.sequence [.number 5, .number 0, .number 0, .number 0]])

/-! ## The domain law of `field.nonzero` -/

#eval show IO Unit from do
  let p := koalaBearOrder
  let tried : List (Closed × List Datum) := [
    (koalaBear, [.number 0, .number 1, .number 2, .number (p - 1)]),
    (scalar, [.number 0, .number 1, .number (bls12381Order - 1)]),
    (ext4, [.sequence [.number 0, .number 0, .number 0, .number 0],
      .sequence [.number 1, .number 0, .number 0, .number 0],
      .sequence [.number 0, .number 0, .number 7, .number 0]])]
  for (type, values) in tried do
    for value in values do
      let decides := applied "field.is_nonzero" [.type type] [value] == some [Datum.ofBool true]
      let defined := (applied "field.nonzero" [.type type] [value]).isSome
      check s!"the domain of field.nonzero at {reprStr type} on {reprStr value}" (decides == defined)

/-! ## A run -/

/-- A function of `koala-bear` to its units: `guard is_nonzero(x); return inverse(nonzero(x))`. -/
def invertText : String := "[\"zkc.core/0\", [[\"original\",
  [[\"koala-bear\", []], [\"nonzero\", [[\"type\", [\"nominal\", 0]]]]], [], [], [],
  [[\"field.is_nonzero\", [[\"type\", [\"nominal\", 0]]], \"pure\", [[\"nominal\", 0]], [\"bool\"]],
   [\"field.nonzero\", [[\"type\", [\"nominal\", 0]]], [\"restricted\", 0], [[\"nominal\", 0]], [[\"nominal\", 1]]],
   [\"field.inverse\", [[\"type\", [\"nominal\", 0]]], \"pure\", [[\"nominal\", 1]], [[\"nominal\", 1]]]],
  [[\"function\", 0, [[\"nominal\", 0]], [[\"nominal\", 1]],
    [[[\"op\", 0, [0]], [\"guard\", \"reject\", 1], [\"op\", 1, [0]], [\"op\", 2, [2]]], [3]]]]]],
  [], [], [], []]"

/-- A function that applies `field.root` to `bls12-381.fr`. -/
def rootText : String := "[\"zkc.core/0\", [[\"original\",
  [[\"bls12-381.fr\", []], [\"nonzero\", [[\"type\", [\"nominal\", 0]]]]], [], [], [],
  [[\"field.root\", [[\"type\", [\"nominal\", 0]]], \"pure\", [[\"fin\", 33]], [[\"nominal\", 1]]]],
  [[\"function\", 0, [[\"fin\", 33]], [[\"nominal\", 1]], [[[\"op\", 0, [0]]], [1]]]]]],
  [], [], [], []]"

def describe : Run → String
  | .returned outputs => s!"returned {reprStr outputs}"
  | .stopped reason => s!"stopped {reprStr reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

#eval show IO Unit from do
  let invert ← IO.ofExcept (Raw.parsePackage invertText)
  let inverse := (koalaBearOrder + 1) / 2
  let returned := describe (runData table invert 0 [.number 2])
  check s!"the inverse of 2: {returned}" (returned == describe (.returned [.number inverse]))
  let stopped := describe (runData table invert 0 [.number 0])
  check s!"the inverse of 0: {stopped}" (stopped == describe (.stopped .reject))
  let root ← IO.ofExcept (Raw.parsePackage rootText)
  match runData table root 0 [.number 3] with
  | .failed message =>
    check s!"the missing row is named: {message}" ((message.splitOn "field.root").length > 1)
  | other => check s!"a missing row runs: {describe other}" false

/-! ## The Merlin suite and the canonical layout -/

def stateType : Closed := .row "suite.merlin3.bls12-381.fr64be/0.state"
def labelType : Closed := .row "suite.merlin3.bls12-381.fr64be/0.label"
def bytesType : Closed := .seq (.index 256) none

kernel_refl suite_start : table.signature? "suite.merlin3.bls12-381.fr64be/0.start" [] equals
  some { kind := .pure, inputs := [labelType], outputs := [stateType] }
kernel_refl suite_absorb : table.signature? "suite.merlin3.bls12-381.fr64be/0.absorb" [.type g1] equals
  some { kind := .pure, inputs := [stateType, labelType, g1], outputs := [stateType] }
kernel_refl suite_derive : table.signature? "suite.merlin3.bls12-381.fr64be/0.derive" [.type scalar] equals
  some { kind := .pure, inputs := [stateType, labelType], outputs := [scalar, stateType] }
kernel_refl layout_take : table.signature? "layout.canonical.take" [.type scalar] equals
  some { kind := .pure, inputs := [bytesType], outputs := [.bool, scalar, bytesType] }
kernel_refl layout_close : table.signature? "layout.canonical.close" [] equals
  some { kind := .pure, inputs := [bytesType], outputs := [bytesType] }

#eval show IO Unit from do
  -- Keccak-f[1600] through SHA3-256 of the empty message: rate 136, padding 0x06 … 0x80
  let empty := ByteArray.mk ((Array.range 200).map fun index =>
    if index == 0 then 0x06 else if index == 135 then 0x80 else 0)
  check "SHA3-256 of the empty message" (hex ((Merlin.permute empty).toList.take 32 |>.map (·.toNat)) ==
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a")
  -- the conformance vector of Merlin 1.0 (the test `transcript_test_vector` of the merlin crate)
  let text := Merlin.bytesOfText
  let transcript := (Merlin.Transcript.new (text "test protocol")).appendMessage (text "some label")
    (text "some data")
  check "the Merlin conformance vector" (hex (transcript.challengeBytes (text "challenge") 32).1 ==
    "d5a21972d0d5fe320c0d263fac7fffb8145aa640af6e9bca177c03c7efcf0615")
  -- a transcript as numbers and back
  check "a transcript as numbers" (Merlin.Transcript.toNumbers (Merlin.Transcript.ofNumbers
    transcript.toNumbers) == transcript.toNumbers)

#eval show IO Unit from do
  let put (type : Closed) (value : Datum) : List Nat :=
    match applied "layout.canonical.put" [.type type] [Datum.ofBytes [], value] with
    | some [written] => written.toBytes
    | _ => []
  let take (type : Closed) (bytes : List Nat) : Option (List Datum) :=
    applied "layout.canonical.take" [.type type] [Datum.ofBytes bytes]
  let point (scalar : Nat) : Datum := Datum.ofPoint (scalePoint generator scalar)
  -- a scalar in 32 bytes, least significant first, and a natural in groups of seven bits, least
  -- significant first, each but the last with its high bit set
  check "a scalar, least significant first" (hex (put scalar (.number
    0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20)) ==
    "201f1e1d1c1b1a191817161514131211100f0e0d0c0b0a090807060504030201")
  check "a natural, in groups of seven bits" (hex (put .nat (.number 0x0102030405060708)) == "888e98a8c0e0808101")
  -- a challenge: 64 squeezed bytes, most significant first, modulo the order
  check "the reduction of 64 squeezed bytes" (reduceChallenge bls12381Order
    (List.replicate 32 0 ++ bigEndian 32 (bls12381Order + 5)) == 5)
  let response := 0x0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20
  let nonce := 5
  -- the reader on what the writer writes, with bytes after it
  for (type, value) in [(g1, point 7), (g1, point 0), (scalar, Datum.number response),
      (.tuple [.bool, .index 5, koalaBear], Datum.sequence [.number 1, .number 4, .number 9]),
      (.seq scalar none, Datum.sequence [.number 1, .number 2]),
      (.seq g1 (some 2), Datum.sequence [point 2, point 3]), (ext4, Datum.sequence [.number 1,
        .number 2, .number 3, .number 4]), (.nonzero scalar, Datum.number 5)] do
    let written := put type value
    check s!"{reprStr type}: read back" (take type (written ++ [7]) ==
      some [Datum.ofBool true, value, Datum.ofBytes [7]])
    -- each proper prefix is refused, with the reader left as it was
    for length in [0:written.length] do
      match take type (written.take length) with
      | some [flag, _, rest] =>
        check s!"{reprStr type}: a prefix of {length} bytes" (!flag.toBool && rest.toBytes == written.take length)
      | _ => check s!"{reprStr type}: a prefix of {length} bytes is taken" false
  -- what the writer does not write is refused: a changed flag of a point, a coordinate not below
  -- the characteristic, a scalar not below the order, a bool of 2, zero for a unit (the sign flag
  -- flipped is the negation of the point, a value)
  let changed := put g1 (point 7)
  for (label, type, bytes) in [("the compression flag cleared", g1, (changed.headD 0 - 0x80) :: changed.tail),
      ("x at the characteristic", g1, let x := bigEndian 48 baseModulus; (x.headD 0 + 0x80) :: x.tail),
      ("the infinity flag set", g1, (changed.headD 0 ||| 0x40) :: changed.tail),
      ("a scalar at the order", scalar, (littleEndian 32 bls12381Order).map (·.val)),
      ("a bool of 2", .bool, [2]), ("zero for a unit", .nonzero scalar, List.replicate 32 0)] do
    match take type bytes with
    | some [flag, _, _] => check s!"{label} is refused" (!flag.toBool)
    | _ => check s!"{label}: no result" false
  -- the bytes absorbed are the bytes written: absorbing `R` equals appending its layout bytes
  let label := Datum.sequence [.number 1, .number 0, .number 1, .number 0, .number 1]
  let some [started] := applied "suite.merlin3.bls12-381.fr64be/0.start" [] [Datum.ofBytes (List.replicate 32 9)]
    | check "start" false
  let some [absorbed] := applied "suite.merlin3.bls12-381.fr64be/0.absorb" [.type g1]
      [started, label, point nonce]
    | check "absorb" false
  let expected := ((Merlin.Transcript.new (Merlin.bytesOfText "suite.merlin3.bls12-381.fr64be/0")).appendMessage
      (Merlin.bytesOfText "identity") (List.replicate 32 9)).appendMessage (labelBytes label) (put g1 (point nonce))
  check "an absorbed value" (absorbed.toBytes == expected.toNumbers)
  -- a derivation at the challenge field, and none at another law
  match applied "suite.merlin3.bls12-381.fr64be/0.derive" [.type scalar] [absorbed, label] with
  | some [challenge, _] =>
    let (squeezed, _) := expected.challengeBytes (labelBytes label) 64
    check "a derived challenge" (challenge.toNat == reduceChallenge bls12381Order squeezed)
  | _ => check "derive" false
  check "no derivation at koala-bear"
    ((applied "suite.merlin3.bls12-381.fr64be/0.derive" [.type koalaBear] [absorbed, label]).isNone)

end VocabularyChecks
