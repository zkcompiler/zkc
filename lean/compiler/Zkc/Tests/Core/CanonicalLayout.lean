import Zkc.Tests.Core.Check
import Zkc.Core.Package
import Zkc.Core.VocabularyModel

/-! Checks of the canonical layout: the formats, the rows that are made of them, and the limit.

- The statements that the laws take have instances: the formats of numbers are lawful, a type
  without a point of G1 has its laws without a hypothesis, the rows of a package under a limit
  exist, and the functions that a run runs are the functions of the meaning, cut at the limit.
- In the model of a package that puts and takes an index below `2^65`, the row that puts
  appends the bytes of the value and the row that takes, on those bytes followed by anything,
  gives the value and what follows, for every value of the type: the statements about the rows
  of the layout in the model of a package have an instance.
- The hypothesis of the compressed encoding of G1 has no proof here. Its executable check: the
  bytes of the point at infinity and of multiples of the generator are read back as the points,
  and the published vectors of the encoding are decided as they state.
- The width that a format states is the number of bytes of its values.
- The widths: `index<1>` takes no bytes, `index<2>` and `index<256>` one, `index<257>` two,
  `index<2^64>` eight, `index<2^64+1>` and `index<2^65>` nine; the largest value of each is read
  back, the bound is not a value, and its bytes are refused where the width holds it.
- A natural: 0, 127, 128 and `2^64` have the bytes of the shortest form, and every form with one
  more group, a form cut short and no bytes are refused.
- Two indices below `2^65` that differ by `2^64` have different bytes and each is read back; a
  collection of two values of no bytes is read back, with and without bytes after it, and
  leaves them; a function of an admitted package that puts and takes either returns it.
- A collection of tuples that contain collections and parts of no bytes is read back; every
  proper prefix of its bytes is refused, with the reader unchanged.
- The limit: a length that asks for more elements of no bytes than the limit is the limit, and
  not a refusal; with elements that take bytes, a length that the bytes do not hold is a
  refusal; the limit counts the elements of every collection in a value; a reading under a
  limit that it does not reach is the reading. A run that reaches the limit ends with the
  limit, which is neither a return nor a stop.
- The row of the suite that absorbs a value gives different transcripts for two different
  values of one type.
- An input of type G1 is valid when it is a point of the group: a point of the curve outside the
  group is not, and a run refuses it. The parts of a tuple, a record, a collection and a variant
  are checked each at its type.
-/

set_option autoImplicit false

open Zkc.Source Zkc.Core Zkc.Core.Vocabulary Zkc.Core.Concrete

namespace CanonicalLayoutChecks

def check (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError s!"canonical layout: {label}")

def koalaBear : Closed := .row "koala-bear"
def scalar : Closed := .row "bls12-381.fr"
def g1 : Closed := .row "bls12-381.g1"

/-- The type with one value, which takes no bytes. -/
def unit : Closed := .tuple []

/-- A collection of tuples that contain collections and parts of no bytes. -/
def nested : Closed :=
  .seq (.tuple [.seq (.index 300) none, unit, .index 1, .seq unit (some 3), .bool, koalaBear,
    .seq unit none]) none

def nestedValue : Datum :=
  let unitDatum := Datum.sequence []
  .sequence [
    .sequence [.sequence [.number 299, .number 0, .number 256], unitDatum, .number 0,
      .sequence [unitDatum, unitDatum, unitDatum], .number 1, .number 2130706432,
      .sequence [unitDatum, unitDatum]],
    .sequence [.sequence [], unitDatum, .number 0, .sequence [unitDatum, unitDatum, unitDatum],
      .number 0, .number 7, .sequence []]]

/-! ## The statements that the laws take -/

/-- The formats of numbers are lawful. -/
theorem numbers_lawful : (Format.below 300).Lawful ∧ Format.natural.Lawful ∧
    (Format.number 5 0).Lawful :=
  ⟨Format.below_lawful 300, Format.natural_lawful, Format.number_lawful 5 0⟩

/-- The readers under a limit of the formats of numbers agree with their readers. -/
theorem numbers_agree : (Format.below 300).Agrees ∧ Format.natural.Agrees :=
  ⟨Format.below_agrees 300, Format.natural_agrees⟩

/-- A number is seen as a datum and back. -/
theorem number_views : Format.Views Datum.number asNumber := views_number

/-- The nested type has a format. -/
theorem nested_built : (formatOf table nested).isSome = true := by decide +kernel

/-- The nested type has no point of G1 in it, so its laws take no hypothesis. -/
theorem nested_lawful {format : Format Datum} (built : formatOf table nested = some format) :
    format.Lawful :=
  formatOf_lawful_of_no_point table built (by decide +kernel)

/-- A wide index and a collection of values of no bytes have their laws without a hypothesis. -/
theorem wide_index_lawful {format : Format Datum}
    (built : formatOf table (.index (2 ^ 65)) = some format) : format.Lawful :=
  formatOf_lawful_of_no_point table built rfl

theorem units_lawful {format : Format Datum}
    (built : formatOf table (.seq unit none) = some format) : format.Lawful :=
  formatOf_lawful_of_no_point table built rfl

/-- A type with a point of G1 in it has its laws under the hypothesis of the encoding. -/
theorem points_lawful (compression : PointCompression) {format : Format Datum}
    (built : formatOf table (.seq g1 (some 2)) = some format) : format.Lawful :=
  formatOf_lawful table _ built fun _ => compression

/-- The reader under a limit of the nested type agrees with its reader. -/
theorem nested_agrees {format : Format Datum} (built : formatOf table nested = some format) :
    format.Agrees :=
  formatOf_agrees table nested built

/-- The width of a bound is the least that holds every number below it, at the bounds where it
changes. -/
theorem widths : [0, 1, 2, 256, 257, 2 ^ 64, 2 ^ 64 + 1, 2 ^ 65].map byteWidth =
    [0, 0, 1, 1, 2, 8, 9, 9] := by decide +kernel

/-! ## The packages of the checks -/

/-- A package whose one function puts a value of a type on a writer and takes a value of the
type from what it wrote. -/
def roundTrip (type : Ty) : Raw.Package where
  types := []
  records := []
  variants := []
  operations := [
    { identity := ⟨Name.ofString "layout.canonical.put", [.type type]⟩
      signature := ⟨[bytesType, type], [bytesType], .pure⟩ },
    { identity := ⟨Name.ofString "layout.canonical.take", [.type type]⟩
      signature := ⟨[bytesType], [.bool, type, bytesType], .pure⟩ }]
  functions := [⟨false, [bytesType, type], [.bool, type, bytesType],
    some (.step (.op 0 [0, 1]) (.step (.op 1 [2]) (.ret [3, 4, 5])))⟩]
  protocols := []
  names := none

/-- A package whose one function takes a value of a type from a reader, guards the flag with
`reject` and returns the value and the rest. -/
def taking (type : Ty) : Raw.Package where
  types := []
  records := []
  variants := []
  operations := [
    { identity := ⟨Name.ofString "layout.canonical.take", [.type type]⟩
      signature := ⟨[bytesType], [.bool, type, bytesType], .pure⟩ }]
  functions := [⟨false, [bytesType], [type, bytesType],
    some (.step (.op 0 [0]) (.step (.guard .reject 1) (.ret [2, 3])))⟩]
  protocols := []
  names := none

/-- The rows of a package under a limit exist, and the functions that a run runs are the
functions of the meaning, cut at the limit. -/
def takingRows : LimitedRows (model table (taking (.seq (.tuple []) none))) :=
  limitedRows table (taking (.seq (.tuple []) none)) 4 0

theorem taking_within (typed : Typed) :
    TableWithin (limitedFunctions table (taking (.seq (.tuple []) none)) typed 4)
      (typed.program.functionTable (model table (taking (.seq (.tuple []) none)))) :=
  limitedFunctions_within table _ typed 4

/-- The format of an index below `2^65`. -/
def wideFormat : Format Datum := numbers (Format.below (2 ^ 65))

theorem wide_built : formatOf table (.index (2 ^ 65)) = some wideFormat := rfl

/-- Every index below `2^65` is of the domain of the format: none is left out. -/
theorem wide_domain (value : Fin (2 ^ 65)) :
    wideFormat.domain (Concrete.toDatum (.fin (2 ^ 65)) value) = true := by
  rw [Concrete.toDatum_fin]
  show (Format.below (2 ^ 65)).domain value.val = true
  rw [Format.below_domain]
  exact decide_eq_true value.isLt

/-- In the model of the package that puts and takes an index below `2^65`, the row that puts
appends the bytes of the value, and the row that takes, on those bytes followed by anything,
gives the flag `true`, the value and what follows: for every value of the type. -/
theorem wide_put (writer : Bytes) (value : Fin (2 ^ 65)) :
    (model table (roundTrip (.fin (2 ^ 65)))).pure ⟨0, [bytesType, .fin (2 ^ 65)], [bytesType]⟩
        rfl (.cons writer (.cons value .nil)) =
      .cons (writer ++ wideFormat.write (Concrete.toDatum (.fin (2 ^ 65)) value)) .nil := by
  have found : (roundTrip (.fin (2 ^ 65))).operations[0]? =
      some ⟨⟨Name.ofString "layout.canonical.put", [.type (.fin (2 ^ 65))]⟩,
        ⟨[bytesType, .fin (2 ^ 65)], [bytesType], .pure⟩⟩ := rfl
  exact model_put found (by decide +kernel) (closed := .index (2 ^ 65)) (by rfl) wide_built
    (wide_index_lawful wide_built) (type := .fin (2 ^ 65)) rfl writer value (wide_domain value)

theorem wide_take (value : Fin (2 ^ 65)) (rest : Bytes) :
    (model table (roundTrip (.fin (2 ^ 65)))).pure
        ⟨1, [bytesType], [.bool, .fin (2 ^ 65), bytesType]⟩ rfl
        (.cons (wideFormat.write (Concrete.toDatum (.fin (2 ^ 65)) value) ++ rest) .nil) =
      .cons true (.cons value (.cons rest .nil)) := by
  have found : (roundTrip (.fin (2 ^ 65))).operations[1]? =
      some ⟨⟨Name.ofString "layout.canonical.take", [.type (.fin (2 ^ 65))]⟩,
        ⟨[bytesType], [.bool, .fin (2 ^ 65), bytesType], .pure⟩⟩ := rfl
  exact model_take found (by decide +kernel) (closed := .index (2 ^ 65)) (by rfl) wide_built
    (wide_index_lawful wide_built) (type := .fin (2 ^ 65)) rfl value (wide_domain value) rest

/-! ## The rows on data -/

/-- The bytes that the layout writes for a value of a type, when the type has a format and the
datum is a value of it. -/
def written (type : Closed) (value : Datum) : Option (List Nat) :=
  match applyRow table "layout.canonical.put" [.type type] [bytesDatum [], value] with
  | .ok [bytes] => some bytes.toBytes
  | _ => none

/-- What the row that takes a value gives. -/
inductive Taken where
  | value (value : Datum) (rest : List Nat)
  | refused (reader : List Nat)
  | limit (elements : Nat)
  | other
  deriving BEq, Repr

def taken (type : Closed) (bytes : List Nat) (limit : Option Nat := none) : Taken :=
  match applyRow table "layout.canonical.take" [.type type] [Datum.ofBytes bytes] limit with
  | .ok [flag, value, rest] =>
    if flag.toBool then .value value rest.toBytes else .refused rest.toBytes
  | .error (.limit elements) => .limit elements
  | _ => .other

/-- The bytes of a natural in the layout. -/
def natural (value : Nat) : List Nat := (writeNatural value).map (·.val)

/-- A value is written, read back with nothing after it and with bytes after it, which it
leaves; every proper prefix of its bytes is refused, with the reader unchanged. -/
def checkValue (label : String) (type : Closed) (value : Datum) : IO (List Nat) := do
  let some bytes := written type value | throw (IO.userError s!"canonical layout: {label}: not written")
  check s!"{label}: read back" (taken type bytes == .value value [])
  check s!"{label}: read back with bytes after it" (taken type (bytes ++ [7, 8]) == .value value [7, 8])
  for length in [0:bytes.length] do
    check s!"{label}: the prefix of {length} bytes is refused"
      (taken type (bytes.take length) == .refused (bytes.take length))
  return bytes

def describe : Run → String
  | .returned outputs => s!"returned {reprStr outputs}"
  | .stopped reason => s!"stopped {reprStr reason}"
  | .limit elements => s!"reached the limit of {elements} elements"
  | .failed message => s!"failed: {message}"

def returns (run : Run) (wanted : List Datum) : Bool :=
  match run with
  | .returned outputs => outputs == wanted
  | _ => false

/-! ## The encoding of a point of G1 -/

/-- Bytes from hexadecimal. -/
def unhex (text : String) : List Nat :=
  let digit (c : Char) : Nat := if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10
  let rec pairs : List Char → List Nat
    | high :: low :: rest => (16 * digit high + digit low) :: pairs rest
    | _ => []
  pairs text.toList

/-- The published vectors of the deserialization of G1, with whether each is accepted:
`case08_deserialization_G1` of `main.py` in github.com/ethereum/bls12-381-tests, commit 006855c5. -/
def g1Vectors : List (String × Bool) := [
  ("a491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a", true),
  ("8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", false),
  ("8123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcde0", false),
  ("9a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab", false),
  ("9a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaac", false),
  ("9a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaa", false),
  ("9a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaa900", false),
  ("c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", true),
  ("c01000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", false),
  ("800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", false),
  ("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", false),
  ("c123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef", false),
  ("e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", false),
  ("e491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a", false),
  ("6491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a", false),
  ("2491d1b0ecd9bb917989f0e74f0dea0422eac4a873e5e2644f368dffb9a6e20fd6e10c1b77654d067c0618f6e5a7f79a", false)]

-- The executable check of the hypothesis `PointCompression`: the bytes of points of the group
-- are read back as the points.
#eval show IO Unit from do
  for multiple in [0, 1, 2, 3, 7, 1000003, scalarModulus - 1] do
    let point := scalePoint generator multiple
    check s!"{multiple} times the generator is of the group" (inGroup point)
    check s!"{multiple} times the generator is read back from its bytes"
      (decompressPoint (compressPoint point) == some point)
    check s!"{multiple} times the generator is 48 bytes" ((compressPoint point).length == 48)
  -- the compressed encoding of a point of G1 is the ZCash serialization format
  -- (draft-irtf-cfrg-pairing-friendly-curves-11, appendix C); its published vectors of
  -- deserialization: the two that are accepted are read, of the group, and written back to the
  -- same bytes; the others are refused
  for (vector, accepted) in g1Vectors do
    let bytes := (unhex vector).map Byte.ofNat
    match decompressPoint bytes with
    | some point =>
      check s!"the published point {vector.take 12}… is accepted" accepted
      check s!"the published point {vector.take 12}… is of the group" (inGroup point)
      check s!"the published point {vector.take 12}… is written back" (compressPoint point == bytes)
      check s!"the published point {vector.take 12}… is read by the layout"
        (taken g1 (unhex vector ++ [5]) == .value (Datum.ofPoint point) [5])
    | none => check s!"the published point {vector.take 12}… is refused" (!accepted)
  -- a point of the curve that is not of the group is not a value. A writer checks that a point
  -- is on the curve and leaves the group to the reader: the bytes of such a point are refused
  let outside : Concrete.Point := some (0, 2)
  check "a point of the curve outside the group" (onCurve outside && !inGroup outside)
  check "a point outside the group is not of the domain"
    ((formatOf table g1).map (·.domain (Datum.ofPoint outside)) == some false)
  match written g1 (Datum.ofPoint outside) with
  | some bytes => check "the bytes of a point outside the group are refused" (taken g1 bytes == .refused bytes)
  | none => check "a point of the curve is admitted" false
  check "a point that is not on the curve is not written" ((written g1 (Datum.ofPoint (some (1, 1)))).isNone)
  check "a datum that is not a point is not written" ((written g1 (.number 0)).isNone)

/-! ## The widths, the naturals and the two defects -/

#eval show IO Unit from do
  -- an index: the fewest bytes that hold every number below the bound
  for (bound, width) in [(1, 0), (2, 1), (256, 1), (257, 2), (2 ^ 64, 8), (2 ^ 64 + 1, 9),
      (2 ^ 65, 9)] do
    let type := Closed.index bound
    let bytes ← checkValue s!"index<{bound}>, its largest value" type (.number (bound - 1))
    check s!"index<{bound}> takes {width} bytes" (bytes.length == width)
    let zero ← checkValue s!"index<{bound}>, zero" type (.number 0)
    check s!"index<{bound}>, zero in {width} bytes" (zero == List.replicate width 0)
    check s!"index<{bound}>: the bound is not a value" ((written type (.number bound)).isNone)
    -- the bytes of the bound, where the width holds it
    if bound < 256 ^ width then
      let ofBound := (littleEndian width bound).map (·.val)
      check s!"index<{bound}>: the bytes of the bound are refused" (taken type ofBound == .refused ofBound)
  check "index<1> reads its value from no bytes and leaves what follows"
    (taken (.index 1) [9] == .value (.number 0) [9])
  check "index<0> has no value" ((written (.index 0) (.number 0)).isNone && taken (.index 0) [] == .refused [])
  check "a bool is one byte" (written .bool (.number 1) == some [1] && written .bool (.number 0) == some [0])
  check "a bool of 2 is refused" (taken .bool [2] == .refused [2] && (written .bool (.number 2)).isNone)
  -- a natural: unsigned LEB128 in its shortest form
  for (value, bytes) in [(0, [0]), (127, [127]), (128, [128, 1]), (300, [172, 2]),
      (2 ^ 64, List.replicate 9 128 ++ [2])] do
    let found ← checkValue s!"the natural {value}" .nat (.number value)
    check s!"the natural {value} is {bytes}" (found == bytes)
    -- the form with one more group, of zero
    let longer := bytes.dropLast ++ [bytes.getLastD 0 + 128, 0]
    check s!"the natural {value} with a last group of zero is refused" (taken .nat longer == .refused longer)
    let longest := bytes.dropLast ++ [bytes.getLastD 0 + 128, 128, 0]
    check s!"the natural {value} with two last groups of zero is refused" (taken .nat longest == .refused longest)
  check "no bytes are not a natural" (taken .nat [] == .refused [])
  check "a natural cut after a group that announces another is refused" (taken .nat [128] == .refused [128])
  check "a natural with a group of zero in the middle" (taken .nat [128, 128, 1] == .value (.number 16384) [])
  -- two indices that differ by 2^64 have different bytes, and each is read back
  let wide := Closed.index (2 ^ 65)
  let small ← checkValue "index<2^65>, zero" wide (.number 0)
  let large ← checkValue "index<2^65>, 2^64" wide (.number (2 ^ 64))
  check "0 and 2^64 below 2^65 have different bytes" (small != large)
  check "2^64 below 2^65 is eight bytes of zero and a one" (large == List.replicate 8 0 ++ [1])
  -- a collection of values of no bytes: its length, and nothing else
  let unitDatum := Datum.sequence []
  let units ← checkValue "a collection of two units" (.seq unit none) (.sequence [unitDatum, unitDatum])
  check "a collection of two units is its length" (units == [2])
  let sized ← checkValue "a sized collection of two units" (.seq unit (some 2)) (.sequence [unitDatum, unitDatum])
  check "a sized collection of two units takes no bytes" (sized == [])
  -- every type with one value takes no bytes
  for (label, type, value) in [("the unit", unit, unitDatum), ("index<1>", Closed.index 1, Datum.number 0),
      ("five of index<1>", .seq (.index 1) (some 5), .sequence (List.replicate 5 (.number 0))),
      ("no bool", .seq .bool (some 0), .sequence []),
      ("a tuple of parts of no bytes", .tuple [unit, .index 1, .seq unit (some 2)],
        .sequence [unitDatum, .number 0, .sequence [unitDatum, unitDatum]])] do
    check s!"{label} takes no bytes" (written type value == some [])
    check s!"{label} is read from no bytes and leaves what follows" (taken type [3] == .value value [3])
  -- a collection of tuples that contain collections and parts of no bytes
  let bytes ← checkValue "the nested collection" nested nestedValue
  check "the nested collection, byte by byte" (bytes ==
    [2] ++ ([3] ++ [43, 1] ++ [0, 0] ++ [0, 1]) ++ [1] ++ [0, 0, 0, 127] ++ [2] ++
      [0] ++ [0] ++ [7, 0, 0, 0] ++ [0])
  -- the width that a format states is the width of its values; a type with a part of variable
  -- length states none
  let width (type : Closed) : Option Nat := (formatOf table type).bind (·.width)
  for (label, type, value, stated) in [
      ("a scalar", scalar, Datum.number 5, some 32),
      ("an element of the quartic extension", .row "koala-bear.ext4",
        .sequence [.number 1, .number 2, .number 3, .number 4], some 16),
      ("a point", g1, Datum.ofPoint generator, some 48),
      ("a tuple of fixed parts", .tuple [.bool, .index 257, .seq koalaBear (some 3), unit],
        .sequence [.number 1, .number 256, .sequence [.number 1, .number 2, .number 3], unitDatum],
        some 15),
      ("a natural", .nat, .number 5, none),
      ("a collection without a size", .seq .bool none, .sequence [.number 1], none)] do
    check s!"{label}: the stated width" (width type == stated)
    if let some bytes := stated then
      check s!"{label}: written in its width" ((written type value).map (·.length) == some bytes)
  -- a value of another shape is not a value of the type
  check "a tuple of fewer components is not written" ((written (.tuple [.bool, .bool]) (.sequence [.number 1])).isNone)
  check "a sized collection of another length is not written"
    ((written (.seq .bool (some 2)) (.sequence [.number 1])).isNone)
  check "a number is not a collection" ((written (.seq .bool none) (.number 1)).isNone)
  check "a type without a format has no row" ((written (.row "bls12-381.g2") (.sequence [])).isNone)

/-! ## The limit -/

#eval show IO Unit from do
  let units := Closed.seq unit none
  let unitDatum := Datum.sequence []
  -- a length that asks for more elements of no bytes than the limit: the limit, not a refusal
  check "five units under a limit of four reach the limit" (taken units (natural 5) (some 4) == .limit 4)
  check "five units under a limit of five are read"
    (taken units (natural 5) (some 5) == .value (.sequence (List.replicate 5 unitDatum)) [])
  check "2^60 units under the default limit reach the limit"
    (taken units (natural (2 ^ 60)) (some defaultLimit) == .limit defaultLimit)
  check "the default limit" (defaultLimit == 1048576)
  -- with elements that take bytes, a length that the bytes do not hold is a refusal
  let short := natural (2 ^ 60) ++ [1, 2, 3, 4, 5]
  check "2^60 scalars in five bytes are refused" (taken (.seq scalar none) short (some 16) == .refused short)
  check "2^60 scalars in five bytes are refused, without a limit" (taken (.seq scalar none) short == .refused short)
  -- the limit counts the elements of every collection in a value
  let lists := Closed.seq units none
  let three := natural 3 ++ natural 2 ++ natural 2 ++ natural 2
  let pairs := Datum.sequence (List.replicate 3 (.sequence [unitDatum, unitDatum]))
  check "three collections of two units under a limit of eight reach the limit"
    (taken lists three (some 8) == .limit 8)
  check "three collections of two units under a limit of nine are read"
    (taken lists three (some 9) == .value pairs [])
  -- a type whose every value has more elements than the limit
  check "a collection of a size above the limit"
    (taken (.seq (.index 256) (some (2 ^ 30))) [] (some defaultLimit) == .limit defaultLimit)
  check "a sized collection under a limit below its size reaches the limit"
    (taken (.seq unit (some 5)) [] (some 4) == .limit 4)
  -- a reading under a limit that it does not reach is the reading
  let some bytes := written nested nestedValue | check "the nested collection is written" false
  for limit in [13, 14, 1000] do
    check s!"the nested collection under a limit of {limit}"
      (taken nested (bytes ++ [9]) (some limit) == taken nested (bytes ++ [9]))
  check "the nested collection has thirteen elements" (taken nested bytes (some 12) == .limit 12)
  for length in [0:bytes.length] do
    check s!"the prefix of {length} bytes of the nested collection, under a limit"
      (taken nested (bytes.take length) (some 1000) == .refused (bytes.take length))
  -- a long collection is read in a loop, each element from its own bytes
  let long := Datum.sequence ((List.range 50000).map fun index => .number (index % 256))
  let some longBytes := written (.seq (.index 256) none) long | check "a long collection is written" false
  check "a collection of 50,000 bytes is its length and its bytes" (longBytes.length == 50003)
  check "a collection of 50,000 bytes is read back"
    (taken (.seq (.index 256) none) (longBytes ++ [1]) (some defaultLimit) == .value long [1])
  -- a run: the limit is its own end, neither a return nor a stop
  let package := taking (.seq (.tuple []) none)
  check "the package that takes a collection of units is admitted" ((missing table package).isEmpty)
  let five := Datum.ofBytes (natural 5 ++ [7])
  let reached := runData table package 0 [five] (limit := 4)
  check s!"a run that reaches the limit: {describe reached}"
    (match reached with | .limit 4 => true | _ => false)
  let read := runData table package 0 [five] (limit := 5)
  check s!"a run under a limit that it does not reach: {describe read}"
    (returns read [.sequence (List.replicate 5 unitDatum), Datum.ofBytes [7]])
  let huge := runData table package 0 [Datum.ofBytes (natural (2 ^ 60))]
  check s!"a run that is asked for 2^60 units: {describe huge}"
    (match huge with | .limit elements => elements == defaultLimit | _ => false)
  let refused := runData table package 0 [Datum.ofBytes [128]]
  check s!"a run on bytes that are not a value stops `reject`: {describe refused}"
    (match refused with | .stopped .reject => true | _ => false)

/-! ## A function that puts and takes -/

#eval show IO Unit from do
  let unitDatum := Datum.sequence []
  let unitList := Datum.sequence [unitDatum, unitDatum]
  let wide := roundTrip (.fin (2 ^ 65))
  let units := roundTrip (.seq (.tuple []) none)
  check "a collection of units is admitted" ((missing table units).isEmpty)
  check "a wide index is admitted" ((missing table wide).isEmpty)
  check "2^64 is a value of index<2^65>" (validInput table #[] (.fin (2 ^ 65)) (.number (2 ^ 64)))
  check "2^64 below 2^65 is put and taken" (returns
    (runData table wide 0 [.sequence [], .number (2 ^ 64)]) [.number 1, .number (2 ^ 64), .sequence []])
  check "7 below 2^65 is put and taken" (returns
    (runData table wide 0 [.sequence [], .number 7]) [.number 1, .number 7, .sequence []])
  check "2^65 is not an input of index<2^65>" (match runData table wide 0 [.sequence [], .number (2 ^ 65)] with
    | .failed _ => true
    | _ => false)
  check "a collection of two units is put and taken" (returns
    (runData table units 0 [.sequence [], unitList]) [.number 1, unitList, .sequence []])
  check "a sized collection of two units is put and taken" (returns
    (runData table (roundTrip (.seq (.tuple []) (some 2))) 0 [.sequence [], unitList])
    [.number 1, unitList, .sequence []])
  -- a package at a type without a format is not admitted: the row is named
  let unwritten := taking (.nominal 0)
  let pairing : Raw.Package := { unwritten with types := [⟨Name.ofString "bls12-381.gt", []⟩] }
  match missing table pairing with
  | [message] =>
    check s!"the row without a format is named: {message}"
      ((message.splitOn "layout.canonical.take").length > 1)
  | other => check s!"a type without a format: {other}" false

/-! ## The inputs of a run -/

/-- A package whose one function returns its input, a point of G1. -/
def returning : Raw.Package where
  types := [⟨Name.ofString "bls12-381.g1", []⟩]
  records := []
  variants := []
  operations := []
  functions := [⟨false, [.nominal 0], [.nominal 0], some (.ret [0])⟩]
  protocols := []
  names := none

#eval show IO Unit from do
  let types : Array CatalogueRow := #[⟨Name.ofString "bls12-381.g1", []⟩]
  let valid (type : Ty) (datum : Datum) : Bool := validInput table types type datum
  -- an input of type G1 is a point of the group, not only a point of the curve
  let outside : Concrete.Point := some (0, 2)
  check "a point of the curve outside the group" (onCurve outside && !inGroup outside)
  check "a point of the curve outside the group is not a valid input"
    (!valid (.nominal 0) (Datum.ofPoint outside))
  check "the generator is a valid input" (valid (.nominal 0) (Datum.ofPoint generator))
  check "the point at infinity is a valid input" (valid (.nominal 0) (Datum.ofPoint none))
  check "a point that is not on the curve is not a valid input"
    (!valid (.nominal 0) (Datum.ofPoint (some (1, 1))))
  check "a run returns a point of the group"
    (returns (runData table returning 0 [Datum.ofPoint generator]) [Datum.ofPoint generator])
  let refused := runData table returning 0 [Datum.ofPoint outside]
  check s!"a run refuses a point outside the group: {describe refused}"
    (match refused with | .failed message => message == "an input is not a value of its type" | _ => false)
  -- the parts of a value are checked each at its type
  let pair : Ty := .tuple [.bool, .nominal 0]
  check "a tuple with a point of the group" (valid pair (.sequence [.number 1, Datum.ofPoint generator]))
  check "a tuple with a point outside the group" (!valid pair (.sequence [.number 1, Datum.ofPoint outside]))
  check "a tuple of fewer components" (!valid pair (.sequence [.number 1]))
  check "a tuple of more components"
    (!valid pair (.sequence [.number 1, Datum.ofPoint generator, .number 0]))
  check "a record as its fields" (valid (.record 0 .free [.fin 3, .bool]) (.sequence [.number 2, .number 0])
    && !valid (.record 0 .free [.fin 3, .bool]) (.sequence [.number 3, .number 0]))
  check "a sized collection of its size" (valid (.seq .bool (some 2)) (.sequence [.number 1, .number 0])
    && !valid (.seq .bool (some 2)) (.sequence [.number 1]))
  check "a collection with an element that is not a value" (!valid (.seq (.fin 3) none) (.sequence [.number 1, .number 3]))
  let choice : Ty := .variant 0 [.bool, .nat]
  check "a variant as its alternative and its payload" (valid choice (.sequence [.number 1, .number 7])
    && valid choice (.sequence [.number 0, .number 1]) && !valid choice (.sequence [.number 0, .number 7])
    && !valid choice (.sequence [.number 2, .number 0]))

/-! ## The absorbing row -/

#eval show IO Unit from do
  let applied (name : String) (arguments : List Value) (inputs : List Datum) : Option (List Datum) :=
    match applyRow table name arguments inputs with
    | .ok results => some results
    | .error _ => none
  let some [started] := applied "suite.merlin3.bls12-381.fr64be/0.start" [] [Datum.ofBytes (List.replicate 32 9)]
    | check "start" false
  let label := Datum.sequence [.number 1]
  let absorb (type : Closed) (value : Datum) : Option (List Datum) :=
    applied "suite.merlin3.bls12-381.fr64be/0.absorb" [.type type] [started, label, value]
  -- two different values of one type give different transcripts
  let unitDatum := Datum.sequence []
  for (label, type, first, second) in [
      ("0 and 2^64 below 2^65", Closed.index (2 ^ 65), Datum.number 0, Datum.number (2 ^ 64)),
      ("one unit and two", .seq unit none, .sequence [unitDatum], .sequence [unitDatum, unitDatum]),
      ("the naturals 127 and 128", .nat, .number 127, .number 128)] do
    match absorb type first, absorb type second with
    | some [one], some [other] => check s!"{label} are absorbed apart" (one != other)
    | _, _ => check s!"{label}: not absorbed" false
  -- what is absorbed is the bytes that the layout writes
  let some bytes := written nested nestedValue | check "the nested collection is written" false
  let expected := ((Merlin.Transcript.new (Merlin.bytesOfText "suite.merlin3.bls12-381.fr64be/0")).appendMessage
    (Merlin.bytesOfText "identity") (List.replicate 32 9)).appendMessage (labelBytes label) bytes
  match absorb nested nestedValue with
  | some [absorbed] => check "an absorbed collection" (absorbed.toBytes == expected.toNumbers)
  | _ => check "the nested collection is absorbed" false
  check "a datum that is not a value of the type is not absorbed" ((absorb (.index 5) (.number 5)).isNone)

end CanonicalLayoutChecks
