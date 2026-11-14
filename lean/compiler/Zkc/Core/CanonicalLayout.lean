module

public import Zkc.Core.FormatNumbers
public import Zkc.Core.VocabularyElements

@[expose] public section

/-! The canonical layout: the format of every closed type of the vocabulary that has one.

The layout `zkc::layout::canonical` writes a value of a closed type as the format that
`formatOf` builds for the type, from the formats of `Zkc.Core.Format` and
`Zkc.Core.FormatNumbers`:

- `index<n>`: the number in the fewest bytes that hold every number below `n`, the least `k`
  with `n ≤ 256 ^ k`, least significant first; a number not below `n` is not read. So
  `index<1>` takes no bytes, a byte one, `index<2^64>` eight and `index<2^65>` nine;
- `bool`: as `index<2>`, one byte;
- `nat`: of variable length, unsigned LEB128 in its shortest form; every other form is not read;
- a collection with a size: its elements, one after another; a collection without a size: its
  length as a `nat`, and then its elements;
- a tuple: its components, one after another; the tuple of no component, and every type built
  from parts of no bytes, takes no bytes;
- `nonzero<F>`: as `F`; zero is not read;
- an element of a prime field of the vocabulary: its natural in the field's `Bytes`, least
  significant first; a natural not below the order is not read. An element of an extension:
  its coefficients, lowest first, each as an element of the base;
- a point of `bls12-381.g1`: 48 bytes, the compressed form of the ZCash serialization format
  (draft-irtf-cfrg-pairing-friendly-curves-11, appendix C).

A type has a format exactly when every leaf of it is `bool`, `nat`, an `index<n>`, a prime field
or an extension of the vocabulary whose width holds its order, or `bls12-381.g1`, and every
`nonzero<F>` in it is at a type with arithmetic. The layout writes the values of a type with a
format and no other type.

The values of a type that its format writes are its domain, a property of data
(`Format.domain`): a number below the bound of an index, an element below the order of its
field, a point of the group, a sequence of as many values as a tuple has components or a sized
collection has elements.

The laws of the format of a type (`formatOf_lawful`): the round trip of a prefix, and that the
reader accepts only what the writer writes. The formats of numbers, of field elements and of
their compositions are proved. For a type with a point of G1 in it the laws take one hypothesis
by name, `PointCompression`: that the bytes of a point of the group are read back as the point.
It needs the arithmetic of the base field of the curve (that the square root which the reader
computes is the ordinate), which this package, without a mathematics library, does not prove.
That the reader of a point gives only a point of the group, from exactly the bytes that the
writer writes for it, is proved (`decompressPoint_canonical`).

The reader under a limit agrees with the reader whenever it answers, for every type, without a
hypothesis (`formatOf_agrees`).
-/

set_option autoImplicit false

namespace Zkc.Core.Vocabulary

open Zkc.Core.Concrete (Datum)

/-! ## Data as numbers, as sequences and as points -/

/-- The number that a datum is. -/
def asNumber : Datum → Option Nat
  | .number value => some value
  | .sequence _ => none

/-- The items of a datum that is a sequence. -/
def asItems : Datum → Option (List Datum)
  | .sequence items => some items
  | .number _ => none

/-- The point that a datum is: no item for the point at infinity, or two coordinates. -/
def asPoint : Datum → Option Concrete.Point
  | .sequence [] => some none
  | .sequence [.number x, .number y] => some (some (x, y))
  | _ => none

theorem views_number : Format.Views Datum.number asNumber where
  view_image := fun _ => rfl
  image_view := by
    intro value inner viewed
    cases value with
    | number found => cases viewed; rfl
    | sequence items => cases viewed

theorem views_sequence : Format.Views Datum.sequence asItems where
  view_image := fun _ => rfl
  image_view := by
    intro value inner viewed
    cases value with
    | number found => cases viewed
    | sequence items => cases viewed; rfl

theorem views_point : Format.Views Datum.ofPoint asPoint where
  view_image := by
    intro point
    match point with
    | none => rfl
    | some (x, y) => rfl
  image_view := by
    intro value inner viewed
    unfold asPoint at viewed
    split at viewed
    · cases viewed; rfl
    · cases viewed; rfl
    · cases viewed

/-- A format of numbers as a format of data: a number as the datum of it. -/
def numbers (format : Format Nat) : Format Datum := format.through Datum.number asNumber

/-- A format of lists of data as a format of data: a list as the sequence of it. -/
def sequences (format : Format (List Datum)) : Format Datum :=
  format.through Datum.sequence asItems

/-! ## A point of G1 compressed -/

/-- The compressed encoding of a point of BLS12-381 G1 in the ZCash serialization format
(draft-irtf-cfrg-pairing-friendly-curves-11, appendix C): `x` in 48 bytes,
most significant first, with three flags in the high bits of the first byte: compressed
(`0x80`), the point at infinity (`0x40`, all else zero), and `y` the larger of the two roots
(`0x20`). -/
def compressPoint : Concrete.Point → Bytes
  | none => Byte.ofNat 0xc0 :: List.replicate 47 (Byte.ofNat 0)
  | some (x, y) =>
    let digits := (littleEndian 48 x).reverse
    let flags := 0x80 + (if y > (Concrete.baseModulus - 1) / 2 then 0x20 else 0)
    Byte.ofNat ((digits.headD (Byte.ofNat 0)).val + flags) :: digits.tail

/-- The point whose compressed encoding 48 bytes could be, from their flags and the abscissa
they state: the square root of `x^3 + 4` is a power (the characteristic is 3 modulo 4). -/
def pointStated (bytes : Bytes) : Option Concrete.Point :=
  let numbers := bytes.map (·.val)
  let first := numbers.headD 0
  let p := Concrete.baseModulus
  if first &&& 0x40 != 0 then some none
  else
    let x := Concrete.numberOf ((first &&& 0x1f) :: numbers.tail)
    let square := (x * x % p * x + 4) % p
    let root := Concrete.powerModulo square ((p + 1) / 4) p
    if x < p && root * root % p == square then
      some (some (x, if (root > (p - 1) / 2) == (first &&& 0x20 != 0) then root else (p - root) % p))
    else none

/-- The point of bytes in the compressed encoding, when they are the encoding of a point of the
group: the point they state is of the group, and they are exactly the bytes that
`compressPoint` writes for it. -/
def decompressPoint (bytes : Bytes) : Option Concrete.Point :=
  match pointStated bytes with
  | some point => if compressPoint point == bytes && inGroup point then some point else none
  | none => none

/-- A compressed point is 48 bytes. -/
theorem compressPoint_length (point : Concrete.Point) : (compressPoint point).length = 48 := by
  match point with
  | none => simp [compressPoint]
  | some (x, y) => simp [compressPoint, littleEndian_length]

/-- Only the compressed encoding of a point of the group is read as a point: what is read is of
the group, and the bytes are those that the writer writes for it. -/
theorem decompressPoint_canonical {bytes : Bytes} {point : Concrete.Point}
    (read : decompressPoint bytes = some point) :
    inGroup point = true ∧ compressPoint point = bytes := by
  unfold decompressPoint at read
  cases stated : pointStated bytes with
  | none => simp [stated] at read
  | some candidate =>
    simp only [stated] at read
    by_cases accepted : (compressPoint candidate == bytes && inGroup candidate) = true
    · simp only [accepted, ↓reduceIte, Option.some.injEq] at read
      subst read
      simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      exact ⟨accepted.2, accepted.1⟩
    · simp [accepted] at read

/-- What the core takes as a hypothesis of the compressed encoding of G1: the bytes of a point
of the group are read back as the point. It says that the square root which the reader computes
from the abscissa is the ordinate of the point or its negation, a fact of the arithmetic of the
base field, which this package does not prove. The published vectors of the encoding and the
round trip of multiples of the generator are its executable checks. -/
structure PointCompression : Prop where
  reads_written : ∀ point, inGroup point = true →
    decompressPoint (compressPoint point) = some point

/-- A point of G1 in 48 bytes. A caller checks of a point that it is on the curve: whether it
is of the group takes a scalar multiplication, which the reader makes of every point it reads.
The reader looks at no more than 48 bytes. -/
def pointFormat : Format Concrete.Point where
  domain := inGroup
  admits := Concrete.onCurve
  write := compressPoint
  read bytes :=
    match decompressPoint (bytes.take 48) with
    | some point => some (point, bytes.drop 48)
    | none => none
  width := some 48
  readWithin limit bytes :=
    Reading.ofOption limit
      (match decompressPoint (bytes.take 48) with
      | some point => some (point, bytes.drop 48)
      | none => none)

theorem pointFormat_lawful (compression : PointCompression) : pointFormat.Lawful where
  round_trip := by
    intro point inDomain rest
    simp only [pointFormat] at inDomain ⊢
    have length := compressPoint_length point
    have taken : (compressPoint point ++ rest).take 48 = compressPoint point := by
      rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    have dropped : (compressPoint point ++ rest).drop 48 = rest := by
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega),
        List.nil_append]
    simp only [taken, dropped, compression.reads_written point inDomain]
  canonical := by
    intro bytes point rest read
    simp only [pointFormat] at read ⊢
    cases decompressed : decompressPoint (bytes.take 48) with
    | none => simp [decompressed] at read
    | some found =>
      simp only [decompressed, Option.some.injEq, Prod.mk.injEq] at read
      obtain ⟨rfl, rfl⟩ := read
      obtain ⟨ofGroup, written⟩ := decompressPoint_canonical decompressed
      exact ⟨ofGroup, by rw [written, List.take_append_drop]⟩
  width_written := by
    intro width stated point _
    simp only [pointFormat, Option.some.injEq] at stated ⊢
    rw [compressPoint_length, stated]
  admits_domain := by
    intro point inDomain
    simp only [pointFormat, inGroup, Bool.and_eq_true] at inDomain ⊢
    exact inDomain.1

theorem pointFormat_agrees : pointFormat.Agrees := by
  intro limit bytes result answered
  simp only [pointFormat, Reading.answer_ofOption, Option.some.injEq] at answered ⊢
  exact answered

/-! ## The leaves of the vocabulary -/

/-- The width of an element of a prime field of the vocabulary: its natural member `Bytes`. -/
def primeWidth (table : Table) (name : String) : Option Nat := do
  let entry ← table.type? name
  let (_, width) ← entry.naturalMembers.find? (·.1 == "Bytes")
  return width

/-- The width of a coefficient of an extension of the vocabulary: that of its `Base`. -/
def baseWidth (table : Table) (name : String) : Option Nat := do
  let entry ← table.type? name
  let (_, base) ← entry.typeMembers.find? (·.1 == "Base")
  let .row baseName := base | none
  primeWidth table baseName

/-- How the canonical layout writes a leaf of the vocabulary: a prime field in its width, an
extension by its coefficients, G1 compressed. -/
inductive Leaf where
  | prime (order width : Nat)
  | extension (order degree width : Nat)
  | curve
  deriving Repr, Inhabited, BEq

/-- The leaf that a type of the vocabulary is, when the layout writes it: a prime field or an
extension whose width holds every element (`order ≤ 256 ^ width`), or G1. -/
def leafOf (table : Table) (name : String) : Option Leaf :=
  match elementOf table (.row name) with
  | some (.prime order) =>
    match primeWidth table name with
    | some width => if order ≤ 256 ^ width then some (.prime order width) else none
    | none => none
  | some (.extension order degree _) =>
    match baseWidth table name with
    | some width => if order ≤ 256 ^ width then some (.extension order degree width) else none
    | none => none
  | some .curve => some .curve
  | none => none

/-- The format of a leaf: an element of a prime field as its natural in the field's width, an
element of an extension as its coefficients, each as an element of the base, a point of G1
compressed. -/
def Leaf.format : Leaf → Format Datum
  | .prime order width => numbers (Format.number order width)
  | .extension order degree width =>
    sequences (Format.each (List.replicate degree (numbers (Format.number order width))))
  | .curve => pointFormat.through Datum.ofPoint asPoint

theorem Leaf.format_lawful : ∀ (leaf : Leaf), (leaf = .curve → PointCompression) →
    leaf.format.Lawful
  | .prime order width, _ => Format.through_lawful (Format.number_lawful order width) views_number
  | .extension order degree width, _ =>
    Format.through_lawful
      (Format.each_lawful fun format member => by
        rw [List.eq_of_mem_replicate member]
        exact Format.through_lawful (Format.number_lawful order width) views_number)
      views_sequence
  | .curve, compression => Format.through_lawful (pointFormat_lawful (compression rfl)) views_point

theorem Leaf.format_agrees : ∀ (leaf : Leaf), leaf.format.Agrees
  | .prime order width => Format.through_agrees (Format.number_agrees order width)
  | .extension order degree width =>
    Format.through_agrees
      (Format.each_agrees fun format member => by
        rw [List.eq_of_mem_replicate member]
        exact Format.through_agrees (Format.number_agrees order width))
  | .curve => Format.through_agrees pointFormat_agrees

/-! ## The format of a closed type -/

mutual
  /-- The format of a closed type, when the canonical layout writes its values. -/
  def formatOf (table : Table) : Closed → Option (Format Datum)
    | .bool => some (numbers (Format.below 2))
    | .nat => some (numbers Format.natural)
    | .index bound => some (numbers (Format.below bound))
    | .nonzero field =>
      match formatOf table field, elementOf table field with
      | some format, some element => some (format.refine fun value => !element.isZero value)
      | _, _ => none
    | .seq element (some size) =>
      match formatOf table element with
      | some format => some (sequences (format.repeated size))
      | none => none
    | .seq element none =>
      match formatOf table element with
      | some format => some (sequences (Format.counted Format.natural format))
      | none => none
    | .tuple components =>
      match formatsOf table components with
      | some formats => some (sequences (Format.each formats))
      | none => none
    | .row name =>
      match leafOf table name with
      | some leaf => some leaf.format
      | none => none

  /-- The formats of closed types, when the layout writes the values of each. -/
  def formatsOf (table : Table) : List Closed → Option (List (Format Datum))
    | [] => some []
    | component :: rest =>
      match formatOf table component, formatsOf table rest with
      | some format, some formats => some (format :: formats)
      | _, _ => none
end

mutual
  /-- Whether a closed type has a point of G1 in it. -/
  def containsPoint (table : Table) : Closed → Bool
    | .nonzero field => containsPoint table field
    | .seq element _ => containsPoint table element
    | .tuple components => anyContainsPoint table components
    | .row name =>
      match leafOf table name with
      | some .curve => true
      | _ => false
    | .bool | .nat | .index _ => false

  def anyContainsPoint (table : Table) : List Closed → Bool
    | [] => false
    | component :: rest => containsPoint table component || anyContainsPoint table rest
end

mutual
  /-- The laws of the format of a closed type: the round trip of a prefix, and that the reader
  accepts only what the writer writes. A type with a point of G1 in it takes the hypothesis of
  the compressed encoding; no other type takes a hypothesis. -/
  theorem formatOf_lawful (table : Table) : ∀ (type : Closed) {format : Format Datum},
      formatOf table type = some format →
        (containsPoint table type = true → PointCompression) → format.Lawful
    | .bool, format, built, _ => by
      simp only [formatOf, Option.some.injEq] at built
      subst built
      exact Format.through_lawful (Format.below_lawful 2) views_number
    | .nat, format, built, _ => by
      simp only [formatOf, Option.some.injEq] at built
      subst built
      exact Format.through_lawful Format.natural_lawful views_number
    | .index bound, format, built, _ => by
      simp only [formatOf, Option.some.injEq] at built
      subst built
      exact Format.through_lawful (Format.below_lawful bound) views_number
    | .nonzero field, format, built, compression => by
      simp only [formatOf] at built
      cases inner : formatOf table field with
      | none => simp [inner] at built
      | some innerFormat =>
        cases arithmetic : elementOf table field with
        | none => simp [inner, arithmetic] at built
        | some element =>
          simp only [inner, arithmetic, Option.some.injEq] at built
          subst built
          exact Format.refine_lawful
            (formatOf_lawful table field inner (by simpa [containsPoint] using compression)) _
    | .seq element (some size), format, built, compression => by
      simp only [formatOf] at built
      cases inner : formatOf table element with
      | none => simp [inner] at built
      | some innerFormat =>
        simp only [inner, Option.some.injEq] at built
        subst built
        exact Format.through_lawful
          (Format.repeated_lawful size
            (formatOf_lawful table element inner (by simpa [containsPoint] using compression)))
          views_sequence
    | .seq element none, format, built, compression => by
      simp only [formatOf] at built
      cases inner : formatOf table element with
      | none => simp [inner] at built
      | some innerFormat =>
        simp only [inner, Option.some.injEq] at built
        subst built
        exact Format.through_lawful
          (Format.counted_lawful Format.natural_lawful
            (formatOf_lawful table element inner (by simpa [containsPoint] using compression)))
          views_sequence
    | .tuple components, format, built, compression => by
      simp only [formatOf] at built
      cases inner : formatsOf table components with
      | none => simp [inner] at built
      | some formats =>
        simp only [inner, Option.some.injEq] at built
        subst built
        exact Format.through_lawful
          (Format.each_lawful
            (formatsOf_lawful table components inner (by simpa [containsPoint] using compression)))
          views_sequence
    | .row name, format, built, compression => by
      simp only [formatOf] at built
      cases found : leafOf table name with
      | none => simp [found] at built
      | some leaf =>
        simp only [found, Option.some.injEq] at built
        subst built
        exact leaf.format_lawful fun isCurve =>
          compression (by simp [containsPoint, found, isCurve])

  theorem formatsOf_lawful (table : Table) : ∀ (types : List Closed) {formats : List (Format Datum)},
      formatsOf table types = some formats →
        (anyContainsPoint table types = true → PointCompression) →
          ∀ format ∈ formats, format.Lawful
    | [], formats, built, _ => by
      simp only [formatsOf, Option.some.injEq] at built
      subst built
      intro format member
      cases member
    | component :: rest, formats, built, compression => by
      simp only [formatsOf] at built
      cases first : formatOf table component with
      | none => simp [first] at built
      | some firstFormat =>
        cases others : formatsOf table rest with
        | none => simp [first, others] at built
        | some otherFormats =>
          simp only [first, others, Option.some.injEq] at built
          subst built
          intro format member
          rcases List.mem_cons.mp member with rfl | later
          · exact formatOf_lawful table component first fun has =>
              compression (by simp [anyContainsPoint, has])
          · exact formatsOf_lawful table rest others
              (fun has => compression (by simp [anyContainsPoint, has])) format later
end

/-- The laws of the format of a closed type without a point of G1 in it, without a
hypothesis. -/
theorem formatOf_lawful_of_no_point (table : Table) {type : Closed} {format : Format Datum}
    (built : formatOf table type = some format) (none : containsPoint table type = false) :
    format.Lawful :=
  formatOf_lawful table type built fun has => by rw [none] at has; cases has

mutual
  /-- The reader under a limit of the format of a closed type agrees with its reader whenever it
  answers. -/
  theorem formatOf_agrees (table : Table) : ∀ (type : Closed) {format : Format Datum},
      formatOf table type = some format → format.Agrees
    | .bool, format, built => by
      simp only [formatOf, Option.some.injEq] at built
      subst built
      exact Format.through_agrees (Format.below_agrees 2)
    | .nat, format, built => by
      simp only [formatOf, Option.some.injEq] at built
      subst built
      exact Format.through_agrees Format.natural_agrees
    | .index bound, format, built => by
      simp only [formatOf, Option.some.injEq] at built
      subst built
      exact Format.through_agrees (Format.below_agrees bound)
    | .nonzero field, format, built => by
      simp only [formatOf] at built
      cases inner : formatOf table field with
      | none => simp [inner] at built
      | some innerFormat =>
        cases arithmetic : elementOf table field with
        | none => simp [inner, arithmetic] at built
        | some element =>
          simp only [inner, arithmetic, Option.some.injEq] at built
          subst built
          exact Format.refine_agrees (formatOf_agrees table field inner) _
    | .seq element (some size), format, built => by
      simp only [formatOf] at built
      cases inner : formatOf table element with
      | none => simp [inner] at built
      | some innerFormat =>
        simp only [inner, Option.some.injEq] at built
        subst built
        exact Format.through_agrees
          (Format.repeated_agrees size (formatOf_agrees table element inner))
    | .seq element none, format, built => by
      simp only [formatOf] at built
      cases inner : formatOf table element with
      | none => simp [inner] at built
      | some innerFormat =>
        simp only [inner, Option.some.injEq] at built
        subst built
        exact Format.through_agrees
          (Format.counted_agrees Format.natural_agrees (formatOf_agrees table element inner))
    | .tuple components, format, built => by
      simp only [formatOf] at built
      cases inner : formatsOf table components with
      | none => simp [inner] at built
      | some formats =>
        simp only [inner, Option.some.injEq] at built
        subst built
        exact Format.through_agrees (Format.each_agrees (formatsOf_agrees table components inner))
    | .row name, format, built => by
      simp only [formatOf] at built
      cases found : leafOf table name with
      | none => simp [found] at built
      | some leaf =>
        simp only [found, Option.some.injEq] at built
        subst built
        exact leaf.format_agrees

  theorem formatsOf_agrees (table : Table) : ∀ (types : List Closed) {formats : List (Format Datum)},
      formatsOf table types = some formats → ∀ format ∈ formats, format.Agrees
    | [], formats, built => by
      simp only [formatsOf, Option.some.injEq] at built
      subst built
      intro format member
      cases member
    | component :: rest, formats, built => by
      simp only [formatsOf] at built
      cases first : formatOf table component with
      | none => simp [first] at built
      | some firstFormat =>
        cases others : formatsOf table rest with
        | none => simp [first, others] at built
        | some otherFormats =>
          simp only [first, others, Option.some.injEq] at built
          subst built
          intro format member
          rcases List.mem_cons.mp member with rfl | later
          · exact formatOf_agrees table component first
          · exact formatsOf_agrees table rest others format later
end

/-! ## A value of a type -/

mutual
  /-- A value of a type: zero, the field's one for `nonzero<F>`, the point at infinity, and the
  collections and tuples of these. A type without a value has none; the datum is then not of
  the domain of its format. -/
  def defaultValue (table : Table) : Closed → Datum
    | .nonzero field =>
      match elementOf table field with
      | some element => element.ofNat 1
      | none => .number 1
    | .seq element (some size) => .sequence (List.replicate size (defaultValue table element))
    | .seq _ none => .sequence []
    | .tuple components => .sequence (defaultValues table components)
    | .row name =>
      match elementOf table (.row name) with
      | some element => element.zero
      | none => .number 0
    | .bool | .nat | .index _ => .number 0

  def defaultValues (table : Table) : List Closed → List Datum
    | [] => []
    | component :: rest => defaultValue table component :: defaultValues table rest
end

mutual
  /-- The number of elements of collections in the value of a type that `defaultValue` gives:
  every value of the type has at least as many. -/
  def defaultElements : Closed → Nat
    | .nonzero _ | .seq _ none | .row _ | .bool | .nat | .index _ => 0
    | .seq element (some size) => size * (1 + defaultElements element)
    | .tuple components => allDefaultElements components

  def allDefaultElements : List Closed → Nat
    | [] => 0
    | component :: rest => defaultElements component + allDefaultElements rest
end

end Zkc.Core.Vocabulary
