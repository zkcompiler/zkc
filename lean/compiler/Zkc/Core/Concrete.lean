module

public import Zkc.Core.Meaning

public section

/-! Concrete data: one carrier of plain data, field and group arithmetic, a hash.

Every nominal type has the carrier `Datum`: a number, or a sequence of data. A typed value is
a datum, and a datum is a value of a type when it has the type's shape (`toDatum`,
`ofDatum`). The executor's models compute on this carrier.

What is fixed here:

- the scalar field of BLS12-381 and its group G1, in affine coordinates on
  `y² = x³ + 4` over the base field;
- SHA-256 (FIPS 180-4): the proof identity, the row `hash.sha256` and the sampler of a run;
- bytes as numbers, in hexadecimal and as big-endian numbers.
-/

set_option autoImplicit false

namespace Zkc.Core.Concrete

open Zkc.Source

/-! ## SHA-256 -/

namespace Sha256

def roundConstants : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

def initialState : Array UInt32 := #[
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

def rotateRight (word : UInt32) (count : UInt32) : UInt32 :=
  (word >>> count) ||| (word <<< (32 - count))

/-- The message with its padding: a one bit, zeros, and the bit length in 64 bits. -/
def padded (message : ByteArray) : ByteArray := Id.run do
  let mut out := message.push 0x80
  while out.size % 64 != 56 do
    out := out.push 0
  let bits := message.size * 8
  for index in [0:8] do
    out := out.push (UInt8.ofNat ((bits >>> (8 * (7 - index))) % 256))
  return out

def compress (state : Array UInt32) (block : ByteArray) (offset : Nat) : Array UInt32 := Id.run do
  let mut schedule : Array UInt32 := Array.replicate 64 0
  for index in [0:16] do
    let word := (block[offset + 4 * index]!.toUInt32 <<< 24) |||
      (block[offset + 4 * index + 1]!.toUInt32 <<< 16) |||
      (block[offset + 4 * index + 2]!.toUInt32 <<< 8) ||| block[offset + 4 * index + 3]!.toUInt32
    schedule := schedule.set! index word
  for index in [16:64] do
    let early := schedule[index - 15]!
    let late := schedule[index - 2]!
    let small := rotateRight early 7 ^^^ rotateRight early 18 ^^^ (early >>> 3)
    let large := rotateRight late 17 ^^^ rotateRight late 19 ^^^ (late >>> 10)
    schedule := schedule.set! index (schedule[index - 16]! + small + schedule[index - 7]! + large)
  let mut a := state[0]!
  let mut b := state[1]!
  let mut c := state[2]!
  let mut d := state[3]!
  let mut e := state[4]!
  let mut f := state[5]!
  let mut g := state[6]!
  let mut h := state[7]!
  for index in [0:64] do
    let sum1 := rotateRight e 6 ^^^ rotateRight e 11 ^^^ rotateRight e 25
    let choice := (e &&& f) ^^^ ((~~~e) &&& g)
    let first := h + sum1 + choice + roundConstants[index]! + schedule[index]!
    let sum0 := rotateRight a 2 ^^^ rotateRight a 13 ^^^ rotateRight a 22
    let majority := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let second := sum0 + majority
    h := g
    g := f
    f := e
    e := d + first
    d := c
    c := b
    b := a
    a := first + second
  return #[state[0]! + a, state[1]! + b, state[2]! + c, state[3]! + d, state[4]! + e,
    state[5]! + f, state[6]! + g, state[7]! + h]

/-- The digest of a message: 32 bytes. -/
def digest (message : ByteArray) : ByteArray := Id.run do
  let block := padded message
  let mut state := initialState
  for index in [0:block.size / 64] do
    state := compress state block (64 * index)
  let mut out := ByteArray.empty
  for word in state do
    out := out.push (word >>> 24).toUInt8
    out := out.push (word >>> 16).toUInt8
    out := out.push (word >>> 8).toUInt8
    out := out.push word.toUInt8
  return out

end Sha256

/-- Bytes as numbers. -/
def bytesOf (data : ByteArray) : List Nat := data.toList.map (·.toNat)

def byteArrayOf (bytes : List Nat) : ByteArray := ⟨(bytes.map UInt8.ofNat).toArray⟩

/-- The SHA-256 digest of bytes given as numbers. -/
def hash (bytes : List Nat) : List Nat := bytesOf (Sha256.digest (byteArrayOf bytes))

def hexDigit (value : Nat) : Char := "0123456789abcdef".toList.getD value '0'

/-- Bytes in hexadecimal. -/
def hex (bytes : List Nat) : String :=
  String.ofList (bytes.flatMap fun byte => [hexDigit (byte / 16), hexDigit (byte % 16)])

/-- The number with the given big-endian bytes. -/
def numberOf (bytes : List Nat) : Nat := bytes.foldl (fun value byte => value * 256 + byte) 0

/-- The big-endian bytes of a number, in a given width. -/
def bigEndian (width value : Nat) : List Nat :=
  (List.range width).map fun index => (value >>> (8 * (width - 1 - index))) % 256

/-! ## The field and the group -/

/-- The order of the scalar field of BLS12-381. -/
def scalarModulus : Nat := 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001

/-- The characteristic of the base field of BLS12-381. -/
def baseModulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

/-- `base ^ exponent` modulo `modulus`, by squaring. -/
def powerModulo (base exponent modulus : Nat) : Nat := Id.run do
  let mut result := 1 % modulus
  let mut square := base % modulus
  let mut remaining := exponent
  for _ in [0:exponent.log2 + 1] do
    if remaining % 2 == 1 then result := result * square % modulus
    square := square * square % modulus
    remaining := remaining / 2
  return result

/-- The inverse in a prime field; zero for zero. -/
def inverseModulo (value modulus : Nat) : Nat := powerModulo value (modulus - 2) modulus

/-- A point of G1 in affine coordinates; `none` is the point at infinity. -/
abbrev Point := Option (Nat × Nat)

def onCurve : Point → Bool
  | none => true
  | some (x, y) =>
      x < baseModulus && y < baseModulus &&
        y * y % baseModulus == (x * x % baseModulus * x + 4) % baseModulus

def addPoints : Point → Point → Point
  | none, other => other
  | first, none => first
  | some (x1, y1), some (x2, y2) =>
      let p := baseModulus
      if x1 == x2 && (y1 + y2) % p == 0 then none
      else
        let slope := if x1 == x2 then 3 * x1 % p * x1 % p * inverseModulo (2 * y1) p % p
          else (y2 + p - y1) % p * inverseModulo ((x2 + p - x1) % p) p % p
        let x3 := (slope * slope + 2 * p - x1 - x2) % p
        some (x3, (slope * ((x1 + p - x3) % p) + p - y1) % p)

/-- A multiple of a point, by doubling. -/
def scalePoint (point : Point) (scalar : Nat) : Point := Id.run do
  let mut result : Point := none
  let mut doubled := point
  let mut remaining := scalar
  for _ in [0:scalar.log2 + 1] do
    if remaining % 2 == 1 then result := addPoints result doubled
    doubled := addPoints doubled doubled
    remaining := remaining / 2
  return result

/-- The generator of G1. -/
def generator : Point := some
  (0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1)

/-- The order of the group, as a number. -/
theorem scalarModulus_eq :
    scalarModulus =
      52435875175126190479447740508185965837690552500527637822603658699938581184513 := by
  decide

/-- Every multiple of the point at infinity is the point at infinity. -/
theorem scalePoint_infinity (scalar : Nat) : scalePoint none scalar = none := by
  unfold scalePoint
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Id.run]
  generalize List.range' _ _ _ = steps
  generalize scalar = remaining
  induction steps generalizing remaining with
  | nil => rfl
  | cons step rest ih =>
    simp only [List.forIn_cons]
    split
    · exact ih _
    · exact ih _

/-- The point at infinity is on the curve, and the order of the group times it is itself. -/
theorem infinity_ofGroup : (onCurve none && scalePoint none scalarModulus == none) = true := by
  rw [scalePoint_infinity]
  rfl

/-! ## Data -/

-- The instances that the type of data derives are exposed: a module that reads the default
-- datum evaluates it.
@[expose] section

/-- A value of any nominal type: a number, or a sequence of data. -/
inductive Datum where
  | number (value : Nat)
  | sequence (items : List Datum)
  deriving Inhabited, Repr

namespace Datum

mutual
  /-- Two data are the same datum. It is written by structural recursion so that the kernel
  reduces it; the function that `deriving BEq` gives for a nested type does not reduce there. -/
  def same : Datum → Datum → Bool
    | .number first, .number second => first == second
    | .sequence first, .sequence second => sameItems first second
    | _, _ => false

  def sameItems : List Datum → List Datum → Bool
    | [], [] => true
    | first :: rest, second :: others => same first second && sameItems rest others
    | _, _ => false
end

mutual
  theorem same_eq : ∀ (first second : Datum), same first second = true → first = second
    | .number _, .number _, equal => by
        simp only [same, beq_iff_eq] at equal
        rw [equal]
    | .sequence first, .sequence second, equal => by
        simp only [same] at equal
        rw [sameItems_eq first second equal]
    | .number _, .sequence _, equal => by simp [same] at equal
    | .sequence _, .number _, equal => by simp [same] at equal

  theorem sameItems_eq :
      ∀ (first second : List Datum), sameItems first second = true → first = second
    | [], [], _ => rfl
    | first :: rest, second :: others, equal => by
        simp only [sameItems, Bool.and_eq_true] at equal
        rw [same_eq first second equal.1, sameItems_eq rest others equal.2]
    | [], _ :: _, equal => by simp [sameItems] at equal
    | _ :: _, [], equal => by simp [sameItems] at equal
end

mutual
  theorem same_self : ∀ (datum : Datum), same datum datum = true
    | .number _ => by simp [same]
    | .sequence items => by simp only [same]; exact sameItems_self items

  theorem sameItems_self : ∀ (items : List Datum), sameItems items items = true
    | [] => rfl
    | first :: rest => by
        simp only [sameItems, same_self first, sameItems_self rest, Bool.and_self]
end

/-- Equality of data is decided by `same`, in the kernel as in compiled code. -/
instance : DecidableEq Datum := fun first second =>
  if equal : same first second = true then isTrue (same_eq first second equal)
  else isFalse fun identical => equal (identical ▸ same_self first)

end Datum

end

namespace Datum

@[expose] def ofBool (value : Bool) : Datum := .number (if value then 1 else 0)

@[expose] def toBool : Datum → Bool
  | .number value => value != 0
  | .sequence _ => false

@[expose] def toNat : Datum → Nat
  | .number value => value
  | .sequence _ => 0

@[expose] def items : Datum → List Datum
  | .number _ => []
  | .sequence items => items

@[expose] def ofBytes (bytes : List Nat) : Datum := .sequence (bytes.map .number)

@[expose] def toBytes (datum : Datum) : List Nat := datum.items.map toNat

@[expose] def ofPoint : Point → Datum
  | none => .sequence []
  | some (x, y) => .sequence [.number x, .number y]

@[expose] def toPoint : Datum → Point
  | .sequence [.number x, .number y] => some (x, y)
  | _ => none

end Datum

/-- A number as an element of the scalar field: its residue. -/
def field (value : Nat) : Datum := .number (value % scalarModulus)

/-- The one carrier of every nominal type. -/
abbrev Carrier : Nat → Type := fun _ => Datum

abbrev Value : Ty → Type := Ty.Value Carrier

mutual
  /-- A typed value as a datum: a sequence, a tuple or a record as the sequence of the data
  of its elements, components or fields; a variant as the sequence of the position of its
  alternative and the datum of its payload. -/
  @[expose] def toDatum : (type : Ty) → Value type → Datum
    | .bool, value => Datum.ofBool value
    | .nat, value => .number value
    | .fin _, value => .number value.val
    | .nominal _, value => value
    | .seq element none, values => .sequence (values.map (toDatum element))
    | .seq element (some _), values => .sequence (values.val.map (toDatum element))
    | .tuple components, values => .sequence (tupleData components values)
    | .record _ _ fields, values => .sequence (tupleData fields values)
    | .variant _ alternatives, value => variantDatum alternatives 0 value

  /-- The data of the components of a tuple. -/
  def tupleData : (components : List Ty) → Ty.Tuple Carrier components → List Datum
    | [], _ => []
    | component :: rest, values => toDatum component values.1 :: tupleData rest values.2

  /-- The datum of a value of a variant whose first alternative has position `position`. -/
  def variantDatum : (alternatives : List Ty) → Nat → Ty.Variant Carrier alternatives → Datum
    | [], _, value => nomatch value
    | alternative :: _, position, .inl payload =>
        .sequence [.number position, toDatum alternative payload]
    | _ :: rest, position, .inr value => variantDatum rest (position + 1) value
end

mutual
  /-- A datum as a value of a type, when it is one: a number below the bound of a `fin`
  type; a sequence of data of the element type, of the size of a sized sequence; a
  sequence of data of the components of a tuple or of the fields of a record; the position
  of an alternative of a variant and a datum of its payload. -/
  def ofDatum : (type : Ty) → Datum → Option (Value type)
    | .bool, datum => some datum.toBool
    | .nat, datum => some datum.toNat
    | .fin bound, datum =>
        if below : datum.toNat < bound then some ⟨datum.toNat, below⟩ else none
    | .nominal _, datum => some datum
    | .seq element none, .sequence items => items.mapM (ofDatum element)
    | .seq element (some size), .sequence items =>
        match items.mapM (ofDatum element) with
        | some values => if same : values.length = size then some ⟨values, same⟩ else none
        | none => none
    | .tuple components, .sequence items => tupleOf components items
    | .record _ _ fields, .sequence items => tupleOf fields items
    | .variant _ alternatives, .sequence [.number position, item] =>
        variantOf alternatives position item
    | .seq .., .number _ | .tuple _, .number _ | .record .., .number _ | .variant .., _ => none

  /-- The components of a tuple from one datum each. -/
  def tupleOf : (components : List Ty) → List Datum → Option (Ty.Tuple Carrier components)
    | [], [] => some PUnit.unit
    | component :: rest, item :: items =>
        match ofDatum component item, tupleOf rest items with
        | some value, some values => some (value, values)
        | _, _ => none
    | [], _ :: _ | _ :: _, [] => none

  /-- The alternative at a position, with its payload from a datum. -/
  def variantOf : (alternatives : List Ty) → Nat → Datum → Option (Ty.Variant Carrier alternatives)
    | [], _, _ => none
    | alternative :: _, 0, item => (ofDatum alternative item).map .inl
    | _ :: rest, position + 1, item => (variantOf rest position item).map .inr
end

/-- Typed values as data, in order. -/
@[expose] def toData : (types : List Ty) → Values Value types → List Datum
  | [], _ => []
  | type :: rest, values => toDatum type (values.get .here) :: toData rest values.tail

/-- Data as typed values, when each datum is a value of its type; a missing datum is the
default one. -/
def ofData : (types : List Ty) → List Datum → Option (Values Value types)
  | [], _ => some .nil
  | type :: rest, data =>
      match ofDatum type (data.headD default), ofData rest data.tail with
      | some value, some values => some (.cons value values)
      | _, _ => none

/-- The data of one typed value. -/
theorem toData_one (type : Ty) (values : Values Value [type]) :
    toData [type] values = [toDatum type (values.get .here)] := by rfl

/-- One datum is a value of a nominal type. -/
theorem ofData_nominal (row : Nat) (datum : Datum) :
    ofData [.nominal row] [datum] = some (.cons datum .nil) := by rfl

/-- One datum as a `bool`. -/
theorem ofData_bool (datum : Datum) :
    ofData [.bool] [datum] = some (.cons datum.toBool .nil) := by rfl

theorem Datum.toBool_ofBool (value : Bool) : (Datum.ofBool value).toBool = value := by
  cases value <;> rfl

/-- The data of typed values: the datum of the first, and the data of the others. -/
theorem toData_cons (type : Ty) (rest : List Ty) (values : Values Value (type :: rest)) :
    toData (type :: rest) values = toDatum type (values.get .here) :: toData rest values.tail := by
  rfl

theorem toData_nil (values : Values Value []) : toData [] values = [] := by rfl

/-- The datum of a `bool`. -/
theorem toDatum_bool (value : Bool) : toDatum .bool value = Datum.ofBool value := by rfl

/-- The datum of an index: its number. -/
theorem toDatum_fin (bound : Nat) (value : Fin bound) :
    toDatum (.fin bound) value = .number value.val := by rfl

/-- The datum of bytes: the sequence of their numbers. -/
theorem toDatum_bytes (bytes : List (Fin 256)) :
    toDatum (.seq (.fin 256) none) bytes = .sequence (bytes.map fun byte => .number byte.val) := by
  simp only [toDatum]

mutual
  /-- A typed value is read back from its datum. -/
  theorem ofDatum_toDatum : ∀ (type : Ty) (value : Value type),
      ofDatum type (toDatum type value) = some value
    | .bool, value => by simp [ofDatum, toDatum, Datum.toBool_ofBool]
    | .nat, _ => rfl
    | .fin _, value => by simp [ofDatum, toDatum, Datum.toNat, value.isLt]
    | .nominal _, _ => rfl
    | .seq element none, values => by
      simp only [toDatum, ofDatum]
      induction values with
      | nil => rfl
      | cons value rest hypothesis =>
        simp only [List.map_cons, List.mapM_cons, ofDatum_toDatum element value, hypothesis]
        rfl
    | .seq element (some size), ⟨values, same⟩ => by
      have read : (values.map (toDatum element)).mapM (ofDatum element) = some values := by
        clear same
        induction values with
        | nil => rfl
        | cons value rest hypothesis =>
          simp only [List.map_cons, List.mapM_cons, ofDatum_toDatum element value, hypothesis]
          rfl
      simp only [toDatum, ofDatum, read, same, ↓reduceDIte]
    | .tuple components, values => by
      simp only [toDatum, ofDatum]
      exact tupleOf_tupleData components values
    | .record _ _ fields, values => by
      simp only [toDatum, ofDatum]
      exact tupleOf_tupleData fields values
    | .variant _ alternatives, value => by
      obtain ⟨position, item, written, read⟩ := variantOf_variantDatum alternatives 0 value
      simp only [toDatum, written, ofDatum, Nat.zero_add]
      exact read

  /-- The components of a tuple are read back from their data. -/
  theorem tupleOf_tupleData : ∀ (components : List Ty) (values : Ty.Tuple Carrier components),
      tupleOf components (tupleData components values) = some values
    | [], _ => rfl
    | component :: rest, (value, values) => by
      simp only [tupleData, tupleOf, ofDatum_toDatum component value, tupleOf_tupleData rest values]

  /-- The datum of a value of a variant is the position of its alternative, counted from the
  position of the first one, and the datum of its payload, from which the value is read back. -/
  theorem variantOf_variantDatum : ∀ (alternatives : List Ty) (first : Nat)
      (value : Ty.Variant Carrier alternatives),
      ∃ position item, variantDatum alternatives first value =
          .sequence [.number (first + position), item] ∧
        variantOf alternatives position item = some value
    | [], _, value => nomatch value
    | alternative :: _, first, .inl payload =>
      ⟨0, toDatum alternative payload, by simp [variantDatum],
        by simp [variantOf, ofDatum_toDatum alternative payload]⟩
    | _ :: rest, first, .inr value => by
      obtain ⟨position, item, written, read⟩ := variantOf_variantDatum rest (first + 1) value
      exact ⟨position + 1, item, by simp only [variantDatum, written]; congr 3; omega,
        by simp [variantOf, read]⟩
end

/-- Typed values are read back from their data. -/
theorem ofData_toData : ∀ (types : List Ty) (values : Values Value types),
    ofData types (toData types values) = some values
  | [], .nil => rfl
  | type :: rest, .cons value values => by
    simp only [toData, ofData, List.headD_cons, List.tail_cons, Values.get_here, Values.tail,
      ofDatum_toDatum type value, ofData_toData rest values]

/-- Checks of the constants: the digest of `abc`, the generator on the curve, and the
group's order. -/
def selfTest (_ : Unit) : List (String × Bool) :=
  [("SHA-256 of abc",
      hex (hash [97, 98, 99]) == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
   ("SHA-256 of the empty message",
      hex (hash []) == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
   ("the generator is on the curve", onCurve generator && generator.isSome),
   ("the order of the generator divides the scalar modulus",
      scalePoint generator scalarModulus == none),
   ("2G + 3G = 5G",
      addPoints (scalePoint generator 2) (scalePoint generator 3) == scalePoint generator 5)]

end Zkc.Core.Concrete
