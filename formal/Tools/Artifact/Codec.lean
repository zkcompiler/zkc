import Tools.Interactive.Decode
import Tools.Interactive.OracleReference
import Tools.Interactive.ScalarReference
import Tools.Interactive.ExtensionReference
import Zkc.Realization.ByteEncoding

/-! Independent executable encoding for artifact observations. Curve subgroup
validity and PCS equations are external public-primitive obligations; scalar,
length, tag and cursor checks here do not delegate to the native decoder. -/

set_option autoImplicit false

namespace Tools.Artifact
open Lean (Json)
open Tools.Interactive

def byteLimit : Nat := 16777216

def little (width value : Nat) : ByteArray :=
  ByteArray.mk ((Zkc.Realization.ByteEncoding.little width value).map
    (fun b => UInt8.ofNat b.val)).toArray

def valueLE (bytes : ByteArray) : Nat :=
  bytes.toList.foldr (fun b n => b.toNat + 256 * n) 0

def hex (bytes : ByteArray) : String :=
  String.ofList (bytes.toList.flatMap fun b =>
    let digits := "0123456789abcdef".toList.toArray
    [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

def unhex (s : String) : Result ByteArray := do
  ensure (s.utf8ByteSize ≤ 2 * byteLimit && s.utf8ByteSize % 2 == 0) "hex-length"
  let digit (c : Char) : Result Nat :=
    if '0' ≤ c && c ≤ '9' then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error "noncanonical-hex"
  let chars := s.toList.toArray
  let mut out := ByteArray.empty
  for i in [:chars.size / 2] do
    let hi ← digit chars[2*i]!
    let lo ← digit chars[2*i+1]!
    out := out.push (UInt8.ofNat (16*hi+lo))
  return out

/-- Only strings and arrays have an identity encoding. JSON textual spelling,
objects, numbers and implicit Unicode normalization are excluded. -/
def encodeTree : Nat → Json → Result ByteArray
  | 0, _ => .error "identity-depth"
  | _ + 1, .str s => do
      let b := s.toUTF8
      ensure (b.size ≤ byteLimit) "identity-bytes"
      return (ByteArray.mk #[0]) ++ little 8 b.size ++ b
  | fuel + 1, .arr xs => do
      ensure (xs.size ≤ 32768) "identity-items"
      let mut result := (ByteArray.mk #[1]) ++ little 8 xs.size
      for x in xs do
        let part ← encodeTree fuel x
        ensure (result.size + part.size ≤ byteLimit) "identity-bytes"
        result := result ++ part
      return result
  | _ + 1, _ => .error "identity-kind"

private def countTree : Nat → Json → Result Nat
  | 0, _ => .error "identity-depth"
  | _ + 1, .str _ => .ok 1
  | fuel + 1, .arr xs => do
      ensure (xs.size ≤ 32768) "identity-items"
      let mut count := 1
      for x in xs do
        count := count + (← countTree fuel x)
        ensure (count ≤ 200000) "identity-nodes"
      return count
  | _ + 1, _ => .error "identity-kind"

def treeBytes (j : Json) : Result ByteArray := do
  let _ ← countTree 65 j
  encodeTree 65 j

def fieldBytes (f : Math.Fr) : ByteArray := little 32 f.val

def fieldFromBytes (b : ByteArray) : Result Math.Fr := do
  ensure (b.size == 32) "field-width"
  let n := valueLE b
  ensure (n < fieldModulus) "noncanonical-field"
  return (n : Math.Fr)

inductive Value where
  | oracle (value : OracleReference.Data)
  | extension (value : ExtensionReference.Data)
  | arithmetic (domain : ScalarReference.Domain) (value : ScalarReference.Data (ScalarReference.Scalar domain))
  | nominalBytes (identity kind : String) (bytes : ByteArray)
  | field (value : Math.Fr)
  | table (value : Math.Table)
  | point (value : List Math.Fr)
  | round (value : Math.Round Math.Fr)
  | boolean (value : Bool)
  | publicBytes (ty : Ty) (bytes : ByteArray)
  | verifierKey (bytes : ByteArray)
  | selectedRng (generation : Nat)
  | ristrettoRng (generation : Nat)
  | extensionRng (generation : Nat)

def Value.ty : Value → Ty
  | .oracle value => value.kind
  | .extension value => value.kind
  | .arithmetic _ value => value.kind
  | .nominalBytes _ kind _ => kind
  | .field _ => "field" | .table _ => "table" | .point _ => "point"
  | .round _ => "round" | .boolean _ => "bool" | .publicBytes ty _ => ty
  | .verifierKey _ => "verifier_key" | .selectedRng _ | .ristrettoRng _ | .extensionRng _ => "rng"

def tag (ty : Ty) : Result UInt8 := do
  match ty with
  | "field" => return 1 | "table" => return 2 | "point" => return 3
  | "round" => return 4 | "bool" => return 5 | "commitment" => return 6
  | "proof" => return 7 | "group" => return 9 | "groups" => return 10
  | _ => throw "nonserializable"

def magic : ByteArray := ByteArray.mk #[90, 75, 67, 86, 1]

def fieldsBytes (values : List Math.Fr) : ByteArray :=
  values.foldl (fun b f => b ++ fieldBytes f) ByteArray.empty

def arithmeticTag (domain : ScalarReference.Domain) (kind : String) : Result UInt8 :=
  match domain, kind with
  | .bn254, "field" => .ok 40 | .bn254, "vector" => .ok 41
  | .bn254, "polynomial" => .ok 42 | .bn254, "round" => .ok 43
  | .bn254, "matrix" => .ok 45
  | .bls, "field" => .ok 1 | .bls, "round" => .ok 4
  | .bls, "vector" => .ok 11 | .bls, "polynomial" => .ok 12
  | .ristretto, "field" => .ok 13 | .ristretto, "vector" => .ok 14
  | .ristretto, "polynomial" => .ok 15 | .ristretto, "round" => .ok 18
  | .koalaBear, "field" => .ok 19 | .koalaBear, "vector" => .ok 20
  | .koalaBear, "polynomial" => .ok 21 | .koalaBear, "round" => .ok 22
  | .bls, "matrix" => .ok 23 | .ristretto, "matrix" => .ok 24 | .koalaBear, "matrix" => .ok 25
  | _, "index" => .ok 31 | _, "indices" => .ok 32
  | _, "bool" => .ok 5
  | _, _ => .error "nonserializable"

def arithmeticWidth : ScalarReference.Domain → Nat
  | .koalaBear => 4
  | .bls | .ristretto | .bn254 => 32

def arithmeticWire (domain : ScalarReference.Domain)
    (value : ScalarReference.Data (ScalarReference.Scalar domain)) : Result ByteArray := do
  ensure value.valid "polynomial-or-vector-shape"
  let header := magic.push (← arithmeticTag domain value.kind)
  let width := arithmeticWidth domain
  let scalar := fun (x : ScalarReference.Scalar domain) => little width x.val
  let sequence := fun xs => xs.foldl (fun bytes x => bytes ++ scalar x) ByteArray.empty
  let size := match value with
    | .index _ => 14 | .indices ns => 10 + 8 * ns.length
    | .matrix m => 18 + (8 + width) * m.entries.length
    | .vector xs | .polynomial xs => 10 + width * xs.length
    | .round _ => 6 + 3 * width
    | .field _ => 6 + width
    | .boolean _ => 7
  ensure (size ≤ byteLimit) "wire-limit"
  return match value with
    | .index n => header ++ little 8 n
    | .indices ns => header ++ little 4 ns.length ++ ns.foldl (fun b n => b ++ little 8 n) ByteArray.empty
    | .matrix m => header ++ little 4 m.rows ++ little 4 m.columns ++ little 4 m.entries.length ++
        m.entries.foldl (fun bytes e => bytes ++ little 4 e.row ++ little 4 e.column ++ scalar e.coefficient) ByteArray.empty
    | .field x => header ++ scalar x
    | .vector xs | .polynomial xs => header ++ little 4 xs.length ++ sequence xs
    | .round r => header ++ sequence [r.constant, r.linear, r.quadratic]
    | .boolean b => header.push (if b then 1 else 0)

def decodeArithmeticWire (domain : ScalarReference.Domain) (kind : String)
    (bytes : ByteArray) : Result (ScalarReference.Data (ScalarReference.Scalar domain)) := do
  ensure (bytes.size ≤ byteLimit) "wire-limit"
  let tag ← arithmeticTag domain kind
  ensure (bytes.size ≥ 6 && bytes.extract 0 5 == magic && bytes[5]! == tag) "wire-header"
  let width := arithmeticWidth domain
  let scalar := fun (bytes : ByteArray) => do
    ensure (bytes.size == width) "field-width"
    let n := valueLE bytes
    ensure (n < domain.modulus) "noncanonical-field"
    pure (n : ScalarReference.Scalar domain)
  let payload := bytes.extract 6 bytes.size
  if kind == "index" then
    ensure (payload.size == 8) "index-length"
    return .index (valueLE payload)
  if kind == "indices" then
    ensure (payload.size ≥ 4) "indices-length"
    let count := valueLE (payload.extract 0 4)
    ensure (count ≤ Zkc.Algebra.FiniteVectors.limit && payload.size == 4 + 8 * count) "indices-length"
    return .indices ((List.range count).map fun i => valueLE (payload.extract (4 + 8*i) (12 + 8*i)))
  if kind == "field" then return .field (← scalar payload)
  if kind == "matrix" then
    ensure (payload.size ≥ 12) "wire-length"
    let rows := valueLE (payload.extract 0 4)
    let columns := valueLE (payload.extract 4 8)
    let nnz := valueLE (payload.extract 8 12)
    ensure (rows ≤ Zkc.Algebra.FiniteMatrices.dimensionLimit &&
      columns ≤ Zkc.Algebra.FiniteMatrices.dimensionLimit) "matrix-dimension-limit"
    ensure (nnz ≤ Zkc.Algebra.FiniteMatrices.nonzeroLimit && nnz ≤ rows * columns) "matrix-nonzero-limit"
    ensure (payload.size == 12 + (8 + width) * nnz) "wire-length"
    -- Independent validation pass before constructing a list of matrix entries.
    let readEntry := fun i => do
      let start := 12 + (8 + width) * i
      pure (Zkc.Algebra.FiniteMatrices.Entry.mk
        (valueLE (payload.extract start (start+4)))
        (valueLE (payload.extract (start+4) (start+8)))
        (← scalar (payload.extract (start+8) (start+8+width))))
    let mut previous : Option (Nat × Nat) := none
    for i in [:nnz] do
      let e ← readEntry i
      ensure (e.row < rows && e.column < columns && e.coefficient != 0) "matrix-canonical"
      if let some (r,c) := previous then
        ensure (r < e.row || (r == e.row && c < e.column)) "matrix-canonical"
      previous := some (e.row,e.column)
    let entries ← (List.range nnz).mapM readEntry
    return .matrix ⟨rows,columns,entries⟩
  let (count, start) ← if kind == "round" then pure (3, 0) else do
    ensure (payload.size ≥ 4) "wire-length"
    pure (valueLE (payload.extract 0 4), 4)
  ensure (count ≤ Zkc.Algebra.FiniteVectors.limit && payload.size == start + width * count) "scalar-vector-length"
  let xs ← (List.range count).mapM fun i => scalar (payload.extract (start + width*i) (start + width*(i+1)))
  if kind == "round" then
    let [a, b, c] := xs | throw "wire-round"
    return .round ⟨a, b, c⟩
  if kind == "vector" then return .vector xs
  if kind == "polynomial" then
    let value := ScalarReference.Data.polynomial xs
    ensure value.valid "polynomial-normalization"
    return value
  throw "unsupported-wire-type"

/-- Nominal octic extension codec; every scalar is eight canonical base u32s. -/
def extensionTag : String → Result UInt8
  | "field" => .ok 26 | "vector" => .ok 27 | "polynomial" => .ok 28
  | "index" => .ok 31 | "indices" => .ok 32
  | "round" => .ok 29 | "matrix" => .ok 30 | "bool" => .ok 5
  | _ => .error "nonserializable"

def extensionBytes (x : ExtensionReference.Scalar) : ByteArray :=
  x.coordinates.toArray.foldl (fun bytes c => bytes ++ little 4 c.val) ByteArray.empty

def extensionWire (value : ExtensionReference.Data) : Result ByteArray := do
  ensure value.valid "polynomial-or-vector-shape"
  let header := magic.push (← extensionTag value.kind)
  let sequence := fun xs => xs.foldl (fun bytes x => bytes ++ extensionBytes x) ByteArray.empty
  let size := match value with
    | .index _ => 14 | .indices ns => 10 + 8 * ns.length
    | .matrix m => 18 + 40 * m.entries.length
    | .vector xs | .polynomial xs => 10 + 32 * xs.length
    | .round _ => 102 | .field _ => 38 | .boolean _ => 7
  ensure (size ≤ byteLimit) "wire-limit"
  return match value with
    | .index n => header ++ little 8 n
    | .indices ns => header ++ little 4 ns.length ++ ns.foldl (fun b n => b ++ little 8 n) ByteArray.empty
    | .field x => header ++ extensionBytes x
    | .matrix m => header ++ little 4 m.rows ++ little 4 m.columns ++ little 4 m.entries.length ++
        m.entries.foldl (fun bytes e => bytes ++ little 4 e.row ++ little 4 e.column ++ extensionBytes e.coefficient) ByteArray.empty
    | .vector xs | .polynomial xs => header ++ little 4 xs.length ++ sequence xs
    | .round r => header ++ sequence [r.constant, r.linear, r.quadratic]
    | .boolean b => header.push (if b then 1 else 0)

def decodeExtensionWire (kind : String) (bytes : ByteArray) : Result ExtensionReference.Data := do
  ensure (bytes.size ≤ byteLimit) "wire-limit"
  ensure (bytes.size ≥ 6 && bytes.extract 0 5 == magic && bytes[5]! == (← extensionTag kind)) "wire-header"
  let scalar := fun (start : Nat) =>
    Json.arr ((List.range 8).map fun i => Json.str (toString
      (valueLE (bytes.extract (start + 4*i) (start + 4*(i+1)))))).toArray
  let payload ← if kind == "index" then do
      ensure (bytes.size == 14) "wire-length"
      pure (Json.str (toString (valueLE (bytes.extract 6 14))))
    else if kind == "indices" then do
      ensure (bytes.size ≥ 10) "wire-length"
      let n := valueLE (bytes.extract 6 10)
      ensure (n ≤ Zkc.Algebra.FiniteVectors.limit && bytes.size == 10 + 8*n) "wire-length"
      pure (Json.arr ((List.range n).map fun i => Json.str (toString (valueLE (bytes.extract (10+8*i) (18+8*i))))).toArray)
    else if kind == "field" then do
      ensure (bytes.size == 38) "field-width"
      pure (scalar 6)
    else if kind == "matrix" then do
      ensure (bytes.size ≥ 18) "wire-length"
      let rows := valueLE (bytes.extract 6 10)
      let columns := valueLE (bytes.extract 10 14)
      let nnz := valueLE (bytes.extract 14 18)
      ensure (rows ≤ Zkc.Algebra.FiniteMatrices.dimensionLimit &&
        columns ≤ Zkc.Algebra.FiniteMatrices.dimensionLimit) "matrix-dimension-limit"
      ensure (nnz ≤ Zkc.Algebra.FiniteMatrices.nonzeroLimit && nnz ≤ rows * columns) "matrix-nonzero-limit"
      ensure (bytes.size == 18 + 40 * nnz) "wire-length"
      pure (Json.arr #[.str (toString rows), .str (toString columns), .arr ((List.range nnz).map fun i =>
        Json.arr #[.str (toString (valueLE (bytes.extract (18+40*i) (22+40*i)))),
          .str (toString (valueLE (bytes.extract (22+40*i) (26+40*i)))), scalar (26+40*i)]).toArray])
    else do
      ensure (["vector", "polynomial", "round"].contains kind) "unsupported-wire-type"
      let (count, start) ← if kind == "round" then pure (3, 6) else do
        ensure (bytes.size ≥ 10) "wire-length"
        pure (valueLE (bytes.extract 6 10), 10)
      ensure (count ≤ Zkc.Algebra.FiniteVectors.limit && bytes.size == start + 32 * count) "scalar-vector-length"
      pure (Json.arr ((List.range count).map fun i => scalar (start + 32*i)).toArray)
  ExtensionReference.decode kind payload

/-- Framing and bounded lengths only. Compressed-point canonicality, decoding
and subgroup membership are explicit trusted validation-service obligations. -/
def checkRistrettoWire (kind : String) (bytes : ByteArray) : Result Unit := do
  ensure (bytes.size ≤ byteLimit) "wire-limit"
  ensure (kind == "group" || kind == "groups") "group-kind"
  ensure (bytes.size ≥ 6 && bytes.extract 0 5 == magic &&
    bytes[5]! == (if kind == "group" then 16 else 17)) "wire-header"
  if kind == "group" then ensure (bytes.size == 38) "group-length"
  else
    ensure (bytes.size ≥ 10) "groups-length"
    let count := valueLE (bytes.extract 6 10)
    ensure (count ≤ 4096) "group-limit"
    ensure (bytes.size == 10 + 32 * count) "groups-length"

/-- Only framing is checked here. Canonical curve decoding and subgroup
membership remain obligations of the installed trusted public service. -/
def bn254GroupTag (identity kind : String) : Result UInt8 := do
  ensure (["group", "groups"].contains kind) "group-kind"
  if identity == Bindings.bn254G1 then return if kind == "group" then 46 else 47
  if identity == Bindings.bn254G2 then return if kind == "group" then 48 else 49
  throw "group-domain"

def checkBn254Wire (identity kind : String) (bytes : ByteArray) : Result Unit := do
  let tag ← bn254GroupTag identity kind
  ensure (bytes.size ≤ byteLimit) "wire-limit"
  ensure (bytes.size ≥ 6 && bytes.extract 0 5 == magic && bytes[5]! == tag) "wire-header"
  let width := if identity == Bindings.bn254G1 then 32 else 64
  if kind == "group" then ensure (bytes.size == 6 + width) "group-length"
  else
    ensure (bytes.size ≥ 10) "groups-length"
    let count := valueLE (bytes.extract 6 10)
    ensure (count ≤ 4096) "group-limit"
    ensure (bytes.size == 10 + width * count) "groups-length"

def Value.wire (v : Value) : Result ByteArray := do
  if let .oracle value := v then return ← value.wire
  if let .extension value := v then return ← extensionWire value
  if let .arithmetic d value := v then return ← arithmeticWire d value
  if let .nominalBytes identity kind bytes := v then
    if identity == Bindings.ristrettoGroup then checkRistrettoWire kind bytes
    else checkBn254Wire identity kind bytes
    return bytes
  let t ← tag v.ty
  let header := magic.push t
  match v with
  | .field f => return header ++ fieldBytes f
  | .table t => return header ++ little 4 t.rank ++ fieldsBytes t.cells
  | .point p => return header ++ little 4 p.length ++ fieldsBytes p
  | .round r => return header ++ fieldsBytes [r.constant, r.linear, r.quadratic]
  | .boolean b => return header.push (if b then 1 else 0)
  | .publicBytes _ bytes => return bytes
  | _ => throw "nonserializable"

def Value.json (v : Value) : Result Json := do
  match v with
  | .verifierKey bytes => return .arr #[.str "verifier_key", .str (hex bytes)]
  | .selectedRng generation | .ristrettoRng generation | .extensionRng generation => return .arr #[.str "rng", .str (toString generation)]
  | _ => return .arr #[.str v.ty, .str (hex (← v.wire))]

def scalarVector (bytes : ByteArray) (count : Nat) : Result (List Math.Fr) := do
  ensure (count ≤ 2 ^ limits.rank && bytes.size == 32 * count) "scalar-vector-length"
  (List.range count).mapM fun i => fieldFromBytes (bytes.extract (32*i) (32*(i+1)))

/-- Structural checks precede the request for public group validation. -/
def decodeWire (ty : Ty) (bytes : ByteArray) : Result Value := do
  ensure (bytes.size ≤ byteLimit) "wire-limit"
  let expected ← tag ty
  ensure (bytes.size ≥ 6 && bytes.extract 0 5 == magic && bytes[5]! == expected) "wire-header"
  let payload := bytes.extract 6 bytes.size
  match ty with
  | "field" => return .field (← fieldFromBytes payload)
  | "bool" =>
      ensure (payload.size == 1 && (payload[0]! == 0 || payload[0]! == 1)) "wire-bool"
      return .boolean (payload[0]! == 1)
  | "round" =>
      let [a,b,c] ← scalarVector payload 3 | throw "wire-round"
      return .round ⟨a,b,c⟩
  | "table" | "point" =>
      ensure (payload.size ≥ 4) "wire-length"
      let n := valueLE (payload.extract 0 4)
      ensure (n ≤ limits.rank) "arity-limit"
      let values ← scalarVector (payload.extract 4 payload.size) (if ty == "table" then 2^n else n)
      if ty == "table" then return .table (← Math.Table.admit n values)
      else return .point values
  | "commitment" | "proof" =>
      ensure (payload.size ≥ 81 && payload.extract 0 8 == "ZKCAR006".toUTF8) "pcs-header"
      ensure (payload[8]! == (if ty == "commitment" then 2 else 3)) "pcs-kind"
      let n := valueLE (payload.extract 9 17)
      ensure (0 < n) "pcs-rank"
      ensure (n ≤ limits.rank) "arity-limit"
      ensure (payload.size == 81 + (if ty == "commitment" then 48 else 96*n)) "pcs-length"
      return .publicBytes ty bytes
  | "group" =>
      ensure (payload.size == 48) "group-length"
      return .publicBytes ty bytes
  | "groups" =>
      ensure (payload.size ≥ 4) "groups-length"
      let n := valueLE (payload.extract 0 4)
      ensure (n ≤ 4096) "group-limit"
      ensure (payload.size == 4 + 48*n) "groups-length"
      return .publicBytes ty bytes
  | _ => throw "unsupported-wire-type"

structure Cursor where
  bytes : ByteArray
  position : Nat

def Cursor.read (cursor : Cursor) (count : Nat) : Result (ByteArray × Cursor) := do
  ensure (cursor.position ≤ cursor.bytes.size && count ≤ cursor.bytes.size - cursor.position) "proof-truncated"
  return (cursor.bytes.extract cursor.position (cursor.position + count),
    { cursor with position := cursor.position + count })

def Cursor.message (cursor : Cursor) : Result (ByteArray × Cursor) := do
  let (sizeBytes, cursor) ← cursor.read 8
  let count := valueLE sizeBytes
  ensure (count ≤ byteLimit) "proof-message-limit"
  cursor.read count

def Cursor.finished (cursor : Cursor) : Bool := cursor.position == cursor.bytes.size

end Tools.Artifact
