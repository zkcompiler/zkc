import Tools.Interactive.ScalarReference
import Tools.JsonSupport
import Zkc.Relation.Reference

/-! Trusted IO/codec boundary for the native canonical relation transport.
The admitted objects use the existing ring model and sparse reference. Neither
JSON parsing nor external importer adequacy is a theorem of this module.
Resource capacities are decoder policy, not mathematical/security parameters.
-/

set_option autoImplicit false

namespace Tools.Relation.Transport

open Lean Zkc.Relation
open Reference
open Tools.Interactive.ScalarReference

def byteLimit : Nat := 64 * 1024 * 1024
def dimensionLimit : Nat := 65536
def termLimit : Nat := 1048576
def nodeLimit : Nat := 4 * termLimit + 4 * dimensionLimit + 16

private def hexUnit (bytes : ByteArray) (start : Nat) : Result Nat := do
  if start + 4 > bytes.size then throw "relation-json"
  let mut value := 0
  for i in [start:start + 4] do
    let b := bytes[i]!.toNat
    let digit ←
      if 48 ≤ b && b ≤ 57 then pure (b - 48)
      else if 65 ≤ b && b ≤ 70 then pure (b - 55)
      else if 97 ≤ b && b ≤ 102 then pure (b - 87)
      else throw "relation-json"
    value := 16 * value + digit
  return value

/-- Linear byte preflight before generic JSON: only arrays and strings; bounded
depth, token length and nodes. Explicit surrogate validation prevents the generic
parser from silently replacing a malformed Unicode escape by U+FFFD. -/
def preflight (bytes : ByteArray) : Result Unit := do
  if bytes.size > byteLimit then throw "relation-byte-limit"
  let mut depth := 0
  let mut nodes := 0
  let mut quoted := false
  let mut escaped := false
  let mut stringBytes := 0
  let mut pairedLowAt : Option Nat := none
  for i in [:bytes.size] do
    let b := bytes[i]!.toNat
    if quoted then
      if b == 34 && !escaped then
        quoted := false
      else
        stringBytes := stringBytes + 1
        if stringBytes > 1024 then throw "relation-string-limit"
        if escaped then
          escaped := false
          if b == 117 then
            let unit ← hexUnit bytes (i + 1)
            if 0xdc00 ≤ unit && unit ≤ 0xdfff then
              if pairedLowAt != some i then throw "relation-json"
              pairedLowAt := none
            else if 0xd800 ≤ unit && unit ≤ 0xdbff then
              if bytes[i + 5]?.map UInt8.toNat != some 92 ||
                  bytes[i + 6]?.map UInt8.toNat != some 117 then throw "relation-json"
              let low ← hexUnit bytes (i + 7)
              if !(0xdc00 ≤ low && low ≤ 0xdfff) then throw "relation-json"
              pairedLowAt := some (i + 6)
        else if b == 92 then escaped := true
    else if b == 34 then
      quoted := true
      stringBytes := 1
      nodes := nodes + 1
    else if b == 91 then
      depth := depth + 1
      nodes := nodes + 1
      if depth > 8 then throw "relation-depth-limit"
    else if b == 93 then
      if depth == 0 then throw "relation-json"
      depth := depth - 1
    else if !([44, 32, 10, 9, 13].contains b) then throw "relation-json"
    if nodes > nodeLimit then throw "relation-node-limit"
  if quoted || depth != 0 then throw "relation-json"

def parse (text : String) : Result Json := do
  preflight text.toUTF8
  (Json.parse text).mapError (fun _ => "relation-json")

/-- Read at most the byte cap plus one, including pipes and growing files. -/
def readJson (path : System.FilePath) : IO (Result Json) := do
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ byteLimit do
      let chunk ← handle.read (min 65536 (byteLimit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    if bytes.size > byteLimit then return .error "relation-byte-limit"
    let some text := String.fromUTF8? bytes | return .error "relation-json"
    return parse text

def array (json : Json) (code : String) : Result (Array Json) :=
  json.getArr?.mapError (fun _ => code)

/-- Decimal strings only, no sign, whitespace, exponent or leading zeros. -/
def natural (json : Json) (maximum : Nat) (code : String) : Result Nat := do
  let .str text := json | throw code
  if text.isEmpty || text.utf8ByteSize > 256 ||
      (text.utf8ByteSize > 1 && text.startsWith "0") ||
      !text.toList.all (fun c => '0' ≤ c && c ≤ '9') then throw code
  let n := text.toList.foldl (fun n c => 10 * n + (c.toNat - 48)) 0
  if n > maximum then throw code
  return n

/-- Range checking precedes casting into ZMod; ingress never reduces a scalar. -/
def scalar (domain : Domain) (json : Json) : Result (Scalar domain) := do
  let n ← natural json (domain.modulus - 1) "relation-coefficient"
  return (n : Scalar domain)

def vector (domain : Domain) (json : Json) : Result (Array (Scalar domain)) := do
  let values ← array json "relation-assignment-shape"
  if values.size > dimensionLimit then throw "relation-assignment-shape"
  values.mapM (scalar domain)

structure Decoded where
  domain : Domain
  columns : Nat
  outputs : Nat
  inputs : Nat
  rows : Nat
  system : RankOne.System (Scalar domain) rows columns

/-- Exact native schema, preserving row order and the output/input split.
Strict sparse admission rejects duplicate, unsorted and zero entries. -/
def decode (json : Json) : Result Decoded := do
  let record ← array json "relation-format"
  if record.size != 6 || record[0]! != .str "zkc.relation.r1cs/1" then
    throw "relation-format"
  let .str field := record[1]! | throw "relation-format"
  let domain ← Domain.parse field |>.mapError (fun _ => "relation-field")
  let columns ← natural record[2]! dimensionLimit "relation-dimension"
  let outputs ← natural record[3]! dimensionLimit "relation-dimension"
  let inputs ← natural record[4]! dimensionLimit "relation-dimension"
  if columns == 0 || outputs + inputs ≥ columns then throw "relation-dimension"
  let rows ← array record[5]! "relation-dimension"
  if rows.size > dimensionLimit then throw "relation-dimension"
  let mut matrices : Array (Array (Array (Nat × Scalar domain))) := #[#[], #[], #[]]
  let mut terms := 0
  for row in rows do
    let forms ← array row "relation-row"
    if forms.size != 3 then throw "relation-row"
    for k in [:3] do
      let entries ← array forms[k]! "relation-term-limit"
      terms := terms + entries.size
      if terms > termLimit then throw "relation-term-limit"
      let entries ← entries.mapM fun entry => do
        let pair ← array entry "relation-term"
        if pair.size != 2 then throw "relation-term"
        let column ← natural pair[0]! dimensionLimit "relation-dimension"
        let value ← scalar domain pair[1]!
        return (column, value)
      matrices := matrices.set! k (matrices[k]!.push entries)
  let system ← admitSystem rows.size columns matrices[0]! matrices[1]! matrices[2]!
  return ⟨domain, columns, outputs, inputs, rows.size, system⟩

def scalarJson {domain : Domain} (value : Scalar domain) : Json := .str (toString value.val)

def encode (relation : Decoded) : Json :=
  let form := fun (entries : Sparse.Row (Scalar relation.domain) relation.columns) =>
    Json.arr (entries.toArray.map fun (column, value) =>
      .arr #[.str (toString column.val), scalarJson value])
  .arr #[.str "zkc.relation.r1cs/1", .str relation.domain.identity,
    .str (toString relation.columns), .str (toString relation.outputs),
    .str (toString relation.inputs), .arr (Array.ofFn fun i : Fin relation.rows =>
      .arr #[form relation.system.A.rows[i], form relation.system.B.rows[i],
        form relation.system.C.rows[i]])]

def evaluate (relation : Decoded) (statement assignment : Json) : Result Json := do
  let x ← admitVector (relation.outputs + relation.inputs) (← vector relation.domain statement)
    "relation-assignment-shape"
  let z ← admitVector relation.columns (← vector relation.domain assignment)
    "relation-assignment-shape"
  let binding ← admitBinding relation.columns (relation.outputs + relation.inputs) 0
    ((Array.range (relation.outputs + relation.inputs)).map (· + 1))
  let values := products relation.system z
  let bound := binding.check x z
  return Json.mkObj [("bound", toJson bound),
    ("satisfied", toJson (bound && values.check)),
    ("products", .arr #[.arr (values.a.toArray.map scalarJson),
      .arr (values.b.toArray.map scalarJson), .arr (values.c.toArray.map scalarJson)])]

end Tools.Relation.Transport

/-! Canonical relation CLI. FILE, STATEMENT and ASSIGNMENT are file paths.
Successful evaluation (including false satisfaction) exits zero. Parsing and
admission refusals exit one with a machine-readable code. No subject hash is
computed; matching semantics does not establish importer/compiler adequacy. -/

set_option autoImplicit false

def main (args : List String) : IO UInt32 := do
  let [file, statement, assignment] := args | do
    IO.eprintln "usage: relation-reference FILE STATEMENT ASSIGNMENT"
    return 2
  try
    let relation ← Tools.Relation.Transport.readJson file
    let x ← Tools.Relation.Transport.readJson statement
    let z ← Tools.Relation.Transport.readJson assignment
    let result := do
      Tools.Relation.Transport.evaluate (← relation >>= Tools.Relation.Transport.decode) (← x) (← z)
    match result with
    | .ok json => Zkc.Tools.emit json; return 0
    | .error code => Zkc.Tools.refused code
  catch _ => Zkc.Tools.refused "relation-io"
