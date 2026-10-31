module

public import Zkc.Source.Format

@[expose] public section

/-! Bounded validation of complete logical type trees. This data vocabulary
does not select an interpreter or confer catalogue or installation authority. -/

namespace Zkc.Source.LogicalFormat
open Lean

def array (json : Json) (limit : Nat := 512) : Except String (List Json) := do
  let values ← json.getArr?.mapError fun _ => "logical-array"
  if values.size > limit then throw "logical-list-limit"
  return values.toList

def text (json : Json) : Except String String := do
  let value ← json.getStr?.mapError fun _ => "logical-string"
  if value.isEmpty || value.utf8ByteSize > 512 then throw "logical-string"
  return value

def natural (json : Json) : Except String Nat := do
  let some value := Source.Format.canonicalDecimal (← text json) |
    throw "logical-natural"
  if value ≥ 2 ^ 64 then throw "logical-natural"
  return value

def hexDigit (char : Char) : Option Nat :=
  if '0' ≤ char && char ≤ '9' then some (char.toNat - '0'.toNat)
  else if 'a' ≤ char && char ≤ 'f' then some (char.toNat - 'a'.toNat + 10)
  else if 'A' ≤ char && char ≤ 'F' then some (char.toNat - 'A'.toNat + 10)
  else none

def fourHex : List Char → Option (Nat × List Char)
  | a :: b :: c :: d :: rest => do
    return (4096 * (← hexDigit a) + 256 * (← hexDigit b) +
      16 * (← hexDigit c) + (← hexDigit d), rest)
  | _ => none

/-- Lean's JSON parser replaces lone surrogate escapes. Refuse those before
parsing, while leaving escaped backslashes and valid pairs unmodified. -/
def unicodeEscapesWithin : Nat → Bool → List Char → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | remaining + 1, quoted, chars =>
    match quoted, chars with
    | _, [] => true
    | true, '\\' :: 'u' :: rest =>
      match fourHex rest with
      | none => false
      | some (code, rest) =>
        if 0xD800 ≤ code && code < 0xDC00 then
          match rest with
          | '\\' :: 'u' :: rest =>
            match fourHex rest with
            | some (low, rest) => 0xDC00 ≤ low && low < 0xE000 &&
                unicodeEscapesWithin remaining true rest
            | none => false
          | _ => false
        else if 0xDC00 ≤ code && code < 0xE000 then false
        else unicodeEscapesWithin remaining true rest
    | true, '\\' :: _ :: rest => unicodeEscapesWithin remaining true rest
    | _, '"' :: rest => unicodeEscapesWithin remaining (!quoted) rest
    | _, _ :: rest => unicodeEscapesWithin remaining quoted rest

def checkUnicodeEscapes (value : String) : Except String Unit := do
  let chars := value.toList
  unless unicodeEscapesWithin chars.length false chars do throw "logical-unicode"

/-- Expanded JSON work is bounded even for callers supplying Json directly.
The source envelope imposes its own smaller byte and lexical-depth limits. -/
def workWithin : Nat → Nat → List (Nat × Json) → Bool
  | _, _, [] => true
  | 0, _, _ :: _ => false
  | remaining + 1, bytes, (depth, json) :: rest =>
    if depth > 64 then false else
    let cost := match json with | .str value => value.utf8ByteSize + 9 | _ => 9
    if cost > bytes then false else
    match json with
    | .arr children => workWithin remaining (bytes - cost)
        (children.toList.map (depth + 1, ·) ++ rest)
    | _ => workWithin remaining (bytes - cost) rest

def checkWork (json : Json) : Except String Unit := do
  unless workWithin 200000 67108864 [(1, json)] do throw "logical-work-limit"

def identifier (json : Json) : Except String String := do
  let value ← text json
  if value.utf8ByteSize > 128 then throw "logical-identifier"
  let initial := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
  unless (match value.toList with
    | [] => false
    | first :: rest => initial first && rest.all (fun c => initial c ||
      ('0' ≤ c && c ≤ '9') || c == '.' || c == '-')) do throw "logical-identifier"
  return value

def checkIdentityAt : Nat → Json → Except String Unit
  | 0, _ => .error "logical-identity-depth"
  | depth + 1, json => do
    match ← array json with
    | [.str "atom", atom] => discard <| text atom
    | [.str "tuple", children] => (← array children).forM (checkIdentityAt depth)
    | _ => throw "logical-identity"

/-- Python's ensure_ascii=False compact JSON convention, including the short
escapes for backspace, tab and form feed that Lean's default printer expands. -/
def quoted (value : String) : String :=
  "\"" ++ value.foldl (fun result char => result ++
    if char == '\x08' then "\\b"
    else if char == '\t' then "\\t"
    else if char == '\x0c' then "\\f"
    else Json.escape (String.singleton char)) "" ++ "\""

def identityEncodingAt : Nat → Json → Except String String
  | 0, _ => .error "logical-identity-depth"
  | depth + 1, json => do
    match ← array json with
    | [.str "atom", atom] => return quoted (← text atom)
    | [.str "tuple", children] =>
      let children ← (← array children).mapM (identityEncodingAt depth)
      return "[" ++ String.intercalate "," children ++ "]"
    | _ => throw "logical-identity"

/-- Atom/string and tuple/array are disjoint, so this exact canonical encoding
preserves the complete identity while retaining existing internal denotations.
Only structured tagged trees are accepted at the wire boundary. -/
def identity (json : Json) : Except String String := do
  checkWork json
  checkIdentityAt 64 json
  identityEncodingAt 64 json

inductive ArgumentKind where
  | domain (sort : String) | type | natural
  deriving BEq, Repr

/-- Fixed data vocabulary from the landed declarations. This selects shapes,
not the narrower semantic profile of any particular reader. -/
def constructorKinds : String → Option (List ArgumentKind)
  | "bool" | "index" | "indices" | "bytes" | "shake128_state" | "quotient_matrix" => some []
  | "field" | "vector" | "matrix" | "polynomial" | "table" | "point" | "round"
    | "rng" | "nonce" => some [.domain "Field"]
  | "group" | "groups" => some [.domain "Group"]
  | "transcript" => some [.domain "Transcript"]
  | "commitment" | "commitments" | "opening_states" | "proof" | "prover_key"
    | "verifier_key" | "opening_state" => some [.domain "Commitment"]
  | "resource_unit" => some [.domain "Slot"]
  | "sequence" => some [.type]
  | "fixed_vector" => some [.type, .natural]
  | "field_array" => some [.domain "Field", .natural]
  | _ => none

def domain (json : Json) : Except String (String × String) := do
  let [.str "domain", sort, name] ← array json | throw "logical-domain"
  let sort ← text sort
  unless ["Codec", "Commitment", "Field", "Group", "Slot", "Transcript"].contains sort do
    throw "logical-domain-sort"
  let name ← text name
  let letter := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
  let valid := match name.toList with
    | [] => false
    | first :: rest =>
      if sort == "Slot" then
        name.utf8ByteSize ≤ 128 && letter first && rest.all (fun c => letter c ||
          ('0' ≤ c && c ≤ '9') || c == '_' || c == '-' || c == '.')
      else name.utf8ByteSize ≤ 256 && (letter first || first == '_') && rest.all (fun c =>
        letter c || ('0' ≤ c && c ≤ '9') || c == '_' || c == '-' || c == '.' || c == '/')
  unless valid do throw "logical-domain-identity"
  return (sort, name)

mutual
  def checkTypeAt : Nat → Json → Except String Unit
    | 0, _ => .error "logical-type-depth"
    | depth + 1, json => do
      match ← array json with
      | [.str "apply", constructor, arguments] =>
        let some kinds := constructorKinds (← text constructor) | throw "logical-constructor"
        checkArgumentsAt depth kinds (← array arguments 16)
      | [.str "variant", nominal, alternatives] =>
        checkIdentityAt depth nominal
        let alternatives ← array alternatives
        if alternatives.isEmpty then throw "logical-alternatives"
        let names ← alternatives.mapM fun alternative => do
          let [name, payloads] ← array alternative | throw "logical-alternative"
          let name ← identifier name
          (← array payloads).forM (checkTypeAt depth)
          return name
        if names.eraseDups.length != names.length then throw "logical-alternatives"
      | [.str "oracle", .str "table", arguments] => checkOracleAt depth arguments
      | [.str "oracle_sequence", .str "table", arguments, maximum] =>
        checkOracleAt depth arguments
        discard <| natural maximum
      | [.str "service", contract] => discard <| text contract
      | _ => throw "logical-type"

  def checkArgumentsAt : Nat → List ArgumentKind → List Json → Except String Unit
    | _, [], [] => pure ()
    | depth, kind :: kinds, argument :: arguments => do
      match kind, ← array argument with
      | .domain expected, [.str "domain", _, _] =>
        let (actual, _) ← domain argument
        if actual != expected then throw "logical-argument-kind"
      | .type, [.str "type", value] => checkTypeAt depth value
      | .natural, [.str "nat", value] => discard <| natural value
      | _, _ => throw "logical-argument-kind"
      checkArgumentsAt depth kinds arguments
    | _, _, _ => throw "logical-argument-arity"

  def checkOracleAt (depth : Nat) (json : Json) : Except String Unit := do
    let arguments ← array json 2
    match arguments with
    | [_] => checkArgumentsAt depth [.type] arguments
    | [_, _] => checkArgumentsAt depth [.type, .natural] arguments
    | _ => throw "logical-oracle-kind"
end

/-- Validate a complete tree and retain it unchanged. Lowering into an admitted
calculus is a separate, explicitly selected consumer operation. -/
def type (json : Json) : Except String Json := do
  checkWork json
  checkTypeAt 64 json
  return json

end Zkc.Source.LogicalFormat
