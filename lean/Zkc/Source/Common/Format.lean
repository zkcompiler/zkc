module

public import Zkc.Source.Common.Import
public import Zkc.Source.Format

@[expose] public section

/-! Strict tagged-array decoder for `zkc.common-source/0`.

No field is optional or ignored. Byte limits and numeric-token preflight precede
JSON parsing; flat instruction and declaration limits precede elaboration.
-/

set_option autoImplicit false

namespace Zkc.Source.Common.Native.Format

open Lean

def array (json : Json) : Except String (List Json) :=
  json.getArr?.map Array.toList |>.mapError fun _ => "common-source-array"

def string (json : Json) : Except String String := do
  let value ← json.getStr?.mapError fun _ => "common-source-string"
  if value.isEmpty || value.utf8ByteSize > 512 then throw "common-source-string"
  return value

def natural (json : Json) : Except String Nat := do
  let value ← Source.Format.natural json |>.mapError fun _ => "common-source-natural"
  if value > 2048 then throw "common-source-limit"
  return value

def naturals (json : Json) : Except String (List Nat) := do
  let values ← array json
  if values.length > 512 then throw "common-source-limit"
  values.mapM natural

def sort (json : Json) : Except String Ty := do
  match ← array json with
  | [.str "bool"] => return .boolean
  | [.str "field", domain] => return .field (← string domain)
  | [.str "group", domain] => return .group (← string domain)
  | [.str "service", contract] => return .service (← string contract)
  | _ => throw "common-source-type"

def decimal (json : Json) : Except String Nat := do
  let text ← string json
  if !(text.toList.all Char.isDigit) || (text.length > 1 && text.startsWith "0") then
    throw "common-source-constant"
  let some value := text.toNat? | throw "common-source-constant"
  return value

def operation (json : Json) : Except String Op := do
  match ← array json with
  | [.str "field.constant", domain, value] => return .fieldConstant (← string domain) (← decimal value)
  | [.str "field.add", domain] => return .fieldAdd (← string domain)
  | [.str "field.subtract", domain] => return .fieldSubtract (← string domain)
  | [.str "field.multiply", domain] => return .fieldMultiply (← string domain)
  | [.str "field.equal", domain] => return .fieldEqual (← string domain)
  | [.str "group.identity", domain] => return .groupIdentity (← string domain)
  | [.str "group.add", domain] => return .groupAdd (← string domain)
  | [.str "group.scale", group, scalar] => return .groupScale (← string group) (← string scalar)
  | [.str "group.equal", domain] => return .groupEqual (← string domain)
  | [.str "bool.constant", .bool value] => return .booleanConstant value
  | [.str "bool.and"] => return .booleanAnd
  | [.str "bool.or"] => return .booleanOr
  | [.str "bool.xor"] => return .booleanXor
  | [.str "bool.equal"] => return .booleanEqual
  | [.str "bool.not_equal"] => return .booleanNotEqual
  | [.str "select", type] => return .select (← sort type)
  | _ => throw "common-source-operation"

def instruction (json : Json) : Except String Instruction := do
  match ← array json with
  | [.str "pure", op, args] => return .pure (← operation op) (← naturals args)
  | [.str "restrict", roles, type, value] => return .restrict (← naturals roles) (← sort type) (← natural value)
  | [.str "exchange", site, sender, receiver, type, value] =>
      return .exchange (← string site) (← natural sender) (← natural receiver) (← sort type) (← natural value)
  | [.str "draw", site, owner, domain, value] =>
      return .draw (← string site) (← natural owner) (← string domain) (← natural value)
  | [.str "guard", site, owner, value] => return .guard (← string site) (← natural owner) (← natural value)
  | [.str "statement", relation, types, selectors, arguments] =>
      let types ← array types
      if types.length > 512 then throw "common-source-limit"
      return .statement (← string relation) (← types.mapM sort) (← naturals selectors) (← naturals arguments)
  | _ => throw "common-source-instruction"

def snapshot (json : Json) : Except String Snapshot := do
  match ← array json with
  | [.str "zkc.common-source/0", source, symbol, roles, inputs, inputRoles,
      result, outputRoles, instructions, returned] =>
      let source ← string source
      if source.length != 71 || !source.startsWith "sha256:" ||
          !(source.toList.drop 7).all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')) then
        throw "common-source-identity"
      let roles ← array roles
      let inputs ← array inputs
      let inputRoles ← array inputRoles
      let instructions ← array instructions
      if roles.length > 16 || inputs.length > 512 || inputRoles.length != inputs.length ||
          instructions.length > 1024 then throw "common-source-limit"
      return ⟨source, ← string symbol, ← roles.mapM string, ← inputs.mapM sort,
        ← inputRoles.mapM naturals, ← sort result, ← naturals outputRoles,
        ← instructions.mapM instruction, ← natural returned⟩
  | _ => throw "common-source-format"

/-- Bound recursion before entering Lean's JSON parser; quoted delimiters do
not count. Syntax, UTF-8 and numeric validation remain separate. -/
def parse (text : String) : Except String Json := do
  if text.utf8ByteSize > 1024 * 1024 then throw "byte-limit"
  let mut depth := 0
  let mut quoted := false
  let mut escaped := false
  for char in text.toList do
    if quoted then
      if escaped then escaped := false
      else if char == '\\' then escaped := true
      else if char == '"' then quoted := false
    else if char == '"' then quoted := true
    else if char == '-' then throw "expected-natural"
    else if char == '{' || char == '}' then throw "invalid-shape"
    else if char == '[' then
      depth := depth + 1
      if depth > 64 then throw "depth-limit"
    else if char == ']' then depth := depth - 1
  (Source.Format.parse (1024 * 1024) text).mapError Source.Format.Error.code

def decode (text : String) : Except String Imported := do
  (← snapshot (← parse text)).check

end Zkc.Source.Common.Native.Format
