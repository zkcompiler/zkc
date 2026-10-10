import Zkc.Source.Decoding
import Lean.Data.Json

/-! A tagged-array format for the finite source and direct logical plan.

Exact arities avoid ignored fields and duplicate-key ambiguity. Type and
operation codecs belong to the consumer-selected vocabulary. Resource limits
are decoder policy, not a semantic bound or a malformed-program theorem.
-/

set_option autoImplicit false

namespace Zkc.Source.Format

open Lean

inductive Error where
  | syntax
  | shape
  | natural
  | string
  | unknownType
  | unknownOperation
  | unknownStop
  | byteLimit
  | depthLimit
  | numberLimit
  deriving DecidableEq, Repr

def Error.code : Error → String
  | .syntax => "invalid-json"
  | .shape => "invalid-shape"
  | .natural => "expected-natural"
  | .string => "expected-string"
  | .unknownType => "unknown-type"
  | .unknownOperation => "unknown-operation"
  | .unknownStop => "unknown-stop"
  | .byteLimit => "byte-limit"
  | .depthLimit => "depth-limit"
  | .numberLimit => "number-limit"

structure Codec (α : Type) where
  encode : α → Json
  decode : Json → Except Error α

def natural : Json → Except Error Nat
  | .num ⟨.ofNat value, 0⟩ => .ok value
  | _ => .error .natural
def string (json : Json) : Except Error String := json.getStr?.mapError (fun _ => .string)

def array (json : Json) : Except Error (List Json) :=
  json.getArr?.map Array.toList |>.mapError (fun _ => .shape)

def stop : Codec PIR.Stop where
  encode
    | .reject => .str "reject"
    | .abort => .str "abort"
    | .exhausted => .str "exhausted"
    | .incomplete => .str "incomplete"
    | .refused => .str "refused"
  decode
    | .str "reject" => .ok .reject
    | .str "abort" => .ok .abort
    | .str "exhausted" => .ok .exhausted
    | .str "incomplete" => .ok .incomplete
    | .str "refused" => .ok .refused
    | _ => .error .unknownStop

variable {Ty Op : Type}

def encodeProgram (types : Codec Ty) (operations : Codec Op) : RawProgram Ty Op → Json
  | .ret index => .arr #[.str "return", toJson index]
  | .stop reason => .arr #[.str "stop", stop.encode reason]
  | .letOp op arguments next =>
    .arr #[.str "apply", operations.encode op, toJson arguments, encodeProgram types operations next]
  | .branch condition yes no =>
    .arr #[.str "if", toJson condition, encodeProgram types operations yes,
      encodeProgram types operations no]
  | .iterate count acc initial body next =>
    .arr #[.str "repeat", toJson count, types.encode acc, toJson initial,
      encodeProgram types operations body, encodeProgram types operations next]

def decodeProgram (types : Codec Ty) (operations : Codec Op) :
    Nat → Json → Except Error (RawProgram Ty Op)
  | 0, _ => .error .depthLimit
  | depth + 1, json => do
    match ← array json with
    | [.str "return", index] => return .ret (← natural index)
    | [.str "stop", reason] => return .stop (← stop.decode reason)
    | [.str "apply", op, arguments, next] =>
      return .letOp (← operations.decode op) (← (← array arguments).mapM natural)
        (← decodeProgram types operations depth next)
    | [.str "if", condition, yes, no] =>
      return .branch (← natural condition) (← decodeProgram types operations depth yes)
        (← decodeProgram types operations depth no)
    | [.str "repeat", count, acc, initial, body, next] =>
      return .iterate (← natural count) (← types.decode acc) (← natural initial)
        (← decodeProgram types operations depth body) (← decodeProgram types operations depth next)
    | _ => .error .shape

/-- Prevent exponent expansion in the JSON parser; strings are left untouched.
The format uses integer tokens only. A token limit is decoder capacity policy,
not a restriction on mathematical naturals in the source language. -/
private def checkNumbers (text : String) : Except Error Unit := do
  let mut quoted := false
  let mut escaped := false
  let mut digits := 0
  for char in text.toList do
    if quoted then
      if escaped then escaped := false
      else if char == '\\' then escaped := true
      else if char == '"' then quoted := false
    else if char == '"' then
      quoted := true
      digits := 0
    else if char.isDigit then
      digits := digits + 1
      if digits > 1024 then throw .numberLimit
    else if digits > 0 && (char == 'e' || char == 'E' || char == '.') then
      throw .natural
    else digits := 0

/-- Parsing is a runtime boundary; this definition makes its input limits explicit. -/
def parse (byteLimit : Nat) (text : String) : Except Error Json :=
  if text.utf8ByteSize > byteLimit then .error .byteLimit
  else do
    checkNumbers text
    (Json.parse text).mapError (fun _ => .syntax)

end Zkc.Source.Format
