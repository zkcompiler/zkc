module

public import Zkc.Semantics.Interaction
public import Lean.Data.Json

@[expose] public section

/-! Strict JSON primitives for the bounded scalar import format.

Consumer-owned tagged arrays check exact arities, avoiding ignored fields and
duplicate-key ambiguity. Type and operation codecs belong to that vocabulary. Resource limits
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

/-- Bounded canonical ASCII decimal text. The list fold reduces in the kernel,
so checked constructor data can contain constants without a native evaluator.
The format excludes signs, separators, whitespace and leading zeroes. -/
def canonicalDecimal (text : String) (byteLimit : Nat := 512) : Option Nat := do
  if text.utf8ByteSize > byteLimit then none else do
    let digits := text.toList
    if digits.isEmpty || !digits.all Char.isDigit ||
        (digits.length > 1 && digits.head? == some '0') then none
    else some (digits.foldl (fun value digit => 10 * value + (digit.toNat - '0'.toNat)) 0)

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

/-- Prevent exponent expansion in the JSON parser; strings are left untouched.
The format uses integer tokens only. A token limit is decoder capacity policy,
not a restriction on mathematical naturals in the source language. -/
def checkNumbers (text : String) : Except Error Unit := do
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
