import Tools.Mathematical.Codec
import Lean.Data.Json.Parser

/-! Bounded JSON transport for mathematical values.

Unlike general Json parsing, this reader retains object keys until duplicate
checking and never expands exponent or fractional numbers. String escaping uses
Lean's JSON primitives but rejects lone surrogates instead of replacing them.
The canonical byte codec remains the identity representation.
-/

set_option autoImplicit false
namespace Tools.Mathematical.Json
open Zkc.Source.Mathematical
open Std.Internal.Parsec Std.Internal.Parsec.String

private def escaped : Parser Char := do
  if (← peek!) != 'u' then return ← Lean.Json.Parser.escapedChar
  skip
  let u1 ← Lean.Json.Parser.hexChar; let u2 ← Lean.Json.Parser.hexChar
  let u3 ← Lean.Json.Parser.hexChar; let u4 ← Lean.Json.Parser.hexChar
  let value := (u1 <<< 12) ||| (u2 <<< 8) ||| (u3 <<< 4) ||| u4
  if 0xD800 ≤ value && value < 0xDC00 then
    attempt (Lean.Json.Parser.finishSurrogatePair value) <|> fail "math-unicode"
  else if 0xDC00 ≤ value && value < 0xE000 then
    fail "math-unicode"
  else
    return Char.ofNat value.toNat

private def text : Parser String := do
  skipChar '"'
  let mut result := ""
  for _ in [0:Codec.byteLimit] do
    let c ← any
    if c == '"' then return result
    if c == '\\' then
      result := result.push (← escaped)
    else if c.val ≥ 0x20 then
      result := result.push c
    else
      fail "math-json"
  fail "math-resource-limit"

private def number : Parser Nat := do
  let mut digits := ""
  for _ in [0:21] do
    if ← isEof then break
    let c ← peek!
    if c < '0' || c > '9' then break
    skip
    digits := digits.push c
  match Codec.natural digits with
  | .ok n => return n
  | .error code => fail code

private def reject {α : Type} (code : String) : StateT Nat Parser α :=
  StateT.lift (fail code)

private def peek : StateT Nat Parser Char := StateT.lift (peek! : Parser Char)
private def next : StateT Nat Parser Char := StateT.lift (any : Parser Char)
private def advance : StateT Nat Parser Unit := StateT.lift (skip : Parser Unit)

private def value : Nat → StateT Nat Parser Raw.Attribute
  | 0 => reject "math-resource-limit"
  | depth + 1 => do
      let remaining ← get
      if remaining == 0 then reject "math-resource-limit"
      set (remaining - 1)
      match ← peek with
      | '"' => let result ← text; ws; return .string result
      | 't' => skipString "true"; ws; return .boolean true
      | 'f' => skipString "false"; ws; return .boolean false
      | '[' =>
          advance; ws
          if (← peek) == ']' then advance; ws; return .array []
          let mut items := #[]
          for _ in [0:Codec.childLimit] do
            let child ← value depth
            items := items.push child
            let separator ← next
            ws
            if separator == ']' then return .array items.toList
            if separator != ',' then reject "math-json"
          reject "math-resource-limit"
      | '{' =>
          advance; ws
          if (← peek) == '}' then advance; ws; return .object []
          let mut items := #[]
          for _ in [0:Codec.childLimit / 2] do
            let key ← text
            ws; skipChar ':'; ws
            let child ← value depth
            items := items.push (key, child)
            let separator ← next
            ws
            if separator == '}' then return .object items.toList
            if separator != ',' then reject "math-json"
          reject "math-resource-limit"
      | c =>
          if '0' ≤ c && c ≤ '9' then
            let n ← number
            ws
            return .natural n
          reject "math-json"

def parse (input : String) : Except String Raw.Attribute := do
  Codec.ensure (input.utf8ByteSize ≤ Codec.byteLimit) "math-resource-limit"
  let parser : Parser Raw.Attribute := do
    ws
    let result ← (value 65).run' Codec.nodeLimit
    eof
    return result
  let result ← parser.run input
  -- Includes exact child counts, duplicate object keys and canonical naturals.
  let _ ← Codec.encode result
  return result

def read (path : System.FilePath) : IO (Except String Raw.Attribute) :=
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ Codec.byteLimit do
      let chunk ← handle.read (min 65536 (Codec.byteLimit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    if bytes.size > Codec.byteLimit then return .error "math-resource-limit"
    let some text := String.fromUTF8? bytes | return .error "math-unicode"
    return parse text

/-- The maintained common carrier contains only arrays and strings. -/
def common : Nat → Raw.Attribute → Except String Lean.Json
  | 0, _ => throw "math-resource-limit"
  | _ + 1, .string text => return .str text
  | depth + 1, .array values => return .arr (← values.mapM (common depth)).toArray
  | _, _ => throw "math-placement-common-value"

end Tools.Mathematical.Json
