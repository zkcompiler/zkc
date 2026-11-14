module

public section

/-! A small JSON reader and printer.

It covers what the package format uses: arrays, strings, non-negative integers,
booleans and null. Objects and fractional numbers are refused. The reader works on the
bytes of the text and imports nothing.
-/

set_option autoImplicit false

namespace Zkc

inductive Json where
  | null
  | bool (value : Bool)
  | num (value : Nat)
  | str (value : String)
  | arr (items : Array Json)
  deriving Inhabited

namespace Json

instance : Coe String Json := ⟨.str⟩
instance : Coe Nat Json := ⟨.num⟩
instance {n : Nat} : OfNat Json n := ⟨.num n⟩

private def isSpace (byte : UInt8) : Bool :=
  byte == 0x20 || byte == 0x0a || byte == 0x0d || byte == 0x09

private partial def skipSpace (bytes : ByteArray) (position : Nat) : Nat :=
  if position < bytes.size && isSpace (bytes.get! position) then skipSpace bytes (position + 1)
  else position

private partial def readDigits (bytes : ByteArray) (position value : Nat) : Nat × Nat :=
  if position < bytes.size then
    let byte := bytes.get! position
    if 0x30 ≤ byte && byte ≤ 0x39 then
      readDigits bytes (position + 1) (value * 10 + (byte.toNat - 0x30))
    else (value, position)
  else (value, position)

private def hexDigit (byte : UInt8) : Option Nat :=
  if 0x30 ≤ byte && byte ≤ 0x39 then some (byte.toNat - 0x30)
  else if 0x61 ≤ byte && byte ≤ 0x66 then some (byte.toNat - 0x61 + 10)
  else if 0x41 ≤ byte && byte ≤ 0x46 then some (byte.toNat - 0x41 + 10)
  else none

/-- The text of a string literal from the byte after its opening quote. -/
private partial def readString (bytes : ByteArray) (position : Nat) (text : String) :
    Except String (String × Nat) :=
  if position < bytes.size then
    let byte := bytes.get! position
    if byte == 0x22 then .ok (text, position + 1)
    else if byte == 0x5c then
      if position + 1 < bytes.size then
        match bytes.get! (position + 1) with
        | 0x6e => readString bytes (position + 2) (text.push '\n')
        | 0x74 => readString bytes (position + 2) (text.push '\t')
        | 0x72 => readString bytes (position + 2) (text.push '\r')
        | 0x62 => readString bytes (position + 2) (text.push '\x08')
        | 0x66 => readString bytes (position + 2) (text.push '\x0c')
        | 0x75 =>
            if position + 5 < bytes.size then
              match hexDigit (bytes.get! (position + 2)), hexDigit (bytes.get! (position + 3)),
                  hexDigit (bytes.get! (position + 4)), hexDigit (bytes.get! (position + 5)) with
              | some a, some b, some c, some d =>
                  readString bytes (position + 6)
                    (text.push (Char.ofNat (((a * 16 + b) * 16 + c) * 16 + d)))
              | _, _, _, _ => .error "malformed JSON: a unicode escape is not four hex digits"
            else .error "malformed JSON: unterminated escape"
        | other => readString bytes (position + 2) (text.push (Char.ofNat other.toNat))
      else .error "malformed JSON: unterminated escape"
    else if byte < 0x80 then readString bytes (position + 1) (text.push (Char.ofNat byte.toNat))
    else
      -- A multi-byte character: decode the lead byte and its continuation bytes.
      let count := if byte < 0xe0 then 2 else if byte < 0xf0 then 3 else 4
      if position + count ≤ bytes.size then
        let lead := if count == 2 then byte.toNat % 0x20 else if count == 3 then byte.toNat % 0x10
          else byte.toNat % 0x08
        let code := (List.range (count - 1)).foldl
          (fun code offset => code * 0x40 + (bytes.get! (position + 1 + offset)).toNat % 0x40) lead
        readString bytes (position + count) (text.push (Char.ofNat code))
      else .error "malformed JSON: truncated character"
  else .error "malformed JSON: unterminated string"

mutual
  private partial def readValue (bytes : ByteArray) (start : Nat) : Except String (Json × Nat) :=
    let position := skipSpace bytes start
    if position < bytes.size then
      let byte := bytes.get! position
      if byte == 0x5b then readItems bytes (position + 1) #[]
      else if byte == 0x22 then
        match readString bytes (position + 1) "" with
        | .ok (text, next) => .ok (.str text, next)
        | .error message => .error message
      else if 0x30 ≤ byte && byte ≤ 0x39 then
        let (value, next) := readDigits bytes position 0
        if next < bytes.size && (bytes.get! next == 0x2e || bytes.get! next == 0x65 ||
            bytes.get! next == 0x45) then
          .error "malformed JSON: a number is not a non-negative integer"
        else .ok (.num value, next)
      else if byte == 0x74 && position + 4 ≤ bytes.size then .ok (.bool true, position + 4)
      else if byte == 0x66 && position + 5 ≤ bytes.size then .ok (.bool false, position + 5)
      else if byte == 0x6e && position + 4 ≤ bytes.size then .ok (.null, position + 4)
      else .error s!"malformed JSON: unexpected byte {byte} at {position}"
    else .error "malformed JSON: unexpected end"

  /-- The items of an array from the byte after its opening bracket or after a comma. -/
  private partial def readItems (bytes : ByteArray) (start : Nat) (items : Array Json) :
      Except String (Json × Nat) :=
    let position := skipSpace bytes start
    if position < bytes.size && bytes.get! position == 0x5d then .ok (.arr items, position + 1)
    else
      match readValue bytes position with
      | .ok (item, next) =>
          let after := skipSpace bytes next
          if after < bytes.size && bytes.get! after == 0x2c then
            readItems bytes (after + 1) (items.push item)
          else if after < bytes.size && bytes.get! after == 0x5d then
            .ok (.arr (items.push item), after + 1)
          else .error s!"malformed JSON: expected a comma or a closing bracket at {after}"
      | .error message => .error message
end

/-- Read one JSON value that fills the text. -/
def parse (text : String) : Except String Json :=
  let bytes := text.toUTF8
  match readValue bytes 0 with
  | .ok (value, next) =>
      if skipSpace bytes next == bytes.size then .ok value
      else .error s!"malformed JSON: text after the value at {next}"
  | .error message => .error message

private def escape (text : String) (out : String) : String :=
  text.foldl (fun out character =>
    if character == '"' then out ++ "\\\""
    else if character == '\\' then out ++ "\\\\"
    else if character == '\n' then out ++ "\\n"
    else if character == '\t' then out ++ "\\t"
    else if character == '\r' then out ++ "\\r"
    else out.push character) out

private partial def renderInto : Json → String → String
  | .null, out => out ++ "null"
  | .bool true, out => out ++ "true"
  | .bool false, out => out ++ "false"
  | .num value, out => out ++ toString value
  | .str text, out => (escape text (out.push '"')).push '"'
  | .arr items, out => Id.run do
      let mut out := out.push '['
      let mut first := true
      for item in items do
        if !first then out := out.push ','
        first := false
        out := renderInto item out
      return out.push ']'

/-- The text of a value, without spaces. -/
def render (value : Json) : String := renderInto value ""

end Json

end Zkc
