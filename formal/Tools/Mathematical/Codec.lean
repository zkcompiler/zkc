import Zkc.Source.Mathematical.Raw

/-! Independent bounded canonical mathematical-value byte codec.

The reader checks the converted logical tree directly, including strict UTF-8,
decimal naturals, key order, complete consumption and allocation limits. These
functions do not resolve declarations or admit a mathematical subject.
-/

set_option autoImplicit false
namespace Tools.Mathematical.Codec
open Zkc.Source.Mathematical

def byteLimit : Nat := 16777216
def nodeLimit : Nat := 200000
def childLimit : Nat := 32768
def depthLimit : Nat := 64

def utf8Less (a b : String) : Bool :=
  decide (List.Lex (fun x y : UInt8 => x.toNat < y.toNat) a.toUTF8.toList b.toUTF8.toList)

def ensure (ok : Bool) (error : String) : Except String Unit :=
  if ok then .ok () else .error error

def natural (text : String) : Except String Nat := do
  ensure (!text.isEmpty && text.utf8ByteSize ≤ 20) "math-natural"
  let some value := text.toNat? | throw "math-natural"
  ensure (value < Static.limit && toString value == text) "math-natural"
  return value

structure Writer where
  output : ByteArray := ByteArray.empty
  nodes : Nat := 0

private def writeHeader (tag : UInt8) (count depth : Nat) : StateT Writer (Except String) Unit := do
  let state ← get
  ensure (depth ≤ depthLimit && state.nodes < nodeLimit && state.output.size + 9 ≤ byteLimit)
    "math-resource-limit"
  let mut bytes := state.output.push tag
  for i in [0:8] do
    bytes := bytes.push (UInt8.ofNat (count / 2 ^ (8 * i) % 256))
  set (⟨bytes, state.nodes + 1⟩ : Writer)

private def writeText (text : String) (depth : Nat) : StateT Writer (Except String) Unit := do
  ensure text.toUTF8.validateUTF8 "math-unicode"
  let state ← get
  ensure (text.utf8ByteSize ≤ byteLimit - state.output.size) "math-resource-limit"
  writeHeader 0 text.utf8ByteSize depth
  let state ← get
  ensure (text.utf8ByteSize ≤ byteLimit - state.output.size) "math-resource-limit"
  set { state with output := state.output ++ text.toUTF8 }

private def scalar (tag payload : String) (depth : Nat) : StateT Writer (Except String) Unit := do
  writeHeader 1 2 depth
  writeText tag (depth + 1)
  writeText payload (depth + 1)

private def writeValue : Nat → Nat → Raw.Attribute → StateT Writer (Except String) Unit
  | 0, _, _ => throw "math-resource-limit"
  | fuel + 1, depth, value => do
      match value with
      | .boolean b => scalar "boolean" (if b then "true" else "false") depth
      | .natural n =>
          ensure (n < Static.limit) "math-natural"
          scalar "natural" (toString n) depth
      | .string text => scalar "string" text depth
      | .array values =>
          ensure (values.length < childLimit) "math-resource-limit"
          writeHeader 1 (values.length + 1) depth
          writeText "array" (depth + 1)
          for value in values do writeValue fuel (depth + 1) value
      | .object fields =>
          ensure (2 * fields.length + 1 ≤ childLimit) "math-resource-limit"
          -- Bound the keys before sorting; their byte strings are part of the
          -- final representation even when the corresponding values are tiny.
          let mut keyBytes := 0
          for (key, _) in fields do
            keyBytes := keyBytes + key.utf8ByteSize
            ensure (keyBytes ≤ byteLimit) "math-resource-limit"
          let fields := fields.toArray.qsort (fun a b => utf8Less a.1 b.1)
          writeHeader 1 (2 * fields.size + 1) depth
          writeText "object" (depth + 1)
          let mut previous : Option String := none
          for (key, value) in fields do
            if let some prior := previous then
              ensure (utf8Less prior key) "math-duplicate-key"
            previous := some key
            writeText key (depth + 1)
            writeValue fuel (depth + 1) value

def encode (value : Raw.Attribute) : Except String ByteArray := do
  let (_, state) ← (writeValue 65 0 value).run {}
  return state.output

structure Reader where
  offset : Nat := 0
  nodes : Nat := 0

private def readHeader (bytes : ByteArray) (tag : UInt8) (depth : Nat) :
    StateT Reader (Except String) Nat := do
  let state ← get
  ensure (state.offset + 9 ≤ bytes.size) "math-truncated"
  ensure (depth ≤ depthLimit && state.nodes < nodeLimit) "math-resource-limit"
  ensure (bytes[state.offset]! == tag) "math-tree-tag"
  let mut count := 0
  for i in [0:8] do
    count := count + bytes[state.offset + 1 + i]!.toNat * 2 ^ (8 * i)
  set (⟨state.offset + 9, state.nodes + 1⟩ : Reader)
  return count

private def readText (bytes : ByteArray) (depth : Nat) : StateT Reader (Except String) String := do
  let count ← readHeader bytes 0 depth
  let state ← get
  ensure (count ≤ byteLimit - state.offset) "math-resource-limit"
  ensure (count ≤ bytes.size - state.offset) "math-truncated"
  let some text := String.fromUTF8? (bytes.extract state.offset (state.offset + count))
    | throw "math-unicode"
  set { state with offset := state.offset + count }
  return text

private def readValue (bytes : ByteArray) :
    Nat → Nat → StateT Reader (Except String) Raw.Attribute
  | 0, _ => throw "math-resource-limit"
  | fuel + 1, depth => do
      let count ← readHeader bytes 1 depth
      let state ← get
      ensure (0 < count && count ≤ childLimit && count ≤ nodeLimit - state.nodes &&
        count ≤ (bytes.size - state.offset) / 9) "math-resource-limit"
      let tag ← readText bytes (depth + 1)
      if tag == "boolean" || tag == "natural" || tag == "string" then
        ensure (count == 2) "math-tree-shape"
        let payload ← readText bytes (depth + 1)
        if tag == "string" then return .string payload
        if tag == "natural" then return .natural (← natural payload)
        ensure (payload == "true" || payload == "false") "math-tree-shape"
        return .boolean (payload == "true")
      if tag == "array" then
        let mut values := #[]
        for _ in [0:count - 1] do
          values := values.push (← readValue bytes fuel (depth + 1))
        return .array values.toList
      if tag == "object" then
        ensure (count % 2 == 1) "math-tree-shape"
        let mut values := #[]
        let mut previous : Option String := none
        for _ in [0:(count - 1) / 2] do
          let key ← readText bytes (depth + 1)
          if let some prior := previous then
            ensure (utf8Less prior key) "math-key-order"
          previous := some key
          values := values.push (key, ← readValue bytes fuel (depth + 1))
        return .object values.toList
      throw "math-tree-shape"

def decode (bytes : ByteArray) : Except String Raw.Attribute := do
  ensure (bytes.size ≤ byteLimit) "math-resource-limit"
  let (value, state) ← (readValue bytes 65 0).run {}
  ensure (state.offset == bytes.size) "math-binary-trailing"
  return value

end Tools.Mathematical.Codec
