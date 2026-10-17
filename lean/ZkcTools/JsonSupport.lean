module

public import Zkc.Source.Format

@[expose] public section

set_option autoImplicit false

namespace Zkc.Tools

open Lean Source

def byteLimit : Nat := 1024 * 1024

def readJson (path : System.FilePath) : IO (Except String Json) := do
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ byteLimit do
      let chunk ← handle.read (min 65536 (byteLimit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    if bytes.size > byteLimit then return .error "byte-limit"
    match String.fromUTF8? bytes with
    | none => return .error "invalid-utf8"
    | some text => return (Format.parse byteLimit text).mapError Format.Error.code

def emit (json : Json) : IO Unit := IO.println json.compress

def refused (code : String) : IO UInt32 := do
  emit (Json.mkObj [("status", .str "refused"), ("code", .str code)])
  return 1

end Zkc.Tools
