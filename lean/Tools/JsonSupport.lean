import Zkc.Source.Format

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

/-- Interpreter work capacity is separate from semantic interface-call bounds. -/
def workBound {Ty Op : Type} : RawProgram Ty Op → Nat
  | .ret _ | .stop _ => 1
  | .letOp _ _ next => 1 + workBound next
  | .branch _ yes no => 1 + max (workBound yes) (workBound no)
  | .iterate count _ _ body next => 1 + count * (1 + workBound body) + workBound next

end Zkc.Tools
