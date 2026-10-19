module

public import ZkcTools.StructuredSource.OpenEvaluation
public import ZkcTools.StructuredSource.NormalForm
public import ZkcTools.JsonSupport

@[expose] public section

namespace ZkcTools.StructuredSource

/-- Bound bytes before UTF-8 decoding and lexical JSON preflight. -/
def read (path : System.FilePath) (byteLimit : Nat := 16 * 1024 * 1024) :
    IO (Except String Lean.Json) := do
  IO.FS.withFile path .read fun handle => do
    let mut bytes := ByteArray.empty
    while bytes.size ≤ byteLimit do
      let chunk ← handle.read (min 65536 (byteLimit + 1 - bytes.size)).toUSize
      if chunk.isEmpty then break
      bytes := bytes ++ chunk
    if bytes.size > byteLimit then return .error "byte-limit"
    let some text := String.fromUTF8? bytes | return .error "invalid-utf8"
    return Zkc.Source.Structured.Format.parse text byteLimit

def run (args : List String) : IO UInt32 := do
  let mode := args.headD ""
  if (mode != "check" || args.length != 2) &&
      ((mode != "run" && mode != "open" && mode != "normal-form") || args.length != 3) then
    return ← Zkc.Tools.refused "structured-source-arguments"
  let json ← read args[1]!
  let decoded := do
    let snapshot ← Zkc.Source.Structured.Format.snapshot (← json)
    Zkc.Source.Structured.check snapshot
  match decoded with
  | .error code => Zkc.Tools.refused code
  | .ok program =>
    if mode == "check" then
      Zkc.Tools.emit (.arr #[.str "checked", .str program.snapshot.source, .str program.snapshot.entry])
      return 0
    match ← read args[2]! (1024 * 1024) with
    | .error code => Zkc.Tools.refused code
    | .ok inputs =>
      let result := if mode == "normal-form" then NormalForms.run program inputs
        else if mode == "open" then evaluateOpen program inputs else evaluate program inputs
      match result with
      | .error code => Zkc.Tools.refused code
      | .ok result => Zkc.Tools.emit result; return 0

end ZkcTools.StructuredSource

def main (args : List String) : IO UInt32 := do
  try ZkcTools.StructuredSource.run args
  catch _ => Zkc.Tools.refused "structured-source-io"
