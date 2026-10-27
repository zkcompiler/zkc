module

public import ZkcTools.StructuredSource.OpenEvaluation
public import ZkcTools.StructuredSource.NormalForm
public import ZkcTools.StructuredSource.Presentation
public import ZkcTools.StructuredSource.Bindings.Generate
public import ZkcTools.StructuredSource.Bindings.Ledger
public import ZkcTools.JsonSupport
public import ZkcTools.SourceClaims.Components

@[expose] public section

namespace ZkcTools.StructuredSource

/-- This CLI accepts declaration names, not executable Lean expressions. The
typed printer API separately supports library-owned expression hints. -/
def declarationName (name : String) : Bool :=
  name.splitOn "." |>.all fun part => match part.toList with
    | [] => false
    | first :: rest =>
      let letter := fun c => ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z') || c == '_'
      letter first && rest.all (fun c => letter c || c.isDigit || c == '\'')

/-- Printer configuration names declarations in the generated Lean module.
It supplies no interpretation or proof: the emitted source is kernel checked
against the named admitted source and its exact protocol bodies. -/
def bindings (program : Zkc.Source.Structured.Program) (input : Lean.Json) :
    Except String Lean.Json := do
  let [.str moduleName, .str sourceModule, .str programExpression, .str importedExpression] ←
      Zkc.Source.Structured.Format.array input | throw "bindings-configuration"
  unless [moduleName, sourceModule, programExpression, importedExpression].all declarationName do
    throw "bindings-declaration-name"
  let output : Bindings.Output := {
    moduleName, sourceModule, programExpression, importedExpression }
  let source ← Bindings.source program output
  return Lean.Json.mkObj [
    ("format", .str "zkc.component-bindings/0"),
    ("source", .str program.snapshot.source),
    ("entry", .str program.snapshot.entry),
    ("lean_source", .str source),
    ("obligations", Bindings.obligationLedger program output)]

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
      ((mode != "run" && mode != "open" && mode != "normal-form" && mode != "presentation" &&
        mode != "bindings" && mode != "components") || args.length != 3) then
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
    if mode == "components" then
      let text ← ZkcTools.SourceClaims.Components.readText args[2]!
      match text.bind (ZkcTools.SourceClaims.Components.check program.snapshot) with
      | .error code => return ← Zkc.Tools.refused code
      | .ok () =>
        Zkc.Tools.emit (Lean.Json.mkObj [("status", .str "associated"),
          ("mathematical_obligations", .str "unresolved")])
        return 0
    match ← read args[2]! (1024 * 1024) with
    | .error code => Zkc.Tools.refused code
    | .ok inputs =>
      let result := if mode == "bindings" then bindings program inputs
        else if mode == "presentation" then Presentation.run program inputs
        else if mode == "normal-form" then NormalForms.run program inputs
        else if mode == "open" then evaluateOpen program inputs else evaluate program inputs
      match result with
      | .error code => Zkc.Tools.refused code
      | .ok result => Zkc.Tools.emit result; return 0

end ZkcTools.StructuredSource
