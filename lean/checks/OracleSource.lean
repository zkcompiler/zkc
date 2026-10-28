import ZkcTools.StructuredSource.WireTypes

/-! Cross-reader control over actual native output. This checks exact decoding,
not source correspondence, semantic admission or oracle realization. -/
set_option autoImplicit false
open Lean Zkc.Source.Structured ZkcTools.StructuredSource

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected native oracle snapshot")
  let json ← IO.ofExcept (Zkc.Source.Structured.Format.parse (← IO.FS.readFile path))
  let snapshot : Zkc.Source.Structured.Snapshot ← IO.ofExcept (Zkc.Source.Structured.Format.snapshot json)
  let kind : OracleKind := .table (.field "koala-bear") (some 16)
  let some (Zkc.Source.Structured.Definition.oracle declaration) := snapshot.definitions[1]? |
    throw (IO.userError "virtual definition was not retained")
  unless declaration.name == "select" && declaration.kind == kind &&
      declaration.admissibility == "admissible" && declaration.shapeArguments.isEmpty &&
      declaration.shapeBounds.isEmpty do throw (IO.userError "virtual header changed")
  let .block instructions terminal := declaration.body
  let [.instruction (.oracle (.query none first)) [0,2] [.field "koala-bear"] [] "first",
       .instruction (.oracle (.query none second)) [1,3] [.field "koala-bear"] [] "second",
       .instruction (.call "identity") [1] [.field "koala-bear"] [] ""] := instructions |
    throw (IO.userError "query events or actual operands changed")
  unless first == kind && second == kind && terminal == .ret [0] do
    throw (IO.userError "query answer changed")
  let some (Zkc.Source.Structured.Definition.function protocol) := snapshot.definitions[2]? |
    throw (IO.userError "protocol missing")
  unless protocol.inputs[1]? == some (.oracle kind) do
    throw (IO.userError "oracle input type changed")
  let .block operations _ := protocol.body
  unless operations.length == 13 do throw (IO.userError "unused operations lost")
  let descriptors := operations.filterMap fun (.instruction descriptor _ _ _ _) =>
    match descriptor with | .oracle value => some value | _ => none
  unless descriptors.length == 12 do throw (IO.userError "oracle vocabulary lost")
  IO.println "native oracle snapshot: exact independent decoding passed"
