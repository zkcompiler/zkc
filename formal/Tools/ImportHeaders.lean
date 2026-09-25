import Lean

/-! Read headers with the selected Lean parser, without loading their imports.
The line-oriented JSON interface lets boundary checks share one parser process.
-/

set_option autoImplicit false

open Lean

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result ← try
      let request ← IO.ofExcept (Json.parse line)
      let source ← IO.ofExcept (request.getObjValAs? String "source")
      let path ← IO.ofExcept (request.getObjValAs? String "path")
      let (header, _, messages) ← Parser.parseHeader (Parser.mkInputContext source path)
      if messages.hasErrors then
        let errors ← messages.toList.mapM fun message => message.toString
        pure <| Json.mkObj [("error", toJson (String.intercalate "\n" errors))]
      else
        pure <| Json.mkObj [("imports", toJson ((Elab.HeaderSyntax.imports header false).map (·.module.toString)))]
    catch error => pure <| Json.mkObj [("error", toJson error.toString)]
    output.putStrLn result.compress
    output.flush
