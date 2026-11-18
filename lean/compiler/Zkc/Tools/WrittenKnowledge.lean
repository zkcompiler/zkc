import Zkc.Frontend.Written.Export
import Zkc.Frontend.Syntax.Parser

open Zkc.Frontend in
private def source (path : System.FilePath) : IO SourceInput := do
  return ⟨path.toString, Syntax.parse path.toString (← IO.FS.readBinFile path)⟩

open Zkc.Frontend in
private def generate (input root : System.FilePath) (scheme : String) (proof : Bool) : IO UInt32 := do
  let entry ← source input
  let assembly ← assemble #[entry] fun segments => do
    let relative := "/".intercalate segments.toList ++ ".zkc"
    for dir in [input.parent.getD ".", root / "libraries", root / "examples", root / "examples/support"] do
      let path := dir / relative
      if ← path.pathExists then return some (← source path)
    return none
  match Written.exportSource assembly scheme proof with
  | .ok text => IO.print text; return 0
  | .error reason => IO.eprintln reason; return 1

def main : List String → IO UInt32
  | [input, root, scheme] => generate input root scheme true
  | ["--target-only", input, root, scheme] => generate input root scheme false
  | _ => do
    IO.eprintln "usage: zkc-knowledge [--target-only] INPUT.zkc PROJECT_ROOT SCHEME"
    return 2
