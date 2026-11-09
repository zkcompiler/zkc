import Zkc.Tools.Program.ImportArtifacts

open Lean System

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError message

private def writeArtifact (root : FilePath) (relative : String) : IO Unit := do
  let path := root / relative
  IO.FS.createDirAll path.parent.get!
  IO.FS.writeFile path ""

#eval IO.FS.withTempDir fun directory => do
  let original ← searchPathRef.get
  try
    let first := directory / "first"
    let second := directory / "second"
    writeArtifact first "Shared/Program.olean"
    writeArtifact second "Shared/IR.olean"
    writeArtifact second "Shared/IR.olean.server"
    writeArtifact second "Shared/IR.olean.private"
    writeArtifact second "Shared/IR.ir.sig"
    writeArtifact second "Shared/IR.ir"
    searchPathRef.set [first, second, first]
    let artifacts ← ZkcTools.ImportArtifacts.collect
    check (artifacts.find? `Shared.Program |>.isSome) "first package module missing"
    let some ir := artifacts.find? `Shared.IR
      | throw <| IO.userError "second package module missing"
    check ((ir.oleanParts true).size == 3) "private proof parts missing"
    check (ir.irParts.size == 2) "interpreter parts missing"
    writeArtifact second "Shared/Program.olean"
    let duplicate ← try
        let _ ← ZkcTools.ImportArtifacts.collect
        pure false
      catch error => pure (error.toString.startsWith "ambiguous module provider")
    check duplicate "distinct providers were accepted"
    IO.FS.removeFile (second / "Shared/Program.olean")
    IO.FS.removeFile (second / "Shared/IR.olean.private")
    let incomplete ← try
        let _ ← ZkcTools.ImportArtifacts.collect
        pure false
      catch error => pure (error.toString.startsWith "incomplete private module artifacts")
    check incomplete "incomplete private proof parts were accepted"
  finally
    searchPathRef.set original
