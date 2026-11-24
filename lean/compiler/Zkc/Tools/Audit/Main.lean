import Lake.Load.Workspace
import Zkc.Tools.Audit
-- the controls are imported so that Lake builds them; the audit reads them from their files
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.Extern
import Zkc.Tools.Audit.Controls.ImplementedBy
import Zkc.Tools.Audit.Controls.ConstructorIndex
import Zkc.Tools.Audit.Controls.Generated
import Zkc.Tools.Audit.Controls.Recognition
import Zkc.Tools.Audit.Controls.Unchecked
import Zkc.Tools.Audit.Controls.UsesUnchecked
import Zkc.Tools.Audit.Controls.Import
import Zkc.Tools.Audit.Controls.ImportOutside
import Zkc.Tools.Audit.Controls.Unreached
import Zkc.Tools.Audit.Controls.Unreached.Apart
import Zkc.Tools.Audit.Controls.Layers

/-! `zkc-audit`: the audit of the core, the vocabulary and their tests (`Zkc.Tools.Audit`). -/

open Zkc.Tools.Audit

/-- The libraries of the package. -/
def libraries (directory : System.FilePath) : Array Library := #[
  { name := "core", root := `Zkc.Core, imports := some coreImports, directory,
    generic := coreGeneric, concrete := coreConcrete },
  { name := "vocabulary", root := `Zkc.Vocabulary, imports := some vocabularyImports, directory },
  { name := "tests of the core", root := `Zkc.Tests.Core, kind := .tests, directory },
  { name := "tests of the vocabulary", root := `Zkc.Tests.Vocabulary, kind := .tests,
    directory }]

/-- Compare the audit's inventory of source files with the modules Lake selects when
building each library as a whole. Compare paths so library-specific source directories count. -/
def checkLibraryCoverage (directory : System.FilePath) : IO Bool := do
  let lean ← Lake.LeanInstall.get (← Lean.findSysroot)
  let lakeEnv ← (Lake.Env.compute (.ofLean lean) lean none).toIO IO.userError
  let some workspace ← (Lake.loadWorkspaceRoot { lakeEnv, wsDir := directory }).toBaseIO
    | throw (IO.userError s!"could not load the Lake package at {directory}")
  let mut selected : Std.HashSet System.FilePath := {}
  for library in workspace.root.leanLibs do
    let sourceDir ← IO.FS.realPath library.srcDir
    for sourceModule in ← library.getModuleArray do
      selected := selected.insert (Lean.modToFilePath sourceDir sourceModule.name "lean")
  let files ← leanFiles directory (directory / "Zkc")
  let mut missing := 0
  for name in files do
    let path := Lean.modToFilePath directory name "lean"
    unless selected.contains path do
      IO.eprintln s!"No Lean library selects {path}"
      missing := missing + 1
  IO.println s!"library coverage: {files.size} compiler modules, {workspace.root.leanLibs.size} library targets, {missing} unselected"
  return missing == 0

def main : IO UInt32 := do
  unless ← checkLibraryCoverage (← IO.FS.realPath (← packageDirectory)) do return 1
  run libraries
