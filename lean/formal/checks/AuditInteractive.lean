import Zkc.Tools.Audit

open Lean Zkc.Tools.Audit

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let artifacts ← zkcArtifacts (← searchPathRef.get)
  let libraries : Array Library := #[
    { name := "interactive security", root := `Zkc.Formal.Interactive, directory := some ".",
      imports := some #[`Zkc.Core,`Zkc.Formal,`Init] },
    { name := "interactive mathematical controls", kind := .tests, root := `Zkc.Tests.Formal.Interactive, directory := some "." }]
  let env ← importModules (libraries.map fun lib => { module := lib.root }) {} (loadExts := false) (level := .private) (arts := artifacts)
  let report ← audit env libraries artifacts
  for line in report.lines do IO.println line
  for finding in report.findings do IO.println finding.line
  IO.println s!"{report.declarations} declarations, {report.reached} reachable constants, axioms {report.axioms}, {report.findings.size} findings"
  return if report.findings.isEmpty then 0 else 1
