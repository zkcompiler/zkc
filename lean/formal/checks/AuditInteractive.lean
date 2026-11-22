import Zkc.Tools.Audit

open Lean Zkc.Tools.Audit

def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let libraries : Array Library := #[
    { name := "interactive security", root := `ZkcFormal.Interactive, directory := some ".",
      imports := some #[`Zkc.Core,`ZkcFormal,`Init] },
    { name := "process judgments", root := `ZkcFormal.ProcessJudgment, directory := some ".",
      imports := some #[`Zkc.Core,`Init] },
    { name := "world observations", root := `ZkcFormal.WorldObservation, directory := some ".",
      imports := some #[`Zkc.Core,`ZkcFormal,`Init] },
    { name := "interactive mathematical controls", kind := .tests, root := `ZkcFormalTests.Interactive, directory := some "." }]
  let env ← importModules (libraries.map fun lib => { module := lib.root }) {} (loadExts := false) (level := .private)
  let report ← audit env libraries
  for line in report.lines do IO.println line
  for finding in report.findings do IO.println finding.line
  IO.println s!"{report.declarations} declarations, {report.reached} reachable constants, axioms {report.axioms}, {report.findings.size} findings"
  return if report.findings.isEmpty then 0 else 1
