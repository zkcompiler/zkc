import Zkc.Tools.Formal.DrawCharge
import Zkc.Tools.Formal.SumcheckGoal
import Zkc.Tools.Formal.TableBound
import Zkc.Tools.Formal.ConstructedVerifier
import Zkc.Tools.Formal.Policy

open Lean Zkc.Tools.Audit

#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let arts ← zkcArtifacts (← searchPathRef.get)
  let issuers := Zkc.Tools.Formal.publicIssuers "."
  let env ← importModules (issuers.map fun issuer => {module := issuer.root}) {}
    (level := .private) (loadExts := false) (arts := arts)
  let report ← audit env issuers arts Zkc.Tools.Formal.policy
  for line in report.lines do IO.println line
  for failure in report.findings do IO.println failure.line
  unless report.declarations > 0 && report.findings.isEmpty do throw (IO.userError "charge issuer audit failed")
  IO.println s!"{report.declarations} issuer declarations, {report.reached} reachable constants, axioms {report.axioms}"
