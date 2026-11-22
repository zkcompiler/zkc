import ZkcFormalTools.DrawCharge
import ZkcFormalTools.Policy

open Lean Zkc.Tools.Audit

#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let issuers := ZkcFormalTools.publicIssuers "."
  let env ← importModules (issuers.map fun issuer => {module := issuer.root}) {}
    (level := .private) (loadExts := false)
  let report ← audit env issuers ZkcFormalTools.policy
  for line in report.lines do IO.println line
  for failure in report.findings do IO.println failure.line
  unless report.declarations > 0 && report.findings.isEmpty do throw (IO.userError "charge issuer audit failed")
  IO.println s!"{report.declarations} issuer declarations, {report.reached} reachable constants, axioms {report.axioms}"
