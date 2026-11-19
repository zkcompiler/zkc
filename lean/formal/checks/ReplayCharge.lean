import Zkc.Tools.Formal.DrawCharge
import Zkc.Tools.Formal.Policy

open Lean Zkc.Tools.Audit

#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let arts ← zkcArtifacts (← searchPathRef.get)
  let issuer := Zkc.Tools.Formal.chargeIssuer "."
  let env ← importModules #[{module := issuer.root}] {} (level := .private) (loadExts := false) (arts := arts)
  unless issuer.withoutReplay.isNone && issuer.root == `Zkc.Tools.Formal.DrawCharge do
    throw (IO.userError "the public charge issuer must be a kernel replay root")
  let report ← audit env #[issuer] arts Zkc.Tools.Formal.policy
  for line in report.lines do IO.println line
  for failure in report.findings do IO.println failure.line
  unless report.declarations > 0 && report.findings.isEmpty do throw (IO.userError "charge issuer audit failed")
  IO.println s!"{report.declarations} issuer declarations, {report.reached} reachable constants, axioms {report.axioms}"
