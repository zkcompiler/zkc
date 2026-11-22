import ZkcFormalTools.Policy
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.UsesUnchecked

open Lean Zkc.Tools.Audit

#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let load (root : Name) := importModules #[{module := root}] {} (level := .private)
    (loadExts := false)
  let policy := ZkcFormalTools.policy
  -- Exercise each refusal in its own environment, outside the issuer's trusted base.
  for root in [`Zkc.Tools.Audit.Controls.Axiom, `Zkc.Tools.Audit.Controls.UsesUnchecked] do
    let some control := (controls "../compiler").find? (·.library.root == root)
      | throw (IO.userError s!"missing refusal control for {root}")
    unless control.refusedIn (← audit (← load control.library.root) #[control.library] policy) do
      throw (IO.userError s!"accepted {control.description}")
    IO.println s!"refused {control.description}"

  -- A library proper imports no module of the tests or of the tools of this package either:
  -- the rule takes their prefixes from the policy. The library here has no list of allowed
  -- imports, so no other rule refuses the import.
  let importer : Library := { name := "a library that imports a tool", root := `ZkcFormalTools.DrawCharge }
  let imported := (← audit (← load importer.root) #[importer] policy).findings
  unless imported.any (fun f => f.rule == .importOfTestsOrTools &&
      (f.line.splitOn "imports ZkcFormalTools.SumcheckCaller").length == 2) do
    throw (IO.userError "accepted a library that imports a module of the formal package's tools")
  IO.println "refused a library that imports a module of the formal package's tools"

  -- Even if the configured prebuilt set included Zkc, a project proof must never
  -- be preloaded into the starting kernel environment.
  let client := `Zkc.Tools.Audit.Controls.UsesUnchecked
  let (failure, _) ← replay (← load client) #[{name := "unchecked client", root := client}]
    (policy.packages.push `Zkc) policy.project
  unless failure.any (fun f => f.rule == .kernel && f.subject == `Zkc.Tools.Audit.Controls.Unchecked &&
      f.line.startsWith "a prebuilt library imports project module ") do
    throw (IO.userError "trusted imports could preload the project proof")
  IO.println "refused a trusted import closure containing the unchecked project proof"
