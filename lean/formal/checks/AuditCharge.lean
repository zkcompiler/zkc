import Zkc.Tools.Formal.Policy
import Zkc.Tools.Audit.Controls.Axiom
import Zkc.Tools.Audit.Controls.UsesUnchecked

open Lean Zkc.Tools.Audit

#eval show IO Unit from do
  initSearchPath (← findSysroot)
  let arts ← zkcArtifacts (← searchPathRef.get)
  let load (root : Name) := importModules #[{module := root}] {} (level := .private)
    (loadExts := false) (arts := arts)
  let policy := Zkc.Tools.Formal.policy
  -- Exercise each refusal in its own environment, outside the issuer's trusted base.
  for root in [`Zkc.Tools.Audit.Controls.Axiom, `Zkc.Tools.Audit.Controls.UsesUnchecked] do
    let some control := (controls "../compiler").find? (·.library.root == root)
      | throw (IO.userError s!"missing refusal control for {root}")
    unless control.refusedIn (← audit (← load control.library.root) #[control.library] arts policy) do
      throw (IO.userError s!"accepted {control.description}")
    IO.println s!"refused {control.description}"

  -- Even if the configured prebuilt set included Zkc, a project proof must never
  -- be preloaded into the starting kernel environment.
  let client := `Zkc.Tools.Audit.Controls.UsesUnchecked
  let (failure, _) ← replay (← load client) #[{name := "unchecked client", root := client}] arts
    (policy.packages.push `Zkc)
  unless failure.any (fun f => f.rule == .kernel && f.subject == `Zkc.Tools.Audit.Controls.Unchecked &&
      f.line.startsWith "a prebuilt library imports project module ") do
    throw (IO.userError "trusted imports could preload the project proof")
  IO.println "refused a trusted import closure containing the unchecked project proof"
