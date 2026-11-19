import Zkc.Tools.Audit

open Lean Zkc.Tools.Audit

/-- Run inside the generated Lake package so both baselines and all their project
imports are loaded from their private artifacts. The three-axiom policy is local to
the published written certificates and the proofs that their admissions succeed. -/
def main : IO UInt32 := do
  initSearchPath (← findSysroot)
  let artifacts ← zkcArtifacts (← searchPathRef.get)
  let roots := #[`Baseline, `SameLog]
  let env ← importModules (roots.map fun module => { module }) {} (loadExts := false)
    (level := .private) (arts := artifacts)
  let libraries := roots.map fun root => ({name := root.toString, root} : Library)
  let (finding, lines) ← replay env libraries artifacts
  for line in lines do IO.println line
  if let some failure := finding then
    IO.eprintln failure.line
    return 1
  let theorems := roots.flatMap fun root =>
    #[`certified_core_admitted, `admitted_exists, `RelationAdmitted, `ExtractorAdmitted].map (root ++ ·)
  for name in theorems do
    unless (env.find? name).any (· matches .thmInfo _) do
      throw (IO.userError s!"missing theorem {name}")
  let (axioms, _, _) := dependencies env theorems
  let allowed := allowedAxioms.push ``Classical.choice
  IO.println s!"{theorems.size} written theorems, axioms {axioms}"
  return if axioms.all allowed.contains then 0 else 1
