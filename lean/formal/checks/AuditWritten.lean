import ZkcFormalTools.Policy

open Lean Zkc.Tools.Audit

/-- Run inside the generated Lake package so both baselines and all their project
imports are loaded from their private artifacts. The three-axiom policy is local to
the published written certificates and the proofs that their admissions succeed. -/
def checkCertificates : IO Unit := do
  initSearchPath (← findSysroot)
  let roots := #[`Baseline, `SameLog]
  let probe ← importModules #[{module := `AuditLocal}] {} (loadExts := false) (level := .private)
  let (finding, _) ← replay probe #[{name := "local replay fixture", root := `AuditLocal},
    {name := "source certificate", root := `Baseline}] #[`AuditVendor]
  unless finding.any (fun f => f.rule == .kernel && f.line.startsWith "a prebuilt library imports project module ") do
    throw (IO.userError "a prebuilt library could preload a project proof into kernel replay")
  let (probeAxioms, _, _) := dependencies probe #[`AuditLocal.fromExternal]
  unless probeAxioms.any (fun ax => !ZkcFormalTools.policy.axioms.contains ax) do
    throw (IO.userError "axiom traversal missed a private upstream dependency")
  let env ← importModules #[{module := `Checks}, {module := `OddFork}] {} (loadExts := false)
    (level := .private)
  let libraries := roots.map fun root => ({name := root.toString, root} : Library)
  let (finding, lines) ← replay env libraries ZkcFormalTools.policy.packages ZkcFormalTools.policy.project
  for line in lines do IO.println line
  if let some failure := finding then
    throw (IO.userError failure.line)
  let issuances := roots.flatMap fun root =>
    #[`certified_source_admitted, `certified_core_admitted, `admitted_exists, `RelationAdmitted, `ExtractorAdmitted].map (root ++ ·)
  let theorems := issuances ++ #[`Named.certified_source_admitted, `Context.certified_source_admitted,
    `Reordered.certified_core_admitted, `RolesReversed.certified_source_admitted,
    `ScalarGuard.certified_core_admitted,
    `WrittenControls.missing_compiled_guard, `WrittenControls.compiled_wrong_extractor,
    `WrittenControls.compiled_wrong_relation, `WrittenControls.missing_guard_admitted,
    `WrittenControls.permitted_counterexample, `WrittenControls.wrong_extractor,
    `WrittenControls.wrong_relation, `WrittenControls.wrong_verifier,
    `OddFork.schnorr_returns, `OddFork.sameLog_returns, `OddFork.compiled_witnesses,
    `OddFork.reversed_numerator, `OddFork.zero_refinement]
  for name in theorems do
    unless (env.find? name).any (· matches .thmInfo _) do
      throw (IO.userError s!"missing theorem {name}")
  let (axioms, _, _) := dependencies env theorems
  let allowed := ZkcFormalTools.policy.axioms
  IO.println s!"{theorems.size} written theorems, axioms {axioms}"
  unless axioms.all allowed.contains do
    throw (IO.userError s!"written certificate exceeds the formal axiom policy: {axioms}")

#eval checkCertificates
