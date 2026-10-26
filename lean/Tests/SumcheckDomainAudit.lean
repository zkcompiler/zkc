import ZkcExamples.Construction.SumcheckProofRounds
import ZkcExamples.Executable.SumcheckProof
import Zkc.Construction.Uniform.DomainHandler
import ZkcTools.DeclarationAudit

/-! Scoped axiom and semantic dependency checks for the retained migration. -/
run_cmd ZkcTools.DeclarationAudit.check [
   `Zkc.Construction.Uniform.DomainExecution, `Zkc.Construction.Uniform.DomainHandler,
   `Zkc.Construction.Uniform.DomainIteration, `Zkc.Construction.Uniform.DomainProperties,
   `ZkcExamples.Construction.SumcheckArtifact, `ZkcExamples.Construction.SumcheckDomainConnection,
   `ZkcExamples.Construction.SumcheckDomainControls, `ZkcExamples.Construction.SumcheckDomainRound,
   `ZkcExamples.Construction.SumcheckDomainLoop, `ZkcExamples.Construction.SumcheckDomainRoot,
   `ZkcExamples.Construction.SumcheckScalarProtocol, `ZkcExamples.Construction.SumcheckScalarRound,
   `ZkcExamples.Construction.SumcheckDomainVerifier, `ZkcExamples.Construction.SumcheckSourceConnection,
   `ZkcExamples.Construction.SumcheckProof,
   `ZkcExamples.Construction.SumcheckProofRounds, `ZkcExamples.Executable.SumcheckProof] "SUMCHECK-DOMAIN-AUDIT-PASS" true

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots := [``ZkcExamples.Construction.SumcheckProof.compiled_transform,
    ``ZkcExamples.Construction.SumcheckProof.compiled_transform_rounds]
  let forbidden := [`Zkc.Construction.specK, `Zkc.Construction.specStep,
    `Zkc.Construction.idealK, `Zkc.Construction.idealStep]
  let mut pending := roots
  let mut seen : Std.HashSet Name := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then throwError "maintained source proof reaches historical interpreter: {name}"
    let some info := env.find? name | throwError "missing dependency: {name}"
    let values := (info.value? true).map Expr.getUsedConstants |>.getD #[]
    pending := (info.type.getUsedConstants ++ values).toList ++ pending
  logInfo m!"SUMCHECK-DIRECT-SOURCE-PASS roots={roots.length} dependencies={seen.size}"

#print axioms Zkc.Construction.Uniform.DomainAdapter.validate_actual
#print axioms ZkcExamples.Construction.SumcheckProof.compiled_transform
#print axioms ZkcExamples.Executable.SumcheckProof.domain_prunes
#print axioms ZkcExamples.Executable.SumcheckProof.executable_transform_prunes
