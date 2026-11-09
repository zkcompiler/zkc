import Zkc.Applications.IR.Construction.SumcheckProofRounds
import Zkc.Applications.IR.Executable.SumcheckProof
import Zkc.IR.Construction.Uniform.DomainHandler
import Zkc.Tools.Program.DeclarationAudit

/-! Scoped axiom and semantic dependency checks for the retained migration. -/
run_cmd ZkcTools.DeclarationAudit.check [`Zkc.IR.Construction.Uniform.DomainExecution, `Zkc.IR.Construction.Uniform.DomainHandler, `Zkc.IR.Construction.ScalarConnection, `Zkc.IR.Construction.Uniform.ScalarFragment, `Zkc.IR.Construction.Uniform.ScalarObservation, `Zkc.Applications.IR.Construction.SumcheckArtifact, `Zkc.Applications.IR.Construction.SumcheckSourceConnection, `Zkc.Applications.IR.Construction.SumcheckProof, `Zkc.Applications.IR.Construction.SumcheckProofRounds, `Zkc.Applications.IR.Executable.SumcheckProof] "SUMCHECK-DOMAIN-AUDIT-PASS" true

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
