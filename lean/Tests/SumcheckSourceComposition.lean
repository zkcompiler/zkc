import ZkcExamples.Structured.SumcheckSourceVerifier
import ZkcTools.DeclarationAudit

/-! Regression check for the maintained proof chain, rather than another
substitution wrapper: every source verifier equation must actually depend on
the generic interpreted source-call rule, through the generated root normal
form and its application step. Inspect stored proof bodies, including private
helpers; merely importing the rule cannot satisfy this check. -/
namespace Tests.SumcheckSourceComposition
open Lean Elab Command

private partial def dependencyPath (env : Lean.Environment) (modules : List Name)
    (wanted : Name) (pending : List (Name × List Name))
    (seen : Std.HashSet Name := {}) : Option (List Name) :=
  match pending with
  | [] => none
  | (name, path) :: rest =>
      if name == wanted then some (path.reverse ++ [name])
      else if seen.contains name then dependencyPath env modules wanted rest seen
      else
        let next := do
          let owner ← ZkcTools.DeclarationAudit.moduleOf env name
          if !modules.contains owner then none else do
            let info ← env.find? name
            let value ← info.value? true
            some (value.getUsedConstants.toList.map (fun dependency => (dependency, name :: path)))
        dependencyPath env modules wanted (next.getD [] ++ rest) (seen.insert name)

/-- Also usable by an optional consumer audit without importing that package
into the main tests. Only actual proof-body edges count as dependencies. -/
def checkDependencies (modules roots : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let wanted := ``Zkc.Source.Structured.UnitPayload.protocolApply_interpret_substitute
  for root in roots do
    let some path := dependencyPath env modules wanted [(root, [])]
      | throwError "source verifier proof does not use generic call substitution: {root}"
    logInfo m!"SOURCE-COMPOSITION-DEPENDENCY {path}"

run_cmd do
  checkDependencies [`ZkcExamples.Structured.SumcheckSourceVerifier,
      `ZkcExamples.Structured.SumcheckSourceNormalForms, `ZkcExamples.Structured.NormalFormSteps]
    [``ZkcExamples.Structured.SumcheckSourceVerifier.root_context_expansion,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_linked,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_missing,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_excess,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_zero,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_context_optional,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_optional,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_permuted_optional,
     ``ZkcExamples.Structured.SumcheckSourceVerifier.verifier_checked]
  ZkcTools.DeclarationAudit.check
    [`ZkcExamples.Structured.SumcheckSourceVerifier,
     `Zkc.Source.Structured.ContractComposition]
    "SUMCHECK-SOURCE-COMPOSITION-AUDIT-PASS" true

/-- error: source verifier proof does not use generic call substitution: ZkcExamples.Structured.SumcheckSourceVerifier.reduce_invoke_plain -/
#guard_msgs in
run_cmd do
  checkDependencies [`ZkcExamples.Structured.SumcheckSourceVerifier]
    [``ZkcExamples.Structured.SumcheckSourceVerifier.reduce_invoke_plain]

end Tests.SumcheckSourceComposition
