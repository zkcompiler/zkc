module

import ZkcSecurity.Generation.OriginalSecurityBindingsCatalogue
meta import ZkcSecurity.Generation.OriginalSecurityBindingsCatalogue

/-! Controls use the production catalogue. This test supplies no root bindings,
mathematical selections, occurrence coordinates or artifact return indices. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.OriginalSecurityGeneration
open ZkcSecurity.Generation
open ZkcSecurity.Generation.OriginalSecurityBindings

private meta def refuses {α : Type} (label : String) (result : Except String α) :
    Lean.Elab.Command.CommandElabM Unit := do
  match result with
  | .ok _ => throwError "accepted invalid binding: {label}"
  | .error reason => Lean.logInfo m!"PASS {label}: {reason}"

run_cmd do
  let roots ← Roots.evaluateSelections
  for root in roots do
    let .ok program := Zkc.Source.Structured.check root.snapshot | throwError "source admission"
    let .ok binding := analyze program root.artifacts.validator root.artifacts.producer
      | throwError "valid binding refused"
    let metadata ← Lean.Elab.Command.liftTermElabM do
      let subject := Lean.mkIdent ((root.subjectModule ++ ".subject").toName)
      let expression ← Lean.Elab.Term.elabTerm (← `(SubjectABI.metadata $subject)) none
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      let reduced ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (← Lean.instantiateMVars expression)
      Lean.Meta.evalExpr SubjectABI.Metadata (Lean.mkConst ``SubjectABI.Metadata) reduced
    unless validateABI program binding metadata == .ok () do throwError "valid subject ABI refused"
    refuses "wrong public ABI association" (validateABI program binding { metadata with publicPositions := [] })
    refuses "wrong producer ABI association" (validateABI program binding { metadata with producerPositions := some [] })
    refuses "wrong nominal input types" (validateABI program binding
      { metadata with types := [], inputPolicy := ⟨[]⟩ })
    refuses "wrong service association" (validateABI program binding
      { metadata with context := { metadata.context with service := metadata.types.length } })
    refuses "missing root calls" (analyze program { root.artifacts.validator with instructions := [] } root.artifacts.producer)
    refuses "wrong root instruction order" (analyze program
      { root.artifacts.validator with instructions := root.artifacts.validator.instructions.reverse } root.artifacts.producer)
    refuses "wrong full return ABI" (analyze program
      { root.artifacts.validator with returned := [] } root.artifacts.producer)
    for other in roots do
      if root.name != other.name then
        refuses "wrong source/artifact association" (analyze program other.artifacts.validator root.artifacts.producer)
    unless binding.calls.length == (binding.assembly.steps.filter (fun step => step.callee.isSome)).length do
      throwError "source call was dropped"
  unless OriginalSecurityBindingsCatalogue.sources.length == roots.length * 5 do
    throwError "generated binding inventory"
  for (_, source) in OriginalSecurityBindingsCatalogue.sources do
    for retired in ["OriginalSecurityMeanings", "OriginalSecurityInstallation", "OriginalRawSources",
        "OriginalHonestSources", "OriginalHonestCompleteness", "pattern17", "pattern23"] do
      if source.contains retired then throwError "generated binding retains handwritten wrapper: {retired}"
  Lean.logInfo "PASS structural security generation, actual ABI associations and output inventory"

end TestsSecurity.OriginalSecurityGeneration
