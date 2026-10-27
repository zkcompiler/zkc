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

/-- Same Boolean ABI, but selecting one operand is not conjunction. -/
example : isConjunction (Zkc.Source.Region.ret
    (Zkc.Source.Values.cons (Zkc.Source.Var.here) Zkc.Source.Values.nil) :
      Zkc.Source.Region Zkc.Source.Structured.dialect [.boolean, .boolean] [.boolean]) = false := rfl

private meta def refuses {α : Type} (label expected : String) (result : Except String α) :
    Lean.Elab.Command.CommandElabM Unit := do
  match result with
  | .ok _ => throwError "accepted invalid binding: {label}"
  | .error reason =>
    unless reason == expected do throwError "wrong refusal for {label}: expected {expected}, got {reason}"
    Lean.logInfo m!"PASS {label}: {reason}"

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
    refuses "wrong public ABI association" "original-security-subject-abi-association" (validateABI program binding { metadata with publicPositions := [] })
    refuses "wrong producer ABI association" "original-security-subject-abi-association" (validateABI program binding { metadata with producerPositions := some [] })
    refuses "wrong nominal input types" "original-security-subject-abi-association" (validateABI program binding
      { metadata with types := [] })
    refuses "wrong service association" "original-security-subject-abi-association" (validateABI program binding
      { metadata with context := metadata.context.mapReplacement (fun replacement => { replacement with service := metadata.types.length }) })
    refuses "missing root calls" "construction-binding-source-query" (analyze program { root.artifacts.validator with instructions := [] } root.artifacts.producer)
    refuses "wrong root instruction order" "construction-binding-forward-reference" (analyze program
      { root.artifacts.validator with instructions := root.artifacts.validator.instructions.reverse } root.artifacts.producer)
    refuses "wrong full return ABI" "original-security-validator-return" (analyze program
      { root.artifacts.validator with returned := [] } root.artifacts.producer)
    for other in roots do
      if root.name != other.name then
        refuses "wrong source/artifact association" "construction-binding-export-context" (analyze program other.artifacts.validator root.artifacts.producer)
    unless binding.calls.length == (binding.assembly.steps.filter (fun step => step.callee.isSome)).length do
      throwError "source call was dropped"
    let some first := binding.calls.head? | throwError "missing call"
    refuses "terminal from unchecked call result" "original-security-terminal-return" (analyzeTerminal program.payload.definitions
      binding.calls binding.conjunctions
      (some first.call.resultOrder))
    if binding.calls.length > 1 then
      refuses "dropped call from final conjunction" "original-security-conjunction-coverage" (analyzeTerminal program.payload.definitions
        binding.calls binding.conjunctions
        (some first.check.resultOrder))
      let some last := binding.conjunctions.getLast? | throwError "missing conjunction"
      let some helper := last.helper | throwError "missing terminal helper"
      let terminal := analyzeTerminal program.payload.definitions
        binding.calls
      refuses "unknown terminal effect" "original-security-terminal-effect" (terminal
        (binding.conjunctions.dropLast ++ [{ last with helper := none }]) binding.assembly.returnedOrder)
      refuses "unknown terminal helper ABI" "original-security-terminal-helper" (terminal
        (binding.conjunctions.dropLast ++ [{ last with helper := some { helper with outputs := [] } }])
        binding.assembly.returnedOrder)
      refuses "missing terminal helper body" "original-security-terminal-helper-body" (analyzeTerminal
        (program.payload.definitions.filter (·.helper != helper))
        binding.calls binding.conjunctions binding.assembly.returnedOrder)
      refuses "non-Boolean terminal tuple coordinate" "original-security-conjunction-operands" (terminal
        (binding.conjunctions.dropLast ++ [{ last with operands := last.operands.map fun (binder, _) => (binder, 1) }])
        binding.assembly.returnedOrder)
      refuses "missing terminal return" "original-security-terminal-return" (terminal binding.conjunctions none)
      let body : Zkc.Source.Region Zkc.Source.Structured.dialect [.boolean, .boolean] [.boolean] :=
        .ret (.cons .here .nil)
      let replacement : Zkc.Source.Structured.CheckedDefinition := {
        name := helper.name, kind := .math, inputs := [.boolean, .boolean], outputs := [.boolean],
        raw := body.erase, body, formed := Zkc.Source.Region.elaborate_erase body }
      let altered := program.payload.definitions.map fun definition =>
        if definition.helper == helper then replacement else definition
      refuses "same helper name and ABI with different body" "original-security-terminal-helper-body" (analyzeTerminal altered
        binding.calls binding.conjunctions binding.assembly.returnedOrder)
      let repeated := { last with operands := [(first.check.resultOrder, 0),
        (first.check.resultOrder, 0)] }
      refuses "duplicate leaf cannot cover other calls" "original-security-conjunction-coverage" (analyzeTerminal program.payload.definitions
        binding.calls
        (binding.conjunctions.dropLast ++ [repeated]) binding.assembly.returnedOrder)
      let unavailable := { last with operands := [(1000000, 0), (1000001, 0)] }
      refuses "unavailable terminal operand" "original-security-conjunction-dependency" (analyzeTerminal program.payload.definitions
        binding.calls
        (binding.conjunctions.dropLast ++ [unavailable]) binding.assembly.returnedOrder)
  unless OriginalSecurityBindingsCatalogue.sources.length == roots.length * 5 do
    throwError "generated binding inventory"
  for (_, source) in OriginalSecurityBindingsCatalogue.sources do
    for retired in ["OriginalSecurityMeanings", "OriginalSecurityInstallation", "OriginalRawSources",
        "OriginalHonestSources", "OriginalHonestCompleteness", "pattern17", "pattern23",
        "sourceTwoRoots", "twoRoots_bridge", "twoRoots_rejected", "twoRoots_cost"] do
      if source.contains retired then throwError "generated binding retains handwritten wrapper: {retired}"
  Lean.logInfo "PASS structural security generation, actual ABI associations and output inventory"

end TestsSecurity.OriginalSecurityGeneration
