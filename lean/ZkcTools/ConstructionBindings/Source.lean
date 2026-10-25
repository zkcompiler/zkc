module

public import ZkcTools.ConstructionBindings.Analysis

@[expose] public section

/-! Producer source assembly from the existing typed normal form. The source
normalizer and interpreter are unchanged. The emitted `derive_process` equation
checks the entire original body at role zero, with arbitrary optional inputs. -/
set_option autoImplicit false
namespace ZkcTools.ConstructionBindings.Source
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcTools.StructuredSource.Presentation ZkcTools.StructuredSource.OriginalRoot

def assemble (program : Program) (callees : List CalleeKey) (inputs : List Ty) :
    {Δ : Scope} → {outputs : List Ty} → List Binder → Form [] callees Δ outputs → Nat → Except String Assembly
  | _, _, binders, .done values, _ => do
    let _ ← selectParameters binders (← dependencies values)
    return { returned := valuesText (compsText (naming callees inputs) (binders.map (·.name)) values) }
  | _, _, binders, .owned owner helper args next, number => do
    let helperName ← helperAlias program helper
    let parameters ← selectParameters binders (← dependencies args)
    let arguments := valuesText (compsText (naming callees inputs) (binders.map (·.name)) args)
    let process := app "Participant.owned" ["0", toString owner, app "invoke" ["tables.closed", helperName], arguments]
    let step : Step := { name := "step" ++ toString number, parameters, arguments := "tables", process, realized := process, outputs := helper.outputs, helper := some helper }
    let tail ← assemble program callees inputs (⟨"out" ++ toString number, .tuple helper.outputs, inputs.length + number⟩ :: binders) next (number + 1)
    return { tail with steps := step :: tail.steps }
  | _, _, binders, .math helper args next, number => do
    let helperName ← helperAlias program helper
    let parameters ← selectParameters binders (← dependencies args)
    let arguments := valuesText (compsText (naming callees inputs) (binders.map (·.name)) args)
    let process := app "invoke" ["tables.components", helperName, arguments]
    let step : Step := { name := "step" ++ toString number, parameters, arguments := "tables", process, realized := process, outputs := helper.outputs, helper := some helper }
    let tail ← assemble program callees inputs (⟨"out" ++ toString number, .tuple helper.outputs, inputs.length + number⟩ :: binders) next (number + 1)
    return { tail with steps := step :: tail.steps }
  | _, _, binders, .apply callee signature roles site args next, number => do
    let index ← calleeIndex program signature
    unless (calleeAt callees callee).role == 0 && roles == [0, 1] do throw "construction-binding-source-roles"
    let (deps, _) ← componentArguments args
    let parameters ← selectParameters binders deps
    let arguments := valuesText (argumentsText (naming callees inputs) (binders.map (·.name)) args)
    let context := app "ProtocolContext.enter" ["{}", quoted site, natsText roles]
    let process := app "invokeProtocol" ["protocols", "sourceProtocol" ++ toString index ++ ".signature", context, "0", arguments]
    let realized := app "realizeProducerCall" ["(G := G)", "payload", "maximum" ++ toString index, context,
      "sourceProtocol" ++ toString index ++ ".outputScopes", arguments]
    let step : Step := { name := "step" ++ toString number, parameters, arguments := "protocols", process, realized, outputs := signature.outputs, context := some context, callee := some index }
    let tail ← assemble program callees inputs (⟨"out" ++ toString number, .tuple signature.outputs, inputs.length + number⟩ :: binders) next (number + 1)
    return { tail with steps := step :: tail.steps }
  | _, _, _, _, _ => throw "construction-binding-source-form"

def assembly (program : Program) : Except String (List Binder × Assembly) := do
  let root := program.payload.entry
  let library ← ZkcTools.ConstructionBindings.unique "source-library"
    (program.payload.protocols.filter fun definition => definition.name != root.name)
  let keys := [CalleeKey.mk library.signature 0 (Bindings.optionalPattern library.inputs) []]
  let sig : Signature := ⟨[], false, true, program.payload.definitions.map (·.helper), keys⟩
  let form ← normalize sig root.body 0 root.roles.length (Bindings.optionalPattern root.inputs)
  unless ZkcTools.StructuredSource.NormalForms.callsMatch form do throw "construction-binding-source-call-identity"
  let binders := root.inputs.zipIdx.map fun (ty, index) => Binder.mk ("input" ++ toString index) (.component ty) index
  return (binders, ← assemble program keys root.inputs binders form 0)

def realizationProof (assembly : Assembly) : String := Id.run do
  let mut text := "  unfold process realized\n"
  let mut indent := "  "
  for (step, index) in assembly.steps.zipIdx do
    let proof := if step.callee.isSome then
      "exact " ++ app (step.name ++ "_binding") ("(G := G)" :: step.parameters.map (·.name))
      else "rfl"
    text := text ++ indent ++ "apply congrArg₂ PIR.Process.bind\n" ++ indent ++ "· " ++ proof ++
      "\n" ++ indent ++ "· funext out" ++ toString index ++ "\n"
    indent := indent ++ "  "
  return text ++ indent ++ "rfl\n"

def source (program : Program) (moduleName originalModule : String) : Except String String := do
  let (binders, assembly) ← assembly program
  let parameters ← parameterText binders
  let inputNames := " ".intercalate (binders.map (·.name))
  let inputValues := valuesText (binders.map (·.name))
  let visibleBinders := binders.filter fun binder =>
    (program.payload.entry.inputScopes[binder.order]?.getD []).contains 0
  let participantParameters ← parameterText visibleBinders
  let participantArguments := binders.map fun binder =>
    if visibleBinders.any (·.name == binder.name) then binder.name else "none"
  let participantNames := " ".intercalate participantArguments
  let participantValues := valuesText participantArguments
  let mut text := "module\n\npublic import " ++ originalModule ++
    "\npublic import ZkcExamples.Structured.OriginalSumcheckProducerCalls\n\n@[expose] public section\n" ++
    "set_option autoImplicit false\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "set_option backward.isDefEq.respectTransparency false\nnoncomputable section\nnamespace " ++ moduleName ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured\n" ++
    "open OriginalSumcheckLibrary SumcheckVerifierBodies\nopen ZkcExamples.Structured.OriginalSumcheckProducerCalls\n" ++
    "open ZkcExamples.Structured.OriginalSumcheckCalls\nopen " ++ originalModule ++ "\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n" ++
    "theorem root_lookup_self (self : Nat) (args : Values (Component (assignment F G)) root.inputs) :\n" ++
    "    invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} self args =\n" ++
    "      root.denoteWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn protocolPrefix1 Occurrence.iterations {} self args := by\n" ++
    "  unfold Occurrence.table\n  rw [← helpers_on, protocols_eq]\n" ++
    "  simp only [List.foldl_cons, List.foldl_nil, extendProtocolTableOn]\n  rw [invokeProtocol_cons_same]\n  rfl\n\n"
  for step in assembly.steps do
    let args ← parameterText step.parameters
    text := text ++ "abbrev " ++ step.name ++ " (" ++ step.arguments ++ " : " ++
      (if step.arguments == "tables" then "Evaluation.ComponentTables F G (signature (F := F) (G := G))"
       else "ProtocolTable (assignment F G) (signature (F := F) (G := G))") ++ ") " ++ args ++
      " : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) " ++ typesText step.outputs ++ ") :=\n  " ++ step.process ++ "\n"
    if step.callee.isSome then
      text := text ++ "abbrev " ++ step.name ++ "Realized " ++ args ++ " := " ++ step.realized ++ "\n" ++
        "theorem " ++ step.name ++ "_binding " ++ args ++ " :\n  " ++
        app step.name ("protocolPrefix1" :: step.parameters.map (·.name)) ++ " = " ++
        app (step.name ++ "Realized") ("(G := G)" :: step.parameters.map (·.name)) ++ " := by\n" ++
        "  unfold " ++ step.name ++ " protocolPrefix1 protocolPrefix0 extendProtocolTableOn\n" ++
        "  rw [invokeProtocol_cons_same]\n  unfold CheckedProtocol.denoteWithOn\n  rw [sourceProtocol0_body]\n  rfl\n"
  text := text ++ "\ndef process (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))\n" ++
    "    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) " ++ parameters ++
    " : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) root.outputs) :=\n  " ++ spine assembly false ++ "\n\n" ++
    "theorem body_binding (tables : Evaluation.ComponentTables F G (signature (F := F) (G := G)))\n" ++
    "    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) " ++ parameters ++ " :\n" ++
    "    sourceBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions tables.toOn 0 protocols {} Occurrence.iterations)\n" ++
    "      (" ++ inputValues ++ " : Values (Component (assignment F G)) root.inputs).get = process tables protocols " ++ inputNames ++ " := by\n  derive_process\n\n" ++
    "abbrev realized " ++ parameters ++ " : PIR.Process (signature (F := F) (G := G)) (Values (Component (assignment F G)) root.outputs) :=\n  let tables := helpers (F := F) (G := G) payload\n  " ++ spine assembly true ++ "\n\n" ++
    "theorem realization_binding " ++ parameters ++ " :\n" ++
    "    process (helpers (F := F) (G := G) payload) protocolPrefix1 " ++ inputNames ++ " = realized (G := G) " ++ inputNames ++ " := by\n" ++
    realizationProof assembly ++ "\n" ++
    "theorem participant_binding " ++ participantParameters ++ " :\n" ++
    "    Occurrence.participant (ringModel F G) imported.program 0 (" ++ participantValues ++ ") =\n" ++
    "      (realized (G := G) " ++ participantNames ++ ").bind (fun out => .done (maskValues 0 root.outputScopes out)) := by\n" ++
    "  change invokeProtocol (Occurrence.table (ringModel F G) payload) root.signature {} 0 (" ++ participantValues ++ ") = _\n" ++
    "  rw [root_lookup_self (F := F) (G := G)]\n  unfold CheckedProtocol.denoteWithOn\n" ++
    "  change (root.body.denote (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn 0 protocolPrefix1 {} Occurrence.iterations)\n" ++
    "    (" ++ participantValues ++ " : Values (Component (assignment F G)) root.inputs).get).bind _ = _\n" ++
    "  rw [root_body, body_binding, realization_binding, ProtocolContext.mapScopes_root]\n\nend " ++ moduleName ++ "\n"
  return text

end ZkcTools.ConstructionBindings.Source
