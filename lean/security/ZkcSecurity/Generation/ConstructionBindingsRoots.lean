module

public import ZkcSecurity.Generation.ConstructionBindings
public import ZkcTools.ConstructionBindings.Source
public import ZkcExamples.Structured.OriginalSumcheckReduce

@[expose] public section
set_option autoImplicit false
namespace ZkcSecurity.Generation.ConstructionBindingsRoots
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcTools.ConstructionBindings ZkcTools.StructuredSource.Presentation
open ZkcSecurity.Generation.ConstructionBindings

structure Symbol where
  value : String
  term : String
  type : String

abbrev Parameters := List (String × String)
def params (values : Parameters) : String :=
  " ".intercalate (values.map fun (name, type) => "(" ++ name ++ " : " ++ type ++ ")")
def arguments (values : Parameters) : String := " ".intercalate (values.map Prod.fst)
def holes (values : Parameters) : String := " ".intercalate (values.map fun _ => "_")
def env (values : List Symbol) : String := listText (values.map (·.value))
def data (ty : Ty) (term : String) : Except String Symbol := do
  let (kind, type) ← match ty with
    | .vector field => pure (".vector " ++ quoted field, "List F")
    | .field field => pure (".field " ++ quoted field, "F")
    | .index => pure (".index", "Nat")
    | .boolean => pure (".boolean", "Bool")
    | _ => throw "construction-binding-root-data-type"
  return ⟨".data (" ++ kind ++ " " ++ term ++ ")", term, type⟩
def history (name : String) : Symbol :=
  ⟨".transcript context.suite " ++ name, name, "Domain.History (uniformCarriers F G)"⟩
def symbolAt (frame : List Symbol) (reference : Nat) : Except String Symbol :=
  match frame[reference]? with | some value => pure value | none => throw "construction-binding-root-reference"
def helper (program : Program) (name : String) : Except String Helper := do
  return (← unique "root-helper" (program.payload.definitions.filter (·.name == name))).helper

def source (program : Program) (artifact : Participant) (layout : Layout)
    (role : Nat) (moduleName bindingModule originalModule producerSource : String) : Except String String := do
  unless role == 0 || role == 1 do throw "construction-binding-root-role"
  let producer := role == 0
  let root := program.payload.entry
  let physicalInputs := root.inputs.zipIdx.filter fun (_, index) =>
    (root.inputScopes[index]?.getD []).contains role &&
    match root.inputs[index]? with | some (.service _) => false | _ => true
  let inputParams ← physicalInputs.mapM fun (ty, index) => do
    let symbol ← data ty ("input" ++ toString index)
    return (symbol.term, symbol.type)
  let indices := root.inputs.zipIdx.filterMap fun (ty, index) => if ty == .index then some index else none
  let countIndex ← unique "root-count" indices
  let count := "input" ++ toString countIndex
  let vectors := physicalInputs.filterMap fun (ty, index) => match ty with | .vector _ => some index | _ => none
  let shapeParams := if producer then vectors.flatMap fun index =>
    [("shape" ++ toString index, "PrimitiveLibrary.HasShape input" ++ toString index ++ " " ++ count ++ " 1"),
     ("bounded" ++ toString index, "input" ++ toString index ++ ".length < indexLimit")] else []
  let originalInputs := root.inputs.zipIdx.map fun (_, index) =>
    if physicalInputs.any (fun pair => pair.2 == index) then "(some input" ++ toString index ++ ")"
    else if !producer && index == layout.context.service then "(some handle)" else "none"
  let originalValues := valuesText originalInputs
  let mut frame ← physicalInputs.mapM fun (ty, index) => data ty ("input" ++ toString index)
  frame := frame ++ [history "history"]
  unless frame.length == artifact.inputs.length do throw "construction-binding-root-input-abi"
  let inputEnv := env frame
  let mut text := preamble moduleName [bindingModule, originalModule, producerSource,
    "ZkcSecurity.Realizations.Sumcheck.ArtifactRoot", "ZkcExamples.Structured.NormalFormSteps",
    "Zkc.Construction.OriginalCorrespondence"] ++
    "attribute [local irreducible] Zkc.Construction.Original.fold ZkcExamples.Structured.OriginalSumcheckLibrary.reduce Zkc.Construction.Domain.View.loop Zkc.Source.Participant.owned Zkc.Source.Structured.invoke Zkc.Construction.Domain.callHelper\n" ++
    "open ZkcSecurity.Realizations.Sumcheck.ArtifactRoot\n" ++
    "abbrev program := " ++ bindingModule ++ ".program\nabbrev context := " ++ bindingModule ++ ".context\n" ++
    "abbrev artifact := " ++ bindingModule ++ (if producer then ".producerArtifact" else ".validatorArtifact") ++ "\n" ++
    "abbrev routing := " ++ bindingModule ++ (if producer then ".ProducerCall0.routing" else ".routing") ++ "\n" ++
    "abbrev RootReturns := " ++ (if producer then "ProducerReturns" else "ValidatorReturns") ++ " (F := F) (G := G)\n" ++
    "def inputs " ++ params inputParams ++ " (history : Domain.History (uniformCarriers F G)) : Domain.Environment (uniformCarriers F G) :=\n  " ++ inputEnv ++ "\n\n"
  if producer then text := text ++ "open ZkcSecurity.Realizations.Sumcheck.OriginalProducer\n"
  let mut dynamic : Parameters := []
  let mut rules : List String := []
  let mut captures : List String := []
  let mut localRules := ""
  let mut sourceCalls : List String := []
  let mut callIndex := 0
  let mut helperIndex := 0
  let mut mathLaws : List String := []
  let mut sourceLaws : List String := []
  for (instruction, instructionIndex) in artifact.instructions.zipIdx do
    let read ← instruction.operands.mapM (symbolAt frame)
    let mut results : List Symbol := []
    match instruction.operation, read with
    | .calculate (.indexConstant value), [] => results := [← data .index (toString value)]
    | .calculate (.booleanConstant value), [] => results := [← data .boolean (boolText value)]
    | .calculate .indexEqual, [left, right] =>
      results := [← data .boolean (if left.term == right.term then "true" else "(decide (" ++ left.term ++ " = " ++ right.term ++ "))")]
    | .calculate .booleanEqual, [left, right] =>
      results := [← data .boolean (if left.term == right.term then "true" else "(" ++ left.term ++ " == " ++ right.term ++ ")")]
    | .calculate .booleanAnd, [left, right] => results := [← data .boolean ("(" ++ left.term ++ " && " ++ right.term ++ ")")]
    | .calculate .booleanNotEqual, [left, right] => results := [← data .boolean ("(" ++ left.term ++ " != " ++ right.term ++ ")")]
    | .guard _, [_] => pure ()
    | .call name, _ =>
      let selected ← helper program name
      if selected == SumcheckHelperBodies.emptyHelper then
        results := [← data (.vector "bls12-381.fr") "[]"]
        mathLaws := mathLaws ++ ["ZkcSecurity.Realizations.Sumcheck.DomainHelpers.empty program " ++ bindingModule ++ ".helper_bodies.sumcheck"]
      else if selected == MapFirstBodies.tableHelper then
        let [raw, dimension, width] := read | throw "construction-binding-table-abi"
        unless width.term == "1" && dimension.term == count do throw "construction-binding-table-domain"
        let rawIndex ← unique "table-input" (vectors.filter fun index => raw.term == "input" ++ toString index)
        let shape := "shape" ++ toString rawIndex
        let bounded := "bounded" ++ toString rawIndex
        results := read
        mathLaws := mathLaws ++ ["ZkcSecurity.Realizations.Sumcheck.DomainHelpers.table program " ++ bindingModule ++ ".helper_bodies.sumcheck " ++ raw.term ++ " " ++ count ++ " 1 " ++ shape ++ " " ++ bounded ++ " countBound (by decide +kernel)"]
        sourceLaws := sourceLaws ++ ["ZkcExamples.Structured.OriginalSumcheckProducerCalls.table_owned program.payload " ++ bindingModule ++ ".helper_bodies.sumcheck " ++ raw.term ++ " " ++ count ++ " " ++ shape ++ " " ++ bounded]
      else if selected == MapFirstBodies.widthHelper then
        let [_, _, width] := read | throw "construction-binding-width-abi"
        results := [width]
      else if selected == MapFirstBodies.variablesHelper then
        let [_, dimension, _] := read | throw "construction-binding-variables-abi"
        results := [dimension]
      else if selected == MapFirstBodies.lessHelper then
        let [left, right] := read | throw "construction-binding-less-abi"
        unless left.term == count && right.term == count do throw "construction-binding-less-domain"
        results := [← data .boolean "false"]
        mathLaws := mathLaws ++ ["ZkcSecurity.Realizations.Sumcheck.DomainHelpers.less program " ++ bindingModule ++ ".helper_bodies.sumcheck " ++ count ++ " " ++ count ++ " countBound countBound"]
      else if selected == SumcheckHelperBodies.checkHelper && !producer then
        let [entries, point, scalar] := read | throw "construction-binding-check-abi"
        let name := "terminalRule" ++ toString helperIndex
        localRules := localRules ++ "  have " ++ name ++ " " ++ params dynamic ++ " :=\n    terminal (F := F) (G := G) program " ++ bindingModule ++ ".helper_bodies (routing handle) ⟨[], " ++ (← symbolAt frame (frame.length - 1)).term ++ "⟩ 1\n      " ++ entries.term ++ " " ++ point.term ++ " " ++ scalar.term ++ " " ++ env frame ++ " " ++ natsText instruction.operands ++ " rfl\n"
        rules := rules ++ [(if instructionIndex + 1 == artifact.instructions.length then "finish (" else "Original.Simulation.bind (") ++ name ++ " " ++ holes dynamic ++ ")"]
        let checked := "checked" ++ toString helperIndex
        results := [← data .boolean checked]
        dynamic := dynamic ++ [(checked, "Bool")]
        helperIndex := helperIndex + 1
      else throw "construction-binding-root-helper-law"
    | .loop _ _ _, _ =>
      let loop ← unique "root-loop" (layout.loops.filter (·.instruction == instructionIndex))
      let capture := "capture" ++ toString callIndex
      let occurrence := bindingModule ++ "." ++ occurrenceName callIndex
      let callbackScope := bindingModule ++ (if producer then ".ProducerCall" else ".ValidatorCall") ++ toString callIndex
      let callback := callbackScope ++ ".callback"
      let outputs := callbackScope ++ ".outputs"
      localRules := localRules ++ "  let " ++ capture ++ " " ++ params dynamic ++ " : Domain.Environment (uniformCarriers F G) := " ++ env frame ++ "\n"
      captures := captures ++ [capture]
      let captureExpr := app capture (dynamic.map Prod.fst)
      let initial ← loop.initial.mapM (symbolAt frame)
      let name := "loopRule" ++ toString callIndex
      let suffix := toString callIndex
      if producer then
        let [raw, dimension, width, _, reached] := initial | throw "construction-binding-producer-loop-abi"
        unless dimension.term == count && width.term == "1" do throw "construction-binding-producer-loop-domain"
        let rawIndex ← unique "loop-input" (vectors.filter fun index => raw.term == "input" ++ toString index)
        localRules := localRules ++ "  have " ++ name ++ " " ++ params dynamic ++ " :=\n    (" ++ callback ++ " (F := F) (G := G) handle).reduce program " ++ bindingModule ++ ".helper_bodies.sumcheck (routing handle) " ++ occurrence ++ " (by decide +kernel)\n      context " ++ outputs ++ " " ++ toString loop.offset ++ " " ++ toString loop.maximum ++ " handle _ " ++ captureExpr ++ " rfl " ++ raw.term ++ " " ++ dimension.term ++ " " ++ count ++ " " ++ toString loop.count ++ " " ++ natsText loop.initial ++ "\n      shape" ++ toString rawIndex ++ " bounded" ++ toString rawIndex ++ " countBound (by omega) " ++ reached.term ++ " rfl rfl\n"
        results := [← data (.vector "bls12-381.fr") ("raw" ++ suffix), ← data .index "0", ← data .index ("width" ++ suffix), ← data (.vector "bls12-381.fr") ("point" ++ suffix), history ("history" ++ suffix)]
        dynamic := dynamic ++ [("raw" ++ suffix, "List F"), ("width" ++ suffix, "Nat"), ("point" ++ suffix, "List F"), ("history" ++ suffix, (history "").type)]
      else
        let [_, scalar, reached] := initial | throw "construction-binding-validator-loop-abi"
        localRules := localRules ++ "  have " ++ name ++ " " ++ params dynamic ++ " :=\n    (" ++ callback ++ " (F := F) (G := G) handle).reduce program " ++ bindingModule ++ ".verifier_bodies (routing handle) " ++ occurrence ++ " (by decide +kernel)\n      context " ++ outputs ++ " " ++ toString loop.offset ++ " " ++ toString loop.maximum ++ " handle _ " ++ captureExpr ++ " rfl " ++ count ++ " " ++ toString loop.count ++ " " ++ natsText loop.initial ++ " " ++ scalar.term ++ " " ++ reached.term ++ " rfl rfl\n"
        results := [← data (.vector "bls12-381.fr") ("point" ++ suffix), ← data (.field "bls12-381.fr") ("scalar" ++ suffix), history ("history" ++ suffix)]
        dynamic := dynamic ++ [("point" ++ suffix, "List F"), ("scalar" ++ suffix, "F"), ("history" ++ suffix, (history "").type)]
      let earlier := if producer then dynamic.length - 4 else dynamic.length - 3
      rules := rules ++ ["Original.Simulation.bind (" ++ name ++ " " ++ holes (dynamic.take earlier) ++ ")"]
      if producer then
        let [raw, _, _, _, _] := initial | throw "construction-binding-producer-loop-abi"
        sourceCalls := sourceCalls ++ ["OriginalSumcheckLibrary.reduce program.payload " ++ toString loop.maximum ++ " " ++ occurrence ++ ".protocol 0 []\n    (.cons (some " ++ raw.term ++ ") (.cons (some " ++ count ++ ") (.cons (some 1) (.cons none (.cons (some " ++ count ++ ") (.cons none .nil))))))"]
      callIndex := callIndex + 1
    | _, _ => throw ("construction-binding-root-operation: " ++ toString instructionIndex ++ " " ++ reprStr instruction.operation)
    unless results.length == instruction.results.length do throw "construction-binding-root-result-abi"
    frame := frame ++ results
  let constructed := "ZkcExamples.Structured.Generated.Constructed." ++ bindingModule.toName.getString! ++ (if producer then "Producer" else "Validator")
  let sourceModule := if producer then producerSource else originalModule
  let (_, sourceAssembly) ← if producer then ZkcTools.ConstructionBindings.Source.assembly program else do
    let root := program.payload.entry
    let protocols := program.payload.protocols.dropLast
    let keys := protocols.map fun definition => NormalForm.CalleeKey.mk definition.signature 1 (Bindings.optionalPattern definition.inputs) []
    let sig : NormalForm.Signature := ⟨[], false, true, program.payload.definitions.map (·.helper), keys⟩
    let form ← NormalForm.normalize sig root.body 1 root.roles.length (Bindings.optionalPattern root.inputs)
    let binders := root.inputs.zipIdx.map fun (ty, index) => ZkcTools.StructuredSource.OriginalRoot.Binder.mk ("input" ++ toString index) (.component ty) index
    pure (binders, ← ZkcTools.StructuredSource.OriginalRoot.assemble program keys root.inputs binders form 0)
  let sourceDefinitions := [sourceModule ++ ".realized"] ++ sourceAssembly.steps.flatMap fun step =>
    [sourceModule ++ "." ++ step.name] ++ if step.callee.isSome then [sourceModule ++ "." ++ step.name ++ "Realized"] else []
  let selectedHelpers := (sourceAssembly.steps.filterMap (·.helper)).eraseDups
  let mut helperIdentities := []
  for selected in selectedHelpers do
    let index ← ZkcTools.StructuredSource.OriginalRoot.uniqueIndex (program.payload.definitions.map (·.helper)) selected
    let name := "sourceHelper" ++ toString index ++ "_identity"
    text := text ++ "theorem " ++ name ++ " : " ++ originalModule ++ ".sourceHelper" ++ toString index ++
      ".helper = " ++ literal selected ++ " := by kernel_rfl\n\n"
    helperIdentities := helperIdentities ++ [name]
  let both := sourceAssembly.steps.filterMap fun step => step.helper.filter (·.kind == .math)
  let mut booleanLaws := []
  for selected in both.eraseDups do
    unless selected.inputs == [.boolean, .boolean] && selected.outputs == [.boolean] do
      throw "construction-binding-root-math-abi"
    let index ← ZkcTools.StructuredSource.OriginalRoot.uniqueIndex (program.payload.definitions.map (·.helper)) selected
    let selectedName := originalModule ++ ".sourceHelper" ++ toString index
    let sourceName := originalModule.replace ".Original." ".Bindings." ++ "Inputs.helper" ++ toString index ++ "Body"
    let name := "mathHelper" ++ toString index
    text := text ++ "theorem " ++ name ++ " (left right : Option Bool) :\n    invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) program.payload).components " ++ selectedName ++ ".helper (.cons left (.cons right .nil)) =\n      .done (.cons (left.bind fun x => right.map fun y => x && y) .nil) := by\n" ++
      "  have association : BodyIn program.payload.definitions " ++ selectedName ++ ".helper " ++ sourceName ++ " := by bind_structured_bodies\n" ++
      "  rw [← (OriginalSumcheckLibrary.helpers_lift program.payload).components, SumcheckVerifierHelpers.component_body_plain program.payload " ++ selectedName ++ ".helper " ++ sourceName ++ " association]\n  cases left <;> cases right <;> rfl\n\n"
    booleanLaws := booleanLaws ++ [name]
  if !producer then text := text ++ "theorem mask_outputs (site : String) (point : List F) (scalar : F) :\n    (show Values (Component (assignment F G)) SumcheckVerifierBodies.reduceOutputs from\n    maskValues ((({} : ProtocolContext).enter site [0, 1]).roles 1)\n      ((({} : ProtocolContext).enter site [0, 1]).mapScopes " ++ originalModule ++ ".sourceProtocol0.outputScopes)\n      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil))))))) =\n      (.cons none (.cons none (.cons none (.cons none (.cons (some point) (.cons (some scalar) .nil)))))) := by kernel_rfl\n\n"
  let rootParams := params inputParams ++ " " ++ params shapeParams
  let normalSource := sourceDefinitions ++ helperIdentities ++ ["ZkcExamples.Structured.OriginalSumcheckProducerCalls.realizeProducerCall", "ZkcExamples.Structured.OriginalSumcheckCalls.realizeCall"] ++ booleanLaws ++ sourceLaws
  if producer then
    let simplified := sourceCalls.foldr (fun call rest => "(" ++ call ++ ").bind fun _ =>\n  " ++ rest) ".done (.cons none .nil)"
    text := text ++ "theorem producer_source " ++ rootParams ++ " :\n    Occurrence.participant (ringModel F G) program 0 (" ++ originalValues ++ ") =\n  " ++ simplified ++ " := by\n  rw [" ++ sourceModule ++ ".participant_binding]\n  simp only [" ++ ", ".intercalate (sourceDefinitions ++ ["ZkcExamples.Structured.OriginalSumcheckProducerCalls.realizeProducerCall"]) ++ "]\n" ++
      String.join (sourceLaws.map fun law => "  erw [" ++ law ++ "]\n  dsimp only [Values.get, PIR.Process.bind]\n") ++
      "  simp only [" ++ ", ".intercalate (booleanLaws ++ ["PIR.Process.bind", "PIR.Process.bind_assoc"]) ++ "]\n  rfl\n\n"
  let returnArgs ← if producer then do
    let [reference] := artifact.returned | throw "construction-binding-producer-return-abi"
    pure (toString reference ++ " " ++ toString layout.arity)
    else do
    let [boolean, transcript] := artifact.returned | throw "construction-binding-validator-return-abi"
    pure (toString boolean ++ " " ++ toString transcript)
  text := text ++ "def " ++ (if producer then "producer" else "validator") ++ " " ++ params inputParams ++ " (handle : Nat) " ++ params shapeParams ++ " (history : Domain.History (uniformCarriers F G)) :\n" ++
    (if producer then
      "    Original.Producer (model := ringModel F G) (program := program) (routing handle) artifact\n" ++
      "      (inputs " ++ arguments inputParams ++ " history) (" ++ originalValues ++ ") ⟨[], history⟩\n" ++
      "      (RootReturns context " ++ returnArgs ++ ")\n" ++
      "      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs " ++ arguments inputParams ++ " history) frame) := by\n" ++
      "  change Original.Simulation _ _ _ _\n"
    else
      "    Original.Simulation (RootReturns context " ++ returnArgs ++ ")\n      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures (inputs " ++ arguments inputParams ++ " history) frame)\n      (Original.participant (ringModel F G) program (routing handle) " ++ toString role ++ " (" ++ originalValues ++ ") ⟨[], history⟩)\n" ++
      "      (Domain.participant (ringModel F G) program context artifact (inputs " ++ arguments inputParams ++ " history)) := by\n")
  if producer then text := text ++ "  have countBound : " ++ count ++ " < indexLimit := lt_trans shape" ++ toString (← unique "root-shape" (vectors.take 1)) ++ ".2.1 (by decide +kernel)\n"
  text := text ++ localRules ++ "  unfold Original.participant\n  rw [" ++ (if producer then "producer_source " ++ arguments inputParams ++ " " ++ arguments shapeParams else originalModule ++ ".participant_binding") ++ "]\n" ++
    "  rw [" ++ constructed ++ ".participant_eq]\n  unfold_component_bodies [" ++ constructed ++ ".view]\n" ++
    "  derive_artifact_binding [" ++ ", ".intercalate rules ++ "]\n    normalizing (\n"
  text := text ++ (if producer then
    "      try (rename_i source final returned; change ReduceReturns _ _ _ _ _ at returned; apply Classical.choice; obtain ⟨nextRaw, width, point, reached, rfl, rfl, nextShape, nextBound⟩ := returned; refine ⟨?_⟩)\n"
    else "      try (rename_i source final returned; change ReduceReturns _ _ _ _ at returned; apply Classical.choice; obtain ⟨point, scalar, reached, rfl, rfl⟩ := returned; refine ⟨?_⟩)\n      try (rename_i source final returned; change BooleanReturns _ _ _ _ at returned; apply Classical.choice; obtain ⟨value, rfl, rfl⟩ := returned; refine ⟨?_⟩)\n")
  text := text ++ "      try simp only [" ++ ", ".intercalate normalSource ++ (if producer then "" else ", mask_outputs") ++ ", Values.get, Values.present, SumcheckVerifierBodies.reduceReturnValues, SumcheckVerifierLaws.embedV, SumcheckRoundNormalForms.verifierState, Original.fold_bind, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind, PIR.Process.bind_assoc]\n" ++
    "      try normalize_artifact_operations [" ++ ", ".intercalate (mathLaws.eraseDups ++ ["boolean_and"]) ++ "] unfolding [" ++ constructed ++ ".inputSorts, " ++ constructed ++ ".outputSorts, " ++ constructed ++ ".returned, inputs, " ++ ", ".intercalate (captures ++ ["carried", "context", bindingModule ++ ".context"]) ++ "]\n" ++
    "      try simp only [Nat.lt_irrefl, decide_false, Nat.sub_self, List.cons_append, List.nil_append, List.getElem?_cons_zero, List.getElem?_cons_succ, PIR.Process.bind, PIR.Process.bind_assoc]\n      try dsimp only\n      change Original.Simulation _ _ _ _)\n" ++
    "    solving (first\n"
  text := text ++ (if producer then
    "      | (rename_i source final returned; change ReduceReturns _ _ _ _ _ at returned; obtain ⟨nextRaw, width, point, reached, sourceEq, frameEq, nextShape, nextBound⟩ := returned; rw [frameEq]; simp [Zkc.Construction.ArtifactBinding.Captures, inputs, " ++ ", ".intercalate captures ++ ", carried, context, " ++ bindingModule ++ ".context, List.append_assoc, List.take_append])\n"
    else "      | (rename_i source final returned; change ReduceReturns _ _ _ _ at returned; obtain ⟨point, scalar, reached, sourceEq, frameEq⟩ := returned; rw [frameEq]; simp [Zkc.Construction.ArtifactBinding.Captures, inputs, " ++ ", ".intercalate captures ++ ", carried, context, " ++ bindingModule ++ ".context, List.append_assoc, List.take_append])\n      | (rename_i source final returned; change BooleanReturns _ _ _ _ at returned; obtain ⟨value, sourceEq, frameEq⟩ := returned; rw [frameEq]; simp [Zkc.Construction.ArtifactBinding.Captures, inputs, " ++ ", ".intercalate captures ++ ", carried, context, " ++ bindingModule ++ ".context, List.append_assoc, List.take_append])\n")
  text := text ++ "      | rfl\n      | solve | simp_all [Zkc.Construction.ArtifactBinding.Captures, inputs, " ++ ", ".intercalate captures ++ ", carried, context, " ++ bindingModule ++ ".context, List.append_assoc, List.take_append]\n" ++
    "      | (intro process frame retained; apply Zkc.Construction.ArtifactBinding.captures_trans (inner := retained); simp [Zkc.Construction.ArtifactBinding.Captures, inputs, " ++ ", ".intercalate captures ++ ", carried, context, " ++ bindingModule ++ ".context, List.append_assoc, List.take_append])\n" ++
    "      | (unfold RootReturns " ++ (if producer then "ProducerReturns; " else "ValidatorReturns; refine ⟨_, rfl, ?_⟩; ") ++ "simp [inputs, " ++ ", ".intercalate captures ++ ", carried, context, " ++ bindingModule ++ ".context, List.cons_append, List.nil_append]))\n\nend " ++ moduleName ++ "\n"
  return if producer then text.replace ", carried," ", ZkcSecurity.Realizations.Sumcheck.OriginalProducer.carried," else text

end ZkcSecurity.Generation.ConstructionBindingsRoots
