module

public import ZkcSecurity.Generation.OriginalSecurityBindingsEndpoints

@[expose] public section
set_option autoImplicit false
namespace ZkcSecurity.Generation.OriginalSecurityBindings
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource.Presentation

def honestArgs (binding : Binding) : String :=
  String.intercalate " " (binding.publicPositions.map fun index =>
    match binding.calls.find? (·.claim == index) with
    | some call => input call.raw ++ ".sum"
    | none => input index)
def shapeParameters (binding : Binding) : String :=
  String.intercalate " " (binding.calls.map fun call =>
    "(shape" ++ toString call.occurrence ++ " : PrimitiveLibrary.HasShape " ++ input call.raw ++ " " ++ input binding.count ++ " 1) " ++
    "(bounded" ++ toString call.occurrence ++ " : " ++ input call.raw ++ ".length < indexLimit)")
def shapeArguments (binding : Binding) : String :=
  String.intercalate " " (binding.calls.map fun call => "shape" ++ toString call.occurrence ++ " bounded" ++ toString call.occurrence)

def honestBindings (program : Program) (binding : Binding) (output : Output) : Except String String := do
  let O := output.originalModule
  let B := output.artifactModule
  let S := output.moduleName ++ ".Sources"
  let parameters ← params program binding.producerPositions
  let arguments := args binding.producerPositions
  let shapes := shapeParameters binding
  let shapeArgs := shapeArguments binding
  let fields := [("O", O), ("B", B), ("V", B ++ "ValidatorRoot"), ("P", B ++ "ProducerRoot"),
    ("S", S), ("MODULE", output.moduleName), ("PARAMS", parameters), ("ARGS", arguments),
    ("SHAPES", shapes), ("SHAPEARGS", shapeArgs), ("COUNT", input binding.count),
    ("MAX", toString binding.maximum), ("HONESTARGS", honestArgs binding),
    ("PRODUCERVALUES", sourceValues program binding true true), ("VALIDATORVALUES", sourceValues program binding false true),
    ("PRODUCERREF", toString binding.producerRef), ("PRODUCERARITY", toString binding.producerArity),
    ("BOOLEAN", toString binding.booleanRef), ("TRANSCRIPT", toString binding.transcriptRef)]
  let mut text := preamble output ".Honest" [output.moduleName ++ ".Sources"] ++
    "open ZkcSecurity.Realizations.Sumcheck\nopen OriginalHonest\n" ++
    "variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]\n\n"
  for call in binding.calls do
    text := text ++ render (fields ++ [("N", toString call.occurrence)]) "def routes%N% (handle : Nat) : OriginalHonest.Routes (%P%.routing handle) (%B%.routing handle)\n    %B%.occurrence%N%.protocol handle :=\n  ⟨_, %B%.ProducerCall%N%.routes handle, %B%.occurrence%N%_routes handle⟩\n\n"
  text := text ++ render fields "set_option linter.unusedSimpArgs false in\ntheorem source %PARAMS% (handle : Nat) %SHAPES%\n    (admitted : %COUNT% ≤ %MAX%) (history : Domain.History (uniformCarriers F G)) :\n    Readback RootPost\n      (Original.participant (ringModel F G) %B%.program (%P%.routing handle) 0 %PRODUCERVALUES% ⟨[], history⟩)\n      (Original.participant (ringModel F G) %B%.program (%B%.routing handle) 1 %VALIDATORVALUES% ⟨[], history⟩) := by\n  unfold Original.participant\n  rw [%P%.producer_source %ARGS% %SHAPEARGS%, %O%.participant_binding]\n  simp only [%O%.realized, Original.fold_bind,\n    PIR.Process.bind_assoc, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind]\n"
  text := text ++ "  simp only [" ++ String.intercalate ", " (binding.calls.map fun call =>
    S ++ ".pending" ++ toString call.occurrence ++ "_raw") ++ ", PIR.Process.bind, Zkc.Construction.ArtifactBinding.fold_done]\n"
  let mut history := "history"
  for (call, index) in binding.calls.zipIdx do
    -- A final call with no conjunction has no remaining bind to normalize.
    let continuation := if index + 1 < binding.calls.length || !binding.conjunctions.isEmpty then
      ", PIR.Process.bind" else ""
    text := text ++ render (fields ++ [("N", toString call.occurrence), ("RAW", input call.raw), ("HISTORY", history), ("CONTINUATION", continuation)]) "  apply (OriginalHonest.reduce %B%.program.payload %B%.helper_bodies.sumcheck %B%.claim_bodies %MAX%\n    (%P%.routing handle) (%B%.routing handle) %B%.occurrence%N%.protocol (by change 0 ≠ 1; decide)\n    handle (routes%N% handle) %RAW% %COUNT% shape%N% bounded%N% admitted %HISTORY%).bind\n  intro left%N% right%N% returned%N%\n  obtain ⟨final%N%, original%N%, length%N%, honest%N%, reached%N%, rfl, rfl⟩ := returned%N%\n  have checked%N% := %S%.check%N%_honest (G := G) final%N%\n    (by simpa only [original%N%] using bounded%N%) (by omega)\n  rw [original%N%] at checked%N%\n  erw [checked%N%]\n  simp only [honest%N%, decide_true, Zkc.Construction.ArtifactBinding.fold_done%CONTINUATION%]\n"
    history := "reached" ++ toString call.occurrence
  for step in binding.conjunctions do
    text := text ++ "  rw [" ++ S ++ ".combine_" ++ step.name ++ "]\n  simp only [both, Values.get, Option.bind, Option.map, Bool.true_and, Zkc.Construction.ArtifactBinding.fold_done, PIR.Process.bind]\n"
  text := text ++ "  exact .done ⟨" ++ history ++ ", rfl, rfl⟩\n\n"
  return text ++ render fields "theorem readback %PARAMS% (handle : Nat) %SHAPES%\n    (admitted : %COUNT% ≤ %MAX%) (history : Domain.History (uniformCarriers F G)) :\n    Readback (ActualPost %B%.context %PRODUCERREF% %PRODUCERARITY% %BOOLEAN% %TRANSCRIPT%)\n      (Domain.participant (ringModel F G) %B%.program %B%.context %P%.artifact (%P%.inputs %ARGS% history))\n      (Domain.participant (ringModel F G) %B%.program %B%.context %V%.artifact (%V%.inputs %HONESTARGS% history)) :=\n  Readback.original (%P%.producer %ARGS% handle %SHAPEARGS% history)\n    (%V%.validator %HONESTARGS% handle history)\n    (source %ARGS% handle %SHAPEARGS% admitted history)\n\ntheorem actual %PARAMS% (handle : Nat) %SHAPES%\n    (admitted : %COUNT% ≤ %MAX%) (history : Domain.History (uniformCarriers F G)) :\n    Readback (fun _ result => Domain.acceptanceAt 0 result.values = some true)\n      (Domain.participant (ringModel F G) %B%.program %B%.context %P%.artifact (%P%.inputs %ARGS% history))\n      (Domain.participant (ringModel F G) %B%.program %B%.context %V%.artifact (%V%.inputs %HONESTARGS% history)) :=\n  (readback %ARGS% handle %SHAPEARGS% admitted history).mono (fun _ _ related => related.acceptance)\n\nend %MODULE%.Honest\n"

def completenessBindings (program : Program) (binding : Binding) (output : Output) : Except String String := do
  let mut fields ← endpointFields program binding output
  let all := List.range program.payload.entry.inputs.length
  let changes ← all.mapM fun index => do
    let some ty := program.payload.entry.inputs[index]? | throw "original-security-completeness-input"
    let type ← rawType ty
    let type := type.replace "List F" "List Scalar" |>.replace "F" "Scalar"
    return "  change " ++ (if index == binding.service then "Option " else "") ++ type ++ " at " ++ input index ++ "\n"
  fields := fields ++ [("EXISTS", String.intercalate ", " (all.map input)),
    ("CHANGES", String.join changes), ("ACTUALARGS", args binding.producerPositions),
    ("SERVICE", input binding.service), ("HONESTARGS", honestArgs binding), ("EXISTSARGS", args all)]
  let mut text := preamble output ".Completeness" [output.moduleName ++ ".Honest", output.abiModule,
    output.formulaNamespace.toName.getPrefix.toString ++ "Formula"] ++ render fields "open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField\nopen %SUBJECT% (subject)\nopen %ABI%\nabbrev Scalar := %FIELD%\nabbrev Group := %GROUP%\nlocal instance : ∀ event : Domain.Event subject.domainModel.toCarriers,\n    SampleableType (Domain.Raw event) := %SAMPLING%\n\ntheorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))\n    (honest : subject.HonestInput (abi.pack values)) :\n    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)\n      (Domain.participant subject.domainModel %SUBJECT%.imported.program subject.selection.context\n        %SUBJECT%.selected.artifacts.producer (abi.producer values))\n      (Domain.participant subject.domainModel %SUBJECT%.imported.program subject.selection.context\n        %SUBJECT%.selected.artifacts.validator (abi.validator values)) := by\n  obtain ⟨%EXISTS%, rfl⟩ := data_surjective values\n%CHANGES%  change Readback _\n    (Domain.participant (ringModel Scalar Group) _ _ %P%.artifact (producerInputs %ARGS%))\n    (Domain.participant (ringModel Scalar Group) _ _ %V%.artifact (validatorInputs %ARGS%))\n  prepare_target_readback [Scalar, Group] for subject using honestInput_iff\n    reading (application_read %EXISTSARGS%) evaluating %FORMULA%.equation\n"
  for call in binding.calls do
    text := text ++ render [("N", toString call.occurrence), ("RAW", input call.raw), ("COUNT", input binding.count)] "  have shape%N% : PrimitiveLibrary.HasShape %RAW% %COUNT% 1 := by\n    simp only [PrimitiveLibrary.HasShape, Nat.mod_one, Nat.div_one]\n    have tableSize : %RAW%.length = 2 ^ %COUNT% := by assumption\n    have lengthBound : %RAW%.length < indexLimit := by assumption\n    have dimensionBound : %COUNT% < 64 :=\n      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (tableSize ▸ lengthBound)\n    exact ⟨by decide, dimensionBound, trivial, by simpa only [one_mul] using tableSize⟩\n"
  let shapes := String.intercalate " " (binding.calls.map fun call => "shape" ++ toString call.occurrence ++ " (by assumption)")
  -- Routing is a proof parameter of the compiled construction. The service
  -- option is not replaced with a fabricated present source input.
  text := text ++ "  exact " ++ output.moduleName ++ ".Honest.actual " ++ args binding.producerPositions ++
    " 0 " ++ shapes ++ " (by assumption) (initialHistory " ++ honestArgs binding ++ ")\n\n"
  return text ++ render fields "theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=\n  Readback.perfect_abi subject abi %FORMULA%.nonvacuous abi_readback\n\nend %MODULE%.Completeness\n"

end ZkcSecurity.Generation.OriginalSecurityBindings
