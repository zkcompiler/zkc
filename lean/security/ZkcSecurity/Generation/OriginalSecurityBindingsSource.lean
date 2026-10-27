module

public import ZkcSecurity.Generation.OriginalSecurityBindings

@[expose] public section
set_option autoImplicit false
namespace ZkcSecurity.Generation.OriginalSecurityBindings
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource.Presentation
open ZkcTools.StructuredSource.OriginalRoot

def render (fields : List (String × String)) (template : String) : String :=
  fields.foldl (fun text field => text.replace ("%" ++ field.1 ++ "%") field.2) template

def preamble (output : Output) (suffix : String) (imports : List String) : String :=
  "module\n\n" ++ String.join (imports.map fun name => "public import " ++ name ++ "\n") ++
    "\n@[expose] public section\nset_option autoImplicit false\nset_option maxRecDepth 50000\n" ++
    "set_option maxHeartbeats 8000000\nset_option backward.isDefEq.respectTransparency false\n" ++
    "noncomputable section\nnamespace " ++ output.moduleName ++ suffix ++ "\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured\n" ++
    "open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent\n" ++
    "open ZkcSecurity.Realizations.Sumcheck\nopen ZkcSecurity.Realizations.Sumcheck.OriginalRaw\n" ++
    "open ZkcSecurity.Realizations.Sumcheck.OriginalRoot\n"

def sourceRoot (binding : Binding) (output : Output) : Except String String := do
  if binding.conjunction.isSome then
    return "sourceTwoRoots " ++ toString binding.maximum ++ " " ++ String.intercalate " " (binding.calls.map fun call =>
      "⟨" ++ output.artifactModule ++ ".occurrence" ++ toString call.occurrence ++ ".protocol, handle⟩") ++ " " ++
      args (binding.calls.map (·.raw) ++ binding.calls.map (·.claim)) ++ " " ++ input binding.count
  else
    let call ← one "single-call" binding.calls
    return "sourceRoot " ++ toString binding.maximum ++ " ⟨" ++ output.artifactModule ++ ".occurrence0.protocol, handle⟩ " ++
      args [call.raw, call.claim, binding.count]

def presentedRoot (binding : Binding) : String :=
  (if binding.conjunction.isSome then "twoRoots " else "root ") ++ toString binding.maximum ++ " " ++
    String.intercalate " " (binding.calls.map fun call => "schedule" ++ toString call.occurrence) ++ " " ++
    args (binding.calls.map (·.raw) ++ binding.calls.map (·.claim)) ++ " " ++ input binding.count ++ " ⟨[], history⟩"

def sourceBindings (program : Program) (binding : Binding) (output : Output) : Except String String := do
  let O := output.originalModule
  let B := output.artifactModule
  let V := B ++ "ValidatorRoot"
  let P := B ++ "ProducerRoot"
  let parameters ← params program binding.publicPositions
  let arguments := args binding.publicPositions
  let fields := [("O", O), ("B", B), ("V", V), ("P", P), ("PARAMS", parameters),
    ("ARGS", arguments), ("VALUES", sourceValues program binding false false),
    ("MAX", toString binding.maximum)]
  let mut text := preamble output ".Sources" [O, V, P,
    "ZkcSecurity.Realizations.Sumcheck.OriginalRoot"] ++
    "variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]\n\n" ++
    "abbrev program := " ++ B ++ ".program\nabbrev payload := program.payload\nabbrev routing := " ++ B ++ ".routing\n" ++
    "abbrev context := " ++ B ++ ".context\n" ++
    "theorem terminal_bodies : OriginalSumcheckLibrary.TerminalBodies payload.definitions :=\n  " ++ B ++ ".helper_bodies.terminal\n\n"
  text := text ++ "theorem source_root_association : " ++ O ++ ".root.signature = " ++ B ++ ".program.payload.entry.signature := by kernel_rfl\n\n"
  let contexts := listText (binding.calls.map fun call => O ++ "." ++ call.call.name.replace "step" "callContext")
  let occurrences := listText (binding.calls.map fun call => B ++ ".occurrence" ++ toString call.occurrence ++ ".protocol")
  text := text ++ "theorem nominal_order : " ++ contexts ++ " = " ++ occurrences ++ " := by kernel_rfl\n\n"
  for call in binding.calls do
    let some helper := call.check.helper | throw "original-security-check-helper"
    let helperIndex ← uniqueIndex (program.payload.definitions.map (·.helper)) helper
    text := text ++ "theorem check" ++ toString call.occurrence ++ "_helper : " ++ O ++ ".sourceHelper" ++ toString helperIndex ++ ".helper = SumcheckHelperBodies.checkHelper := by kernel_rfl\n\n"
  for call in binding.calls do
    text := text ++ render (fields ++ [("N", toString call.occurrence), ("CALL", call.call.name), ("CHECK", call.check.name)]) "def schedule%N% := schedule %B%.occurrence%N% context\n theorem routes%N% (handle : Nat) : OriginalSecurity.Routes (routing handle)\n    ⟨%B%.occurrence%N%.protocol, handle⟩ schedule%N% [] :=\n  routes (routing handle) %B%.occurrence%N% handle (%B%.occurrence%N%_routes handle)\n\ntheorem call%N%_raw (scalar : F) (count handle : Nat) :\n    %O%.%CALL%Realized (G := G) (some scalar) (some count) (some handle) =\n      if count ≤ %MAX% then\n        (run (G := G) ⟨%B%.occurrence%N%.protocol, handle⟩ (List.range count) ⟨[], scalar⟩).bind\n          (fun result => .done (output result))\n      else .halt .refused := by\n  change verifierCall payload %MAX% %B%.occurrence%N%.protocol %O%.reduceDefinition.outputScopes scalar count handle = _\n  rw [call_raw payload %B%.verifier_bodies %MAX% ⟨%B%.occurrence%N%.protocol, handle⟩ (by change 0 ≠ 1; decide)]\n  split\n  · apply congrArg (PIR.Process.bind _)\n    funext result\n    exact congrArg PIR.Process.done (by kernel_rfl)\n  · rfl\n\ntheorem check%N%_raw (raw : List F) (state : State F) :\n    %O%.%CHECK% (OriginalSumcheckLibrary.helpers payload) (some raw) (output (G := G) state) =\n      terminal raw state.point state.scalar := by\n  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)\n    (.cons (some raw) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _\n  exact source_terminal payload terminal_bodies 1 raw state.point state.scalar\n\ntheorem checked%N% (raw : List F) (scalar : F) (count handle : Nat) :\n    (%O%.%CALL%Realized (G := G) (some scalar) (some count) (some handle)).bind\n      (%O%.%CHECK% (OriginalSumcheckLibrary.helpers payload) (some raw)) =\n      sourceRoot %MAX% ⟨%B%.occurrence%N%.protocol, handle⟩ raw scalar count := by\n  rw [call%N%_raw]\n  unfold sourceRoot\n  split\n  · simp only [PIR.Process.bind_assoc, PIR.Process.bind]\n    apply congrArg (PIR.Process.bind _)\n    funext state\n    exact check%N%_raw raw state\n  · rfl\n\n"
  for call in binding.calls do
    text := text ++ render (fields ++ [("N", toString call.occurrence), ("CALL", call.call.name), ("CHECK", call.check.name)]) "theorem call%N%_binding (scalar : F) (count handle : Nat) :\n    %O%.%CALL%Realized (G := G) (some scalar) (some count) (some handle) =\n      verifierCall payload %MAX% %B%.occurrence%N%.protocol %O%.reduceDefinition.outputScopes scalar count handle := by rfl\n\ntheorem check%N%_honest (state : OriginalHonest.MathState F 0)\n    (bounded : state.original.length < indexLimit) (pointBound : state.point.length < 64) :\n    %O%.%CHECK% (OriginalSumcheckLibrary.helpers payload) (some state.original)\n      (maskValues (%B%.occurrence%N%.protocol.roles 1)\n        (%B%.occurrence%N%.protocol.mapScopes %O%.reduceDefinition.outputScopes)\n        (SumcheckVerifierBodies.reduceReturnValues (OriginalHonest.verifierValues (G := G) state))) =\n      .done (.cons (some (decide (state.entries.sum = state.scalar))) .nil) := by\n  change Participant.owned 1 1 (invoke (OriginalSumcheckLibrary.helpers payload).closed SumcheckHelperBodies.checkHelper)\n    (.cons (some state.original) (.cons (some state.point) (.cons (some state.scalar) .nil))) = _\n  exact honest_check payload terminal_bodies state bounded pointBound\n\n"
  if let some step := binding.conjunction then
    let some helper := step.helper | throw "original-security-conjunction"
    let helperIndex ← uniqueIndex (program.payload.definitions.map (·.helper)) helper
    text := text ++ render (fields ++ [("COMBINE", step.name), ("HELPER", toString helperIndex)]) "theorem combine (left right : Values (Component (assignment F G)) [.boolean]) :\n    %O%.%COMBINE% (OriginalSumcheckLibrary.helpers payload) left right = both left right := by\n  cases left with\n  | cons a left =>\n    cases left\n    cases right with\n    | cons b right =>\n      cases right\n      change invoke (OriginalSumcheckLibrary.helpers payload).components %O%.terminalHelper\n        (.cons a (.cons b .nil)) = _\n      exact %V%.mathHelper%HELPER% a b\n\n"
  text := text ++ render (fields ++ [("ROOT", ← sourceRoot binding output)]) "theorem source_root %PARAMS% (handle : Nat) :\n    Occurrence.participant (ringModel F G) program 1 %VALUES% =\n      %ROOT% := by\n  rw [%O%.participant_binding]\n"
  if binding.conjunction.isSome then
    let [left, right] := binding.calls | throw "original-security-conjunction-calls"
    text := text ++ "  unfold " ++ O ++ ".realized sourceTwoRoots\n" ++
      "  rw [← checked0 " ++ args [left.raw, left.claim, binding.count] ++ " handle, ← checked1 " ++
      args [right.raw, right.claim, binding.count] ++ " handle]\n" ++
      "  simp only [PIR.Process.bind_assoc, combine]\n\n"
  else
    let call ← one "single-call" binding.calls
    text := text ++ "  exact checked0 " ++ args [call.raw, call.claim, binding.count] ++ " handle\n\n"
  let contexts := String.intercalate " " (binding.calls.map fun call => "⟨" ++ B ++ ".occurrence" ++ toString call.occurrence ++ ".protocol, handle⟩")
  let schedules := String.intercalate " " (binding.calls.map fun call => "schedule" ++ toString call.occurrence)
  let routes := String.intercalate " " (binding.calls.map fun call => "(routes" ++ toString call.occurrence ++ " handle)")
  let bridge := (if binding.conjunction.isSome then "twoRoots_bridge" else "root_bridge") ++ " (routing handle) " ++
    contexts ++ " " ++ schedules ++ " " ++ toString binding.maximum ++ " " ++
    args (binding.calls.map (·.raw) ++ binding.calls.map (·.claim)) ++ " " ++ input binding.count ++ " ⟨[], history⟩ " ++ routes
  text := text ++ render (fields ++ [("PRESENTED", presentedRoot binding), ("BRIDGE", bridge), ("MODULE", output.moduleName)]) "def presented %PARAMS% (history : Domain.History (uniformCarriers F G)) :=\n  %PRESENTED%\n\ntheorem bridge %PARAMS% (handle : Nat) (history : Domain.History (uniformCarriers F G)) :\n    DomainReduction.Bridge (Nominal.interface (G := G) \"bls12-381.fr\") closedPost history\n      (Original.participant (ringModel F G) program (routing handle) 1 %VALUES% ⟨[], history⟩)\n      (presented %ARGS% history) := by\n  unfold Original.participant\n  rw [source_root]\n  exact %BRIDGE%\n\nend %MODULE%.Sources\n"
  return text

end ZkcSecurity.Generation.OriginalSecurityBindings
