module

public import ZkcTools.StructuredSource.Bindings.Callbacks
public import ZkcTools.StructuredSource.Bindings.Calls
public import Zkc.Protocols.AlgebraicRounds.Gate

@[expose] public section

/-! Exact gate arithmetic bindings. Indices select candidate admitted helpers;
selection is not a semantic assertion. Every emitted full-body component
equation is independently checked, including every operand's order. -/

namespace ZkcTools.StructuredSource.Bindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open Zkc.Source.Structured.Bindings
open ZkcTools.StructuredSource.Presentation

structure GateOutput where
  valueIndex : Nat
  quadraticIndex : Nat

/-- Typed origins select candidates; generated full-body equations remain the
authority. Refuse ambiguity instead of retaining historical table ordinals. -/
def gkrProtocols (program : Program) : Except String (List Nat) := do
  let mut selected := []
  for origin in [ProtocolOrigin.mk "gkr::Rounds" [("F", .field "bls12-381.fr"), ("Max", .natural "4")],
      ProtocolOrigin.mk "gkr::Gkr" [("F", .field "bls12-381.fr"),
        ("MaxLayers", .natural "4"), ("MaxWidth", .natural "4")]] do
    let names := program.snapshot.definitions.filterMap fun definition => do
      let .function function := definition | none
      if function.origin == some (.protocol origin) then some function.name else none
    let [name] := names | throw "gkr-protocol-origin"
    let [index] := (program.payload.protocols.zipIdx.filter (fun (p, _) => p.name == name)).map Prod.snd
      | throw "gkr-protocol-association"
    selected := selected ++ [index]
  return selected

def gkrGateOutput (program : Program) : Except String GateOutput := do
  let select := fun arity => (program.payload.definitions.zipIdx.filter fun (d, _) =>
    d.kind == .math && d.inputs == List.replicate arity (.field "bls12-381.fr") &&
      d.outputs == [.field "bls12-381.fr"]).map Prod.snd
  let [value] := select 4 | throw "gkr-gate-value-candidate"
  let [quadratic] := select 8 | throw "gkr-gate-quadratic-candidate"
  return ⟨value, quadratic⟩

/-- The enclosing layer callback and its exact retained continuation are
selected from the admitted caller, never supplied as a handwritten wrapper. -/
def gkrCallerSource (program : Program) (output : Output) : Except String String := do
  let [_, index] ← gkrProtocols program | throw "gkr-caller-selection"
  let some definition := program.payload.protocols[index]? | throw "gkr-caller-definition"
  let mut text := "module\n\npublic import " ++ output.moduleName ++ "Callbacks\npublic import Zkc.Source.Structured.RepeatLaws\n\n@[expose] public section\n\n" ++
    "/-! Generated actual GKR call seam. No terminal security assertion. -/\nnamespace " ++ output.moduleName ++ "Caller\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "open " ++ output.moduleName ++ " " ++ output.moduleName ++ "Callbacks\n" ++
    "set_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\nnoncomputable section\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  let field := Ty.field "bls12-381.fr"
  let vector := Ty.vector "bls12-381.fr"
  for (helperName, inputs, outputs) in [
      ("valuesBelow", [vector, vector, vector, .index, .index, .index, .index], [vector]),
      ("layerGates", [vector, vector, vector, vector, .index], List.replicate 4 vector),
      ("evaluate", [vector, vector], [field])] do
    let candidates := program.payload.definitions.zipIdx.filter fun (d, _) =>
      d.inputs == inputs && d.outputs == outputs && d.kind == .local
    let [(d, i)] := candidates | throw ("gkr-helper-candidate-" ++ helperName)
    text := text ++ "abbrev " ++ helperName ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
      toString i ++ ", by decide +kernel⟩\n" ++
      "abbrev " ++ helperName ++ "Helper := " ++ helperName ++ "Definition.helper\n" ++
      "theorem " ++ helperName ++ "_body (args : Values (assignment F G) " ++ helperName ++ "Helper.inputs) :\n" ++
      "    invoke (closedMeanings payload.definitions) " ++ helperName ++ "Helper args =\n" ++
      "      " ++ helperName ++ "Definition.body.denote (meaning F G (closedMeanings payload.definitions)) args.get :=\n" ++
      "  Evaluation.definitions_invoke_body_view_as SiteObservations.closed payload.definitions payload.linked\n" ++
      "    " ++ helperName ++ "Definition (List.get_mem _ _) " ++ helperText d.helper ++ " rfl " ++
      helperName ++ "Definition.body rfl args\n\n"
  let outputs := (callbacks definition.body).zipIdx.filter fun (callback, _) =>
    callback.spec.state == [vector, vector] &&
      callback.spec.captures == [.service "random.bls12-381.fr/0"]
  let [(outputCallback, outputIndex)] := outputs | throw "gkr-output-callback-selection"
  text := text ++ "abbrev outputSpec : RepeatSpec := " ++ repeatText outputCallback.spec ++ "\n" ++
    "abbrev outputBody := " ++ roleName index 1 ++ "Callback" ++ toString outputIndex ++ "Body\n\n"
  let mut layerCount := 0
  for (callback, callbackIndex) in (callbacks definition.body).zipIdx do
    let inputs := .index :: (callback.spec.state ++ callback.spec.captures)
    let pattern := optionalPattern inputs
    let signature : Signature := ⟨[], false, false, program.payload.definitions.map (·.helper), keys program⟩
    let naming : Naming signature.laws signature.callees pattern.scope := {
      carriers := .uniform "F" "G", tables := "(helpers (F := F) (G := G) payload).toOn"
      results := "callbackResults (F := F) (G := G)", context := "ctx"
      runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)"
      processes := "actualCallees payload calleeKeys" }
    let form ← normalize signature callback.body 1 definition.roles.length pattern
    let some _ := applicationCursor "label_6c656674" (inputNames naming.inputs 0) form | continue
    layerCount := layerCount + 1
    let producer ← normalize signature callback.body 0 definition.roles.length pattern
    let .owned _ _ _ (.owned _ block _ _) := producer | throw "gkr-producer-block-selection"
    let [(_, blockIndex)] := program.payload.definitions.zipIdx.filter (fun (d, _) => d.helper == block)
      | throw "gkr-producer-block-association"
    text := text ++ "abbrev selectBlockDefinition : CheckedDefinition := payload.definitions.get ⟨" ++
      toString blockIndex ++ ", by decide +kernel⟩\nabbrev selectBlockHelper := selectBlockDefinition.helper\n\n"
    let producerNaming := { naming with
      runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)" }
    text := text ++ (← callSplitSource producerNaming producer
      (roleName index 0 ++ "Callback" ++ toString callbackIndex) "label_6c656674")
    let name := roleName index 1 ++ "Callback" ++ toString callbackIndex
    text := text ++ (← callSplitSource naming form name "label_6c656674")
    text := text ++ "abbrev firstLeft := @" ++ name ++ "Process\n" ++
      "abbrev firstLeftContext := " ++ name ++ "SetupContext\n" ++
      "abbrev firstLeftInput := @" ++ name ++ "SetupInput\n" ++
      "abbrev firstLeftContinuation := @" ++ name ++ "SetupContinuation\n" ++
      "abbrev layerSpec : RepeatSpec := " ++ repeatText callback.spec ++ "\n" ++
      "abbrev layerBody := " ++ name ++ "Body\n\n"
    let wholePattern := optionalPattern definition.inputs
    let wholeSignature : Signature := ⟨projectionLaws program, false, false,
      program.payload.definitions.map (·.helper), keys program⟩
    let wholeNaming : Naming wholeSignature.laws wholeSignature.callees wholePattern.scope := {
      carriers := .uniform "F" "G", tables := "(helpers (F := F) (G := G) payload).toOn"
      results := "projectionResults (F := F) (G := G)", context := "ctx"
      runs := "Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)"
      processes := roleName index 1 ++ "Callees" }
    let (_, named, _) ← request wholeSignature definition.body 1 definition.roles.length wholePattern wholeNaming
    let whole ← normalize {wholeSignature with names := named} definition.body 1 definition.roles.length wholePattern
    text := text ++ (← repeatSplitSource wholeNaming whole 1 (roleName index 1) callback.site)
  unless layerCount == 1 do throw "gkr-layer-call-selection"
  return text ++ "end\nend " ++ output.moduleName ++ "Caller\n"

/-- The admitted definitions are in dependency order. Follow their actual
edges through scoped callbacks and mathematical realizations without assuming
that a source wrapper calls its arithmetic implementation directly. -/
def helperDependsOn (program : Program) (parent candidate : Helper) : Bool :=
  let reachable := program.payload.definitions.foldl (fun found definition =>
    if definition.helper == candidate || definition.helpers.any found.contains then
      definition.helper :: found
    else found) []
  reachable.contains parent

/-- Candidate associations follow complete signatures and actual dependency
edges. Printed positions are checked membership witnesses, not dispatch keys. -/
def gkrHelperAssociations (program : Program) (gate : GateOutput) :
    Except String (List (String × Nat)) := do
  let field := Ty.field "bls12-381.fr"
  let vector := Ty.vector "bls12-381.fr"
  let select := fun (name : String) (kind : HelperKind) (inputs outputs : List Ty)
      (within : Option CheckedDefinition) => do
    let candidates := program.payload.definitions.zipIdx.filter fun (d, _) =>
      d.kind == kind && d.inputs == inputs && d.outputs == outputs &&
        (within.map (fun parent => helperDependsOn program parent.helper d.helper)).getD true
    let [(definition, index)] := candidates | throw ("gkr-helper-association-" ++ name)
    pure (definition, index)
  let (_, empty) ← select "empty" .local [] [vector] none
  let (restriction, gateRestriction) ← select "gateRestriction" .local
    (List.replicate 4 vector ++ [field]) (List.replicate 4 vector) none
  let (factor, factorRestriction) ← select "factorRestriction" .local
    [vector, field] [vector] (some restriction)
  let (maps, interpolations) ← select "interpolations" .local
    [vector, vector, field] [vector] (some factor)
  let (interpolationCallback, interpolationCallbackIndex) ← select "interpolationCallback" .local
    [field, field, vector, vector, field] [field] (some maps)
  let (_, interpolationRealization) ← select "interpolationRealization" .local
    (List.replicate 3 field) [field] (some interpolationCallback)
  let (_, interpolation) ← select "interpolation" .math
    (List.replicate 3 field) [field] (some maps)
  let [roundsIndex, callerIndex] ← gkrProtocols program | throw "gkr-rounds-association"
  let some rounds := program.payload.protocols[roundsIndex]? | throw "gkr-rounds-definition"
  let signature : Signature := ⟨[], false, false, program.payload.definitions.map (·.helper), keys program⟩
  let roundsForm ← normalize signature rounds.body 1 rounds.roles.length (optionalPattern rounds.inputs)
  let .owned _ roundsOpen _ (.repeat _ _ _ _ _ _ (.owned _ roundsClose _ _)) := roundsForm
    | throw "gkr-rounds-pending-boundaries"
  let some caller := program.payload.protocols[callerIndex]? | throw "gkr-caller-definition"
  let mut pendingBoundaries := []
  for callback in callbacks caller.body do
    let form ← normalize signature callback.body 1 caller.roles.length
      (optionalPattern (.index :: (callback.spec.state ++ callback.spec.captures)))
    if let .owned _ layerOpen _ (.owned _ pending _ (.apply _ _ _ "label_6c656674" _ _)) := form then
      pendingBoundaries := pendingBoundaries ++ [(layerOpen, pending)]
  let [(layerOpen, pending)] := pendingBoundaries | throw "gkr-layer-pending-boundaries"
  let mut pendingHelpers := []
  for (name, helper) in [("roundsOpen", roundsOpen), ("roundsClose", roundsClose),
      ("layerOpen", layerOpen), ("pending", pending)] do
    let [(_, index)] := program.payload.definitions.zipIdx.filter (fun (d, _) => d.helper == helper)
      | throw ("gkr-pending-helper-association-" ++ name)
    pendingHelpers := pendingHelpers ++ [(name, index)]
  let [(_, append)] := program.payload.definitions.zipIdx.filter (fun (d, _) =>
    rounds.helpers.contains d.helper && d.kind == .local && d.inputs == [vector, field] && d.outputs == [vector] &&
      (match d.raw.operations.filter (fun | .mark _ => false | _ => true) with
        | [.exec (.vectorAppend domain)] => domain == "bls12-381.fr"
        | _ => false))
    | throw "gkr-helper-association-append"
  let (message, roundMessage) ← select "roundMessage" .local
    (List.replicate 4 vector) (List.replicate 3 field) none
  let [leftValue, rightValue] := message.helpers.filter (fun helper =>
    helper.kind == .local && helper.inputs == List.replicate 4 vector && helper.outputs == [vector])
    | throw "gkr-gate-values-occurrences"
  let [(leftValues, leftValueIndex)] := program.payload.definitions.zipIdx.filter (fun (d, _) => d.helper == leftValue)
    | throw "gkr-gate-values-left-association"
  let [(_, rightValueIndex)] := program.payload.definitions.zipIdx.filter (fun (d, _) => d.helper == rightValue)
    | throw "gkr-gate-values-right-association"
  let (valueCallback, valueCallbackIndex) ← select "gateValueCallback" .local
    (List.replicate 4 field ++ List.replicate 4 vector) [field] (some leftValues)
  let (_, valueRealization) ← select "gateValueRealization" .local
    (List.replicate 4 field) [field] (some valueCallback)
  let (quadratics, quadraticsIndex) ← select "gateQuadratics" .local
    (List.replicate 8 vector) [vector] (some message)
  let (quadraticCallback, quadraticCallbackIndex) ← select "gateQuadraticCallback" .local
    (List.replicate 8 field ++ List.replicate 8 vector) [field] (some quadratics)
  let (_, quadraticRealization) ← select "gateQuadraticRealization" .local
    (List.replicate 8 field) [field] (some quadraticCallback)
  let (wrapper, linearWrapper) ← select "linearWrapper" .local
    (List.replicate 3 field) [field] (some message)
  let (_, linearCoefficient) ← select "linearCoefficient" .math
    (List.replicate 3 field) [field] (some wrapper)
  return pendingHelpers ++ [("empty", empty), ("append", append), ("gateValue", gate.valueIndex),
    ("gateValuesLeft", leftValueIndex), ("gateValuesRight", rightValueIndex),
    ("gateValueCallback", valueCallbackIndex), ("gateValueRealization", valueRealization),
    ("gateQuadratic", gate.quadraticIndex), ("gateQuadratics", quadraticsIndex),
    ("gateQuadraticCallback", quadraticCallbackIndex), ("gateQuadraticRealization", quadraticRealization),
    ("linearCoefficient", linearCoefficient),
    ("linearWrapper", linearWrapper), ("roundMessage", roundMessage),
    ("interpolation", interpolation), ("interpolations", interpolations),
    ("interpolationCallback", interpolationCallbackIndex), ("interpolationRealization", interpolationRealization),
    ("factorRestriction", factorRestriction), ("gateRestriction", gateRestriction)]

def gateSource (program : Program) (output : Output) (gate : GateOutput) : Except String String := do
  let some value := program.payload.definitions[gate.valueIndex]? | throw "gate-value-index"
  let some quadratic := program.payload.definitions[gate.quadraticIndex]? | throw "gate-quadratic-index"
  let [.field domain] := value.outputs | throw "gate-value-output"
  unless value.inputs == List.replicate 4 (.field domain) &&
      quadratic.inputs == List.replicate 8 (.field domain) && quadratic.outputs == value.outputs do
    throw "gate-helper-signature"
  let mut text := "module\n\npublic import " ++ output.moduleName ++ "Callbacks\n" ++
    "public import Zkc.Protocols.AlgebraicRounds.Gate\n\n@[expose] public section\n\n" ++
    "/-! Generated actual-helper gate equations. This is not a full GKR theorem. -/\nnamespace " ++ output.moduleName ++ "Gate\n" ++
    "open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings\n" ++
    "open Zkc.Protocols.AlgebraicRounds\nopen " ++ output.moduleName ++ "\nset_option maxRecDepth 50000\nset_option maxHeartbeats 8000000\n" ++
    "set_option smartUnfolding false\nnoncomputable section\n" ++
    "variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]\n\n"
  for (name, index) in (← gkrHelperAssociations program gate) do
    let some definition := program.payload.definitions[index]? | throw "gkr-associated-helper-index"
    text := text ++ "abbrev " ++ name ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
      toString index ++ ", by decide +kernel⟩\n" ++
      "abbrev " ++ name ++ "Helper : Helper := " ++ helperText definition.helper ++ "\n" ++
      "def " ++ name ++ "Body : Region dialect " ++ name ++ "Helper.inputs " ++ name ++
      "Helper.outputs :=\n  " ++ helperRegionText definition.body ++ "\n" ++
      "theorem " ++ name ++ "_closed (args : Values (assignment F G) " ++ name ++ "Helper.inputs) :\n" ++
      "    invoke (helpers payload).closed " ++ name ++ "Helper args =\n" ++
      "      " ++ name ++ "Body.denote (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed) args.get :=\n" ++
      "  Evaluation.definitions_invoke_body_view_as (.silent _) payload.definitions payload.linked\n" ++
      "    " ++ name ++ "Definition (List.get_mem _ _) " ++ helperText definition.helper ++ " rfl " ++
      name ++ "Body rfl args\n\n"
    if let [.collect spec] := definition.raw.operations then
      text := text ++ "abbrev " ++ name ++ "Collection : CollectSpec :=\n  " ++
        collectText spec ++ "\n\n"
  for (name, index, arguments, expression) in [
      ("value", gate.valueIndex, ["add", "mul", "left", "right"], "Gate.value add mul left right"),
      ("quadratic", gate.quadraticIndex, ["a0", "a1", "m0", "m1", "l0", "l1", "r0", "r1"],
        "Gate.quadratic a0 a1 m0 m1 l0 l1 r0 r1")] do
    let args := valuesText (arguments.map fun argument => app "some" [argument])
    let result := ".done (.cons (some (" ++ expression ++ ")) .nil)"
    let parameters := "(" ++ " ".intercalate arguments ++ " : F)"
    text := text ++ "abbrev " ++ name ++ "Definition : CheckedDefinition := payload.definitions.get ⟨" ++
      toString index ++ ", by decide +kernel⟩\n\n" ++
      "theorem " ++ name ++ "_body " ++ parameters ++ " :\n" ++
      "    " ++ name ++ "Definition.body.component\n" ++
      "      (Evaluation.meaning (.silent (participantInterface F G)) (helpers payload).closed)\n" ++
      "      (Evaluation.componentOperation (.silent _) (helpers payload)) " ++
      "(" ++ paren (args ++ " : Values (Component (assignment F G)) " ++ name ++ "Definition.inputs") ++ ".get) =\n" ++
      "      " ++ result ++ " := by\n  kernel_rfl\n\n" ++
      "theorem " ++ name ++ "_invoke " ++ parameters ++ " :\n" ++
      "    invoke (helpers (F := F) (G := G) payload).components " ++ name ++ "Definition.helper " ++ args ++ " =\n" ++
      "      " ++ result ++ " :=\n" ++
      "  (helper_body payload " ++ name ++ "Definition (List.get_mem _ _) " ++ args ++ ").trans\n" ++
      "    (" ++ name ++ "_body " ++ " ".intercalate arguments ++ ")\n\n"
  return text ++ "end\nend " ++ output.moduleName ++ "Gate\n"

end ZkcTools.StructuredSource.Bindings
