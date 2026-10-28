module

public import ZkcTools.ConstructionBindings.Frames
public import ZkcTools.StructuredSource.Constructed
public import ZkcSecurity.Generation.GkrConnectionTemplates
public import ZkcExamples.Construction.GkrOriginalRounds
public import ZkcExamples.Construction.GkrOriginalLine

@[expose] public section

/-! Registered GKR structural installation. This family selects its existing
mathematical callback laws. Recursive SSA discovery and view printing are shared
machinery. No interpreter or protocol dispatch is added to that machinery.
All emitted body equations and full certificates are kernel checked. -/
set_option autoImplicit false
namespace ZkcSecurity.Generation.GkrConnections
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.ConstructionBindings
open ZkcTools.ConstructionBindings.Frames
open ZkcExamples.Structured ZkcExamples.Construction
open GkrConnectionTemplates

inductive Provenance where
  | canonicalExport
  | formalLayoutPerturbation
  deriving Repr

structure Installation where
  provenance : Provenance
  modulePrefix : String
  pairModule : String
  producerExpression : String
  validatorExpression : String
  producer : Participant
  validator : Participant
  /-- Physical input order as a permutation of the source role's data ABI and
  transcript. This is a routing proposal, checked by the emitted full proof. -/
  producerOrder : List Nat
  validatorOrder : List Nat

def literal {α : Type} [Repr α] (value : α) : String :=
  "(" ++ (reprStr value).replace "\n" " " ++ ")"

def fill (text : String) (fields : List (String × String)) : String :=
  -- Match longer keys first: INPUT must never consume INPUT_ABI or INPUT_VALUES.
  (fields.mergeSort (fun left right => decide (left.1.length > right.1.length))).foldl
    (fun text (key, value) => text.replace ("$" ++ key) value) text

def occurrenceSite (template : Template) : Except String String := do
  match (SourceOccurrences.repeatSites template).getLast? with
  | some site => return site
  | none => throw "gkr-connection-source-repeat"

structure RoleLayout where
  output : Frames.Repeat
  layer : Frames.Repeat
  left : Frames.Repeat
  right : Frames.Repeat
  coefficient : Frames.Repeat

def layout (artifact : Participant) : Except String RoleLayout := do
  let repeats ← Frames.analyze artifact
  let output ← Frames.select repeats (← occurrenceSite GkrOriginalOutput.drawTemplate)
  let layer ← Frames.select repeats (← occurrenceSite GkrSourceRouting.template14)
  let left ← Frames.select repeats (← occurrenceSite (GkrOriginalRounds.drawTemplate .left))
  let right ← Frames.select repeats (← occurrenceSite (GkrOriginalRounds.drawTemplate .right))
  let coefficient ← Frames.select repeats (← occurrenceSite GkrOriginalCoefficient.template)
  unless repeats.length == 5 && output.path.length == 1 && layer.path.length == 1 &&
      [left, right, coefficient].all (fun child => child.path.dropLast == layer.path) do
    throw "gkr-connection-nesting"
  return ⟨output, layer, left, right, coefficient⟩

def repeatFields (fieldPrefix view : String) (descriptor : Frames.Repeat) : List (String × String) :=
  [(fieldPrefix ++ "_OFFSET", toString descriptor.offset),
   (fieldPrefix ++ "_INITIAL", literal descriptor.initial),
   (fieldPrefix ++ "_YIELDS", literal descriptor.yielded),
   (fieldPrefix ++ "_MAXIMUM", toString descriptor.maximum),
   (fieldPrefix ++ "_COUNT", toString descriptor.count),
   (fieldPrefix ++ "_BODY", view ++ "." ++ Frames.selector descriptor.path),
   (fieldPrefix ++ "_LOOP", view ++ "." ++ Frames.loopSelector descriptor.path)]

/-- Library parameter names denote mathematical input coordinates. Their
physical locations are computed from independent source visibility and the
proposed input permutation, never copied from a previous construction. -/
def inputFields (role : Nat) (artifact : Participant) (order : List Nat) :
    Except String (List (String × String)) := do
  let root := GkrSourceViews.program.payload.entry
  let names := ["initial", "outputs", "add", "mul", "layers", "selector", "width", "handle"]
  unless root.inputs.length == names.length && root.inputScopes.length == names.length &&
      order.length == artifact.inputs.length && decide (order.Perm (List.range order.length)) do
    throw "gkr-connection-input-interface"
  let data := (root.inputs.zip root.inputScopes).zipIdx.filterMap fun ((ty, scope), index) =>
    if !ty.isHandle && scope.contains role then some index else none
  unless artifact.inputs.length == data.length + 1 && order.getLast? == some data.length do
    throw "gkr-connection-transcript-position"
  let mut locations := []
  let mut fields := []
  let mut values := []
  for (ty, index) in root.inputs.zipIdx do
    let some scope := root.inputScopes[index]? | throw "gkr-connection-input-scope"
    if !scope.contains role then
      locations := locations ++ [".absent"]
    else if ty.isService then
      locations := locations ++ [".capability handle"]
    else if ty.isHandle then
      throw "gkr-connection-handle"
    else
      let reference := order.idxOf (data.idxOf index)
      locations := locations ++ [".data " ++ toString reference]
      let name := names[index]!
      fields := fields ++ [(if name == "initial" then "INPUT" else name.toUpper, toString reference)]
  for oldReference in order do
    if oldReference == data.length then
      values := values ++ [".transcript context.suite history"]
    else
      let some sourceIndex := data[oldReference]? | throw "gkr-connection-input-reference"
      let some ty := root.inputs[sourceIndex]? | throw "gkr-connection-input-type"
      let some actualSort := artifact.inputs[values.length]? | throw "gkr-connection-input-sort"
      unless actualSort == .data ty do throw "gkr-connection-input-sort"
      let name := names[sourceIndex]!
      let value ← match ty with
        | .vector _ => pure (".data (.vector scalarDomain " ++ name ++ ")")
        | .index => pure (".data (.index " ++ name ++ ")")
        | _ => throw "gkr-connection-input-type"
      values := values ++ [value]
  return fields ++ [("INPUT_ABI", "[" ++ ", ".intercalate locations ++ "]"),
    ("INPUT_VALUES", "[" ++ ", ".intercalate values ++ "]")]

/-- Pure root padding is read from the actual instruction tree. It is
emitted into the complete frame relation, so inserted allocations remain
visible in both the certificate and execution projection. -/
def producerPrelude (artifact : Participant) (output : Frames.Repeat) : Except String String := do
  let prefixSteps := artifact.instructions.take (output.path.headD 0)
  let some (last, preceding) := prefixSteps.getLast?.map (fun last => (last, prefixSteps.dropLast))
    | throw "gkr-connection-producer-prelude"
  unless last.operation == .call GkrSourceBodies.emptyHelper.name && last.operands.isEmpty do
    throw "gkr-connection-producer-empty-vector"
  let mut values := []
  for step in preceding do
    unless step.operation == .indicesEmpty && step.operands.isEmpty && step.results == [.indices] do
      throw "gkr-connection-producer-padding"
    values := values ++ [".indices []"]
  return "[" ++ ", ".intercalate values ++ "]"

def roleFields (installation : Installation) (producer : Bool) :
    Except String (RoleLayout × List (String × String)) := do
  let artifact := if producer then installation.producer else installation.validator
  let order := if producer then installation.producerOrder else installation.validatorOrder
  let fieldPrefix := if producer then "PRODUCER" else "VALIDATOR"
  let view := installation.modulePrefix ++ ".Generated." ++ (if producer then "Producer" else "Validator")
  let selected ← layout artifact
  let inputs ← inputFields (if producer then 0 else 1) artifact order
  let mut fields := [(fieldPrefix ++ "_VIEW", view)] ++ inputs.map (fun (key, value) => (fieldPrefix ++ "_" ++ key, value))
  for (key, descriptor) in [("OUTPUT", selected.output), ("LAYER", selected.layer),
      ("LEFT", selected.left), ("RIGHT", selected.right), ("COEFFICIENT", selected.coefficient)] do
    fields := fields ++ repeatFields (fieldPrefix ++ "_" ++ key) view descriptor
  let relative := selected.left.yielded.map (· - selected.left.offset)
  unless selected.left.yielded.all (selected.left.offset ≤ ·) &&
      selected.right.yielded.all (selected.right.offset ≤ ·) &&
      relative == selected.right.yielded.map (· - selected.right.offset) do
    throw "gkr-connection-round-yield-map"
  let offsetName := if producer then "producerOffset" else "validatorOffset"
  fields := fields ++ [(fieldPrefix ++ "_RELATIVE_YIELDS", "[" ++ ", ".intercalate
    (relative.map fun reference => "(" ++ offsetName ++ " side) + " ++ toString reference) ++ "]")]
  if producer then
    fields := fields ++ [("PRODUCER_PRELUDE", ← producerPrelude artifact selected.output)]
    let line ← Frames.callOperands selected.coefficient GkrSourceBodies.helper70Helper.name
    let [reference, index] := line | throw "gkr-connection-coefficient-operands"
    unless index == selected.coefficient.offset do throw "gkr-connection-coefficient-index"
    fields := fields ++ [("PRODUCER_LINE", toString reference)]
  return (selected, fields)

def moduleSource (installation : Installation) (name space template : String)
    (dependencies : List String) (fields : List (String × String)) : Except String (String × String) := do
  let moduleName := installation.modulePrefix ++ "." ++ name
  let text := fill template fields
  unless !(text.contains '$') do throw ("gkr-connection-unfilled-template: " ++ name)
  let text := text.replace "CanonicalPair.Producer.participant" installation.producerExpression
    |>.replace "CanonicalPair.Validator.participant" installation.validatorExpression
  let imports := dependencies.map fun dependency =>
    if dependency.startsWith "Zkc" then dependency else installation.modulePrefix ++ "." ++ dependency
  let preamble := "module\n\n" ++ String.join (imports.map ("public import " ++ · ++ "\n")) ++
    "public import " ++ installation.modulePrefix ++ ".Generated.Producer\n" ++
    "public import " ++ installation.modulePrefix ++ ".Generated.Validator\n" ++
    "public import ZkcSecurity.Realizations.Gkr.HonestProducerSource\n" ++
    "public meta import ZkcSecurity.Realizations.Gkr.ConnectionTactics\n\n" ++
    "@[expose] public section\n" ++
    "/-! Generated by checks/GenerateGkrConnections.lean from source/SSA descriptors.\n" ++
    "Regenerate with checks/generate_gkr_connections.py; do not edit. -/\n" ++
    "set_option autoImplicit false\nset_option maxRecDepth 50000\n" ++
    "set_option maxHeartbeats 8000000\nset_option linter.unusedSimpArgs false\n" ++
    "set_option linter.unusedTactic false\nset_option backward.isDefEq.respectTransparency false\n" ++
    "noncomputable section\nnamespace " ++ installation.modulePrefix ++ "." ++ space ++ "\n"
  let views := ["PRODUCER_VIEW", "VALIDATOR_VIEW"].filterMap fun key => (fields.find? (·.1 == key)).map (·.2 ++ ".body")
  let layers := ["PRODUCER_LAYER_BODY", "VALIDATOR_LAYER_BODY"].filterMap fun key => (fields.find? (·.1 == key)).map Prod.snd
  let attributes := String.join ((views ++ layers).map ("attribute [local irreducible] " ++ · ++ "\n"))
  return (moduleName, preamble ++ attributes ++ text ++ "\nend " ++ installation.modulePrefix ++ "." ++ space ++ "\n")

def sources (installation : Installation) : Except String (List (String × String)) := do
  let (producerLayout, producerFields) ← roleFields installation true
  let (validatorLayout, validatorFields) ← roleFields installation false
  let fields := producerFields ++ validatorFields
  let localFields (producer : Bool) : List (String × String) := Id.run do
    let selected := if producer then producerLayout else validatorLayout
    let fieldPrefix := if producer then "PRODUCER" else "VALIDATOR"
    let role := if producer then "Producer" else "Validator"
    let view := installation.modulePrefix ++ ".Generated." ++ role
    let mut scopedFields := [("OFFSET", toString selected.layer.offset),
      ("YIELDS", literal selected.layer.yielded), ("INITIAL", literal selected.layer.initial),
      ("MAXIMUM", toString selected.layer.maximum), ("COUNT", toString selected.layer.count),
      ("SITE", literal selected.layer.site), ("ROOT_BODY", view ++ ".body"),
      ("LAYER_BODY", view ++ "." ++ Frames.selector selected.layer.path)]
    for key in ["INPUT", "ADD", "MUL", "LAYERS", "SELECTOR", "WIDTH"] do
      let value := (fields.find? (·.1 == fieldPrefix ++ "_" ++ key)).map Prod.snd |>.getD "MISSING"
      scopedFields := scopedFields ++ [(key, value)]
    return scopedFields ++ fields
  let mut result := []
  for (role, artifact, expression) in [("Producer", installation.producer, installation.producerExpression),
      ("Validator", installation.validator, installation.validatorExpression)] do
    let name := installation.modulePrefix ++ ".Generated." ++ role
    let source ← ZkcTools.StructuredSource.Constructed.source artifact
      ⟨name, installation.pairModule, expression⟩
    result := result ++ [(name, source)]
  let sourceRegions := "ZkcSecurity.Realizations.Gkr.OriginalRegions"
  let rootRegions := "ZkcSecurity.Realizations.Gkr.OriginalRootRegions"
  for (name, space, template, dependencies, scopedFields) in [
      ("OriginalOutput", "OriginalOutput", originalOutput, ["ZkcSecurity.Realizations.Gkr.OutputTemplate"], fields),
      ("OriginalRounds", "OriginalRounds", originalRounds, ["ZkcExamples.Construction.GkrOriginalRounds"], fields),
      ("OriginalCoefficient", "OriginalCoefficient", originalCoefficient, ["ZkcExamples.Construction.GkrOriginalCoefficient"], fields),
      ("OriginalProducerLayer", "OriginalLayer", originalProducerLayer, [sourceRegions, "OriginalRounds", "OriginalCoefficient", "ZkcExamples.Construction.GkrOriginalLine"], localFields true),
      ("OriginalValidatorLayer", "OriginalLayer", originalValidatorLayer, [sourceRegions, "OriginalRounds", "OriginalCoefficient", "ZkcExamples.Construction.GkrOriginalLine"], localFields false),
      ("OriginalCertificateFrames", "OriginalCertificates", originalCertificateFrames,
        [rootRegions, "ZkcExamples.Structured.GkrProverContinuation", "Zkc.Construction.OriginalExecution"], fields),
      ("OriginalProducerBody", "OriginalCertificates", originalProducerBody,
        ["OriginalCertificateFrames", "OriginalProducerLayer", "OriginalOutput", rootRegions], localFields true),
      ("OriginalValidatorBody", "OriginalCertificates", originalValidatorBody,
        ["OriginalCertificateFrames", "OriginalValidatorLayer", "OriginalOutput", rootRegions], localFields false),
      ("OriginalProducerRoot", "OriginalCertificates", originalProducerRoot,
        ["OriginalProducerBody", rootRegions, "Zkc.Construction.OriginalParticipant"], fields),
      ("OriginalValidatorRoot", "OriginalCertificates", originalValidatorRoot,
        ["OriginalValidatorBody", rootRegions, "Zkc.Construction.OriginalParticipant"], fields)] do
    result := result ++ [← moduleSource installation name space template dependencies scopedFields]
  return result

/-- Machine-readable provenance of the selected physical proposal. It is
reported alongside exact output hashes, never used as theorem authority. -/
def describe (installation : Installation) : Except String Lean.Json := do
  let role (producer : Bool) : Except String Lean.Json := do
    let artifact := if producer then installation.producer else installation.validator
    let repeats ← Frames.analyze artifact
    return Lean.Json.mkObj [
      ("inputOrder", Lean.toJson (if producer then installation.producerOrder else installation.validatorOrder)),
      ("inputArity", Lean.toJson artifact.inputs.length),
      ("returned", Lean.toJson artifact.returned),
      ("repeats", .arr ((repeats.map fun descriptor => Lean.Json.mkObj [
        ("site", Lean.toJson descriptor.site), ("path", Lean.toJson descriptor.path),
        ("selector", Lean.toJson (Frames.selector descriptor.path)),
        ("captureSize", Lean.toJson descriptor.offset), ("maximum", Lean.toJson descriptor.maximum),
        ("count", Lean.toJson descriptor.count), ("initial", Lean.toJson descriptor.initial),
        ("yielded", Lean.toJson descriptor.yielded)]).toArray))]
  return Lean.Json.mkObj [("modulePrefix", Lean.toJson installation.modulePrefix),
    ("artifactModule", Lean.toJson installation.pairModule),
    ("provenance", Lean.toJson (reprStr installation.provenance)),
    ("claimsNewNativeByteAssociation", Lean.toJson false),
    ("identityMetadata", Lean.toJson (match installation.provenance with
      | .canonicalExport => "unchanged retained native export"
      | .formalLayoutPerturbation => "unchanged ancestor identity fields; tree derived by checked transformation, not new native bytes")),
    ("producerExpression", Lean.toJson installation.producerExpression),
    ("validatorExpression", Lean.toJson installation.validatorExpression),
    ("producer", ← role true), ("validator", ← role false)]

end ZkcSecurity.Generation.GkrConnections
