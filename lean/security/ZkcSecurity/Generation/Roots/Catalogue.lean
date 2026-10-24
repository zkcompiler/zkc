module

public import ZkcTools.StructuredSource.Root
public meta import ZkcTools.StructuredSource.Root
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcExamples.Construction.Generated.TwoSumsPair
public import ZkcSecurity.Claims.SourceChargeSites
public meta import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Production selections for the retained fixed requests. Naming conventions
are applied once. Family/model/target/policy choices are authored here; source
aliases, positions and charge labels are derived from the admitted inputs.
The generated export metadata preserves the original fixed requests. Its
participant identity bytes predate the current export's trailing local-service
field; they must not be replaced by current export hashes without migration. -/
namespace ZkcSecurity.Generation.Roots
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource.Root

structure Mathematics where
  model : String
  fieldType : String
  groupType : String
  modulus : String
  sampling : String
  capabilities : String

/-- The selected model declaration owns its module under this catalogue convention. -/
def Mathematics.modelModule (mathematics : Mathematics) : String :=
  mathematics.model.toName.getPrefix.toString

def primeField : Mathematics where
  model := "ZkcSecurity.Domains.PrimeField.blsScalarModel"
  fieldType := "ZMod blsModulus"
  groupType := "ZMod blsModulus"
  modulus := "blsModulus"
  sampling := "rawSampleable blsModulus"
  capabilities := "blsCapabilities original (by decide +kernel)"

/-- Explicit transitional honest-input choice. All vector inputs are cube tables
of this width at the unique index input, bounded by the unique compiled loop
maximum. The checked source-clause migration must replace this policy by proof. -/
structure CubeInputs where
  width : Nat

structure Selection where
  name : String
  snapshot : Snapshot
  helpers : List String
  artifacts : AuthoredPair.Artifacts
  target : String
  honestInputs : CubeInputs
  mathematics : Mathematics
  formulaNamespace : String

def Selection.sourceModule (root : Selection) : String :=
  "ZkcExamples.Structured.Generated.Bindings." ++ root.name ++ "Inputs"
def Selection.pairModule (root : Selection) : String :=
  "ZkcExamples.Construction.Generated." ++ root.name ++ "Pair"
def Selection.subjectModule (root : Selection) : String :=
  "ZkcSecurity.Examples.Generated." ++ root.name
def Selection.componentModule (root : Selection) (suffix : String) : String :=
  "ZkcSecurity.Examples.Generated.Components." ++ root.name ++ suffix
/-- Naming follows the generated binding; it selects no handwritten root proof. -/
def Selection.securityModule (root : Selection) : String :=
  "ZkcSecurity.Examples.Generated.OriginalSecurity." ++ root.name
def Selection.constructedModule (root : Selection) (role : String) : String :=
  "ZkcExamples.Structured.Generated.Constructed." ++ root.name ++ role

noncomputable def selections : List Selection := [
  { name := "SmallSumcheck"
    snapshot := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.snapshot
    helpers := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.payload.definitions.map (·.name)
    artifacts := ZkcExamples.Construction.Generated.SmallSumcheckPair.artifacts
    target := "public_sum", honestInputs := ⟨1⟩, mathematics := primeField
    formulaNamespace := "ZkcSecurity.Examples.Components.SmallSumcheck.Formula" },
  { name := "TwoSums"
    snapshot := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.snapshot
    helpers := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.payload.definitions.map (·.name)
    artifacts := ZkcExamples.Construction.Generated.TwoSumsPair.artifacts
    target := "public_sums", honestInputs := ⟨1⟩, mathematics := primeField
    formulaNamespace := "ZkcSecurity.Examples.Components.TwoSums.Formula" }]

/-- Materialize only closed selection data. Proof records and the source
interpreter are not reimplemented or evaluated by a second language. -/
meta unsafe def evaluateSelections : Lean.Elab.Command.CommandElabM (List Selection) :=
  Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (Lean.mkConst ``selections)
    Lean.Meta.evalExpr (List Selection) (Lean.mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Selection)) expression

/- A generated transport manifest exposes the author selections to the narrow
pipeline without duplicating a root list in Python or in a test module. -/
run_cmd do
  let mut manifest : List Lean.Json := []
  for root in ← evaluateSelections do
    manifest := manifest ++ [Lean.Json.mkObj [
      ("name", Lean.toJson root.name), ("target", Lean.toJson root.target),
      ("tableWidth", Lean.toJson root.honestInputs.width),
      ("formulaNamespace", Lean.toJson root.formulaNamespace),
      ("model", Lean.toJson root.mathematics.model), ("sourceModule", Lean.toJson root.sourceModule),
      ("pairModule", Lean.toJson root.pairModule), ("subjectModule", Lean.toJson root.subjectModule),
      ("aliasesModule", Lean.toJson (root.componentModule "Sources"))]]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `catalogueManifest) : String :=
    $(Lean.quote ((Lean.Json.arr manifest.toArray).compress))))

/-- The source spelling is derived from the actual nominal query template.
Round-trip through the existing selector refuses ambiguous, malformed or
unselected sites; there is no protocol-name dispatch. -/
def chargeLabels (root : Selection) : Except String (List String) := do
  let occurrences := ZkcSecurity.Claims.Domain.challengeOccurrences root.artifacts.validator.instructions
  let mut labels := []
  for occurrence in occurrences do
    let some path := ZkcSecurity.Claims.Domain.ChargeSite.sourcePath occurrence.template
      | throw "root-charge-origin"
    let label ← path.mapM sourceLabel
    let label := ".".intercalate label
    let some native := occurrence.template.querySite? | throw "root-charge-origin"
    unless ZkcSecurity.Claims.Domain.ChargeSite.resolveLabel occurrences label == some native do
      throw "root-ambiguous-charge-origin"
    unless root.artifacts.validator.policy.draws.any (fun draw => draw.1 == native) do
      throw "root-unselected-charge-origin"
    if labels.contains label then throw "root-ambiguous-charge-origin"
    labels := labels ++ [label]
  unless labels.length == root.artifacts.validator.policy.draws.length do
    throw "root-missing-charge-origin"
  return labels

mutual
  def loopBounds : List Zkc.Construction.Instruction → List Nat
    | [] => []
    | instruction :: rest => instructionBounds instruction ++ loopBounds rest
  def instructionBounds : Zkc.Construction.Instruction → List Nat
    | ⟨.loop _ maximum _, _, _, body⟩ => maximum :: loopBounds body
    | ⟨_, _, _, body⟩ => loopBounds body
end

def position (index : Nat) : String :=
  (List.range index).foldl (fun result _ => "(.there " ++ result ++ ")") ".here"

/-- The policy choice is explicit; positions, nominal field, and the bound
are derived. Layout changes or ambiguous count inputs refuse generation. -/
def inputPolicy (root : Selection) : Except String String := do
  let some entry := root.snapshot.protocolFunctions.find? (·.name == root.snapshot.entry)
    | throw "root-missing-entry"
  let [index] := (entry.inputs.zipIdx.filter (fun (ty, _) => ty == .index)).map Prod.snd
    | throw "root-ambiguous-policy-index"
  let [maximum] := (loopBounds root.artifacts.producer.instructions ++
    loopBounds root.artifacts.validator.instructions).eraseDups | throw "root-ambiguous-policy-bound"
  let tables := entry.inputs.zipIdx.filterMap fun (ty, index) =>
    match ty with | .vector _ => some index | _ => none
  if tables.isEmpty || root.honestInputs.width == 0 then throw "root-missing-policy-table"
  let rules := tables.map fun table =>
    ".cubeTable " ++ position table ++ " " ++ position index ++ " " ++ toString root.honestInputs.width
  return "⟨[" ++ ", ".intercalate (rules ++ [".boundedIndex " ++ position index ++ " " ++ toString maximum]) ++ "]⟩"

def subjectOutput (root : Selection) (originalExport producerExport validatorExport : String) : Except String FixedSubjectOutput := do
  return {
    moduleName := root.subjectModule, sourceModule := root.sourceModule
    originalExpression := root.sourceModule ++ ".program.snapshot"
    importedExpression := root.sourceModule ++ ".imported"
    pairModule := root.pairModule, artifactsExpression := root.pairModule ++ ".artifacts"
    modelModule := root.mathematics.modelModule, modelExpression := root.mathematics.model
    targetName := root.target, inputPolicyExpression := ← inputPolicy root
    originalExportExpression := quoted originalExport
    producerExportExpression := quoted producerExport
    validatorExportExpression := quoted validatorExport
    chargeSites := ← chargeLabels root }

/-- Shared output handling for production generators and their test drivers. -/
def writeSources (directory : String) (sources : List (String × String)) : IO Unit := do
  for (name, source) in sources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name}"

end ZkcSecurity.Generation.Roots
