module

public import ZkcTools.StructuredSource.Root
public meta import ZkcTools.StructuredSource.Root
public import ZkcSecurity.Claims.SourceChargeSites
public meta import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Reusable generation inputs and output conventions. Naming conventions
are applied once. Family/model/target choices are authored here; source
aliases, positions and charge labels are derived from the admitted inputs.
Generated export metadata names the exact current original and participant
bytes. Changing it reissues the requests and requires an explicit checked
migration; input-domain equivalence alone does not identify oracle experiments. -/
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

structure Selection where
  name : String
  snapshot : Snapshot
  helpers : List String
  artifacts : AuthoredPair.Artifacts
  target : String
  mathematics : Mathematics
  formulaNamespace : String
  registryExpression : String

def Selection.sourceModule (root : Selection) : String :=
  "ZkcExamples.Structured.Generated.Bindings." ++ root.name ++ "Inputs"
def Selection.pairModule (root : Selection) : String :=
  "ZkcExamples.Construction.Generated." ++ root.name ++ "Pair"
def Selection.subjectModule (root : Selection) : String :=
  "ZkcSecurity.Examples.Generated." ++ root.name
def Selection.componentModule (root : Selection) (suffix : String) : String :=
  "ZkcSecurity.Examples.Generated.Components." ++ root.name ++ suffix
/-- A library-owned property module uses the same checked source roots for both
honest completeness and adversarial soundness. Structural connection code is
never selected by this catalogue. -/
def Selection.securityModule (root : Selection) : String :=
  "ZkcSecurity.Examples.RootProperties." ++ root.name
def Selection.constructedModule (root : Selection) (role : String) : String :=
  "ZkcExamples.Structured.Generated.Constructed." ++ root.name ++ role

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

def subjectOutput (root : Selection) (originalExport producerExport validatorExport : String) : Except String FixedSubjectOutput := do
  return {
    connectionModule := "ZkcExamples.Structured.Generated.Connections." ++ root.name
    moduleName := root.subjectModule, sourceModule := root.sourceModule
    originalExpression := root.sourceModule ++ ".program.snapshot"
    importedExpression := root.sourceModule ++ ".imported"
    pairModule := root.pairModule, artifactsExpression := root.pairModule ++ ".artifacts"
    modelModule := root.mathematics.modelModule, modelExpression := root.mathematics.model
    targetName := root.target
    registryExpression := root.registryExpression
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
