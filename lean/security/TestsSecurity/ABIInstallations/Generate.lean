import ZkcSecurity.Generation.SubjectABI
import ZkcSecurity.Generation.SigmaCompleteness
import TestsSecurity.ABIInstallations.Ordered
import TestsSecurity.ABIInstallations.Permuted
import TestsSecurity.ABIInstallations.Repeated
import TestsSecurity.ABIInstallations.Heterogeneous
import TestsSecurity.ABIInstallations.WitnessOnly
import TestsSecurity.ABIInstallations.NoData
import TestsSecurity.ABIInstallations.ConstrainedLaws
import ZkcSecurity.Examples.Generated.SchnorrRandomized
import ZkcSecurity.Examples.Generated.SmallSumcheck

/-! Exercise the actual printers on admitted subjects. The focused Python
runner compiles these outputs and their independent semantic controls. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ABIInstallations.Generate
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Generation

private meta unsafe def evaluate (α : Type) (typeName : Lean.Name)
    (term : Lean.Syntax) : Lean.Elab.Command.CommandElabM α :=
  Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Elab.Term.elabTerm term (some (Lean.mkConst typeName))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let reduced ← Lean.Meta.withTransparency .all <|
      Lean.Meta.reduce (← Lean.instantiateMVars expression)
    Lean.Meta.evalExpr α (Lean.mkConst typeName) reduced

private meta def require {α : Type} : Except String α → Lean.Elab.Command.CommandElabM α
  | .ok value => pure value
  | .error reason => Lean.throwError reason

run_cmd do
  let mut sources : List (String × String) := []
  for label in ["Ordered", "Permuted", "Repeated", "Heterogeneous", "WitnessOnly", "NoData", "Constrained"] do
    let subjectModule := "TestsSecurity.ABIInstallations." ++ label
    let subject := Lean.mkIdent ((subjectModule ++ ".subject").toName)
    let artifacts := Lean.mkIdent ((subjectModule ++ ".artifacts").toName)
    let metadata ← evaluate SubjectABI.Metadata ``SubjectABI.Metadata (← `(SubjectABI.metadata $subject))
    let pair ← evaluate AuthoredPair.Artifacts ``AuthoredPair.Artifacts artifacts
    let modulePrefix := "ABIInstallationClients." ++ label
    sources := sources ++ [(modulePrefix ++ "ABI", ← require <| SubjectABI.source metadata {
      moduleName := modulePrefix ++ "ABI", subjectModule })]
    for (role, artifact) in [("Producer", pair.producer), ("Validator", pair.validator)] do
      sources := sources ++ [(modulePrefix ++ role, ← require <| ZkcTools.StructuredSource.Constructed.source artifact {
        moduleName := modulePrefix ++ role, artifactModule := subjectModule
        artifactExpression := subjectModule ++ ".artifacts." ++ role.toLower })]
    let output : UniformRoot.Output := {
      moduleName := modulePrefix ++ "Completeness", subjectModule
      producerModule := modulePrefix ++ "Producer", validatorModule := modulePrefix ++ "Validator"
      abiModule := modulePrefix ++ "ABI", fieldType := "ZMod 5", groupType := "ZMod 5"
      sampling := "ZkcSecurity.Domains.PrimeField.rawSampleable 5" }
    let input : SigmaCompleteness.Input := { metadata, output }
    if label == "Constrained" then
      let lawsModule := "TestsSecurity.ABIInstallations.ConstrainedLaws"
      sources := sources ++ [(modulePrefix ++ "MissingNonvacuity", ← require <| SigmaCompleteness.source
        { input with output.moduleName := modulePrefix ++ "MissingNonvacuity" })]
      sources := sources ++ [(modulePrefix ++ "WrongNonvacuity", ← require <| SigmaCompleteness.source
        { input with output.moduleName := modulePrefix ++ "WrongNonvacuity", nonvacuityLaw := some "True.intro" })]
      sources := sources ++ [(modulePrefix ++ "Completeness", ← require <| SigmaCompleteness.source
        { input with imports := [lawsModule], nonvacuityLaw := some (lawsModule ++ ".nonvacuous") })]
      sources := sources ++ [(modulePrefix ++ "CrossedNonvacuity", ← require <| SigmaCompleteness.source
        { input with output.moduleName := modulePrefix ++ "CrossedNonvacuity"
                     imports := ["ABIInstallationClients.NoDataCompleteness"]
                     nonvacuityLaw := some "ABIInstallationClients.NoDataCompleteness.nonvacuous" })]
      sources := sources ++ [(modulePrefix ++ "InterpretedCompleteness", ← require <| SigmaCompleteness.source
        { input with output.moduleName := modulePrefix ++ "InterpretedCompleteness"
                     output.abiModule := modulePrefix ++ "InterpretedABI"
                     imports := [lawsModule], nonvacuityLaw := some (lawsModule ++ ".nonvacuous") })]
      for (suffix, law) in [("InterpretedABI", ".condition_iff"), ("WrongClauseABI", ".condition_iff"),
          ("MissingClauseABI", ".missingLaw")] do
        sources := sources ++ [(modulePrefix ++ suffix, ← require <| SubjectABI.source metadata {
          moduleName := modulePrefix ++ suffix, subjectModule, imports := [lawsModule]
          clauseInterpretation := some {
            condition := if suffix == "WrongClauseABI" then "fun (_ : subject.Inputs) => True"
              else lawsModule ++ ".condition"
            law := lawsModule ++ law } })]
    else
      sources := sources ++ [(modulePrefix ++ "Completeness", ← require <| SigmaCompleteness.source input)]
    if label == "NoData" then
      let empty : SubjectABI.Metadata := { metadata with
        types := [], producerPositions := some [], publicPositions := [], targetPositions := .ok []
        inputPolicy := ⟨[]⟩ }
      sources := sources ++ [("EmptySourceTemplate", ← require <| SubjectABI.source empty {
        moduleName := "EmptySourceTemplate", subjectModule })]
      sources := sources ++ [("EmptyRootTemplate", ← require <| RootCompleteness.source empty output.toOutput {
        imports := [], description := "Empty source elimination control."
        nonvacuityLaw := "nonvacuous", body := "  rfl\n" })]
  for label in ["SchnorrRandomized", "SmallSumcheck"] do
    let subjectModule := "ZkcSecurity.Examples.Generated." ++ label
    let subject := Lean.mkIdent ((subjectModule ++ ".subject").toName)
    let metadata ← evaluate SubjectABI.Metadata ``SubjectABI.Metadata (← `(SubjectABI.metadata $subject))
    let name := "ABIInstallationClients.Existing" ++ label ++ "ABI"
    sources := sources ++ [(name, ← require <| SubjectABI.source metadata { moduleName := name, subjectModule })]
  let name := Lean.mkIdent `generatedSources
  Lean.Elab.Command.elabCommand (← `(def $name : List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  for (name, source) in generatedSources do
    let path := System.FilePath.mk directory / (name.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile path source
    IO.println s!"generated {name}"

end TestsSecurity.ABIInstallations.Generate
