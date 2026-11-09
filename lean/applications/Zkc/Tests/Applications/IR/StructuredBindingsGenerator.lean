import Zkc.Tests.Verification.IR.Generators.SumcheckBindings
import Zkc.Tests.IR.Generators.SourceConfigurations.Gkr
import Zkc.Tools.IR.StructuredSource.Root
import Zkc.Tools.IR.StructuredSource.Bindings.Inputs
import Zkc.Tools.IR.StructuredSource.Bindings.PresentInputs
import Zkc.Tools.IR.StructuredSource.Bindings.Ledger
import Zkc.Tests.IR.StructuredBindingsGeneric
import Zkc.Applications.IR.Structured.SumcheckSourceData
import Zkc.Applications.IR.Structured.Generated.Bindings.TwoSumsData
import Zkc.Applications.IR.Structured.GkrSourceData

namespace Tests.StructuredBindingsGenerator

/-! Reproducible Lean-owned generation of the three actual-source clients.
Python, when used by a caller, only runs this command and serializes artifacts.
No old Python execution AST or evaluator participates in this route. -/

open Zkc.Source.Structured ZkcTools.StructuredSource.Bindings

private structure InputSelection where
  dataModule : String
  namespaceName : String
  snapshotExpression : String

private def clients : List (Snapshot × Output × Option (Program → Except String SourceInstallation) × Option InputSelection) := [
  (ZkcExamples.Structured.SumcheckSourceData.snapshot,
    { moduleName := "Zkc.Applications.IR.Structured.Generated.Bindings.SmallSumcheck"
      namespaceName := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheck"
      sourceModule := "Zkc.Applications.IR.Structured.Generated.Bindings.SmallSumcheckInputs"
      programExpression := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program"
      importedExpression := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported" }, none, some {
      dataModule := "Zkc.Applications.IR.Structured.SumcheckSourceData"
      namespaceName := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs"
      snapshotExpression := "ZkcExamples.Structured.SumcheckSourceData.snapshot" }),
  (ZkcExamples.Structured.Generated.Bindings.TwoSumsData.snapshot,
    { moduleName := "Zkc.Applications.IR.Structured.Generated.Bindings.TwoSums"
      namespaceName := "ZkcExamples.Structured.Generated.Bindings.TwoSums"
      sourceModule := "Zkc.Applications.IR.Structured.Generated.Bindings.TwoSumsInputs"
      programExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program"
      importedExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported" }, none, some {
      dataModule := "Zkc.Applications.IR.Structured.Generated.Bindings.TwoSumsData"
      namespaceName := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs"
      snapshotExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsData.snapshot" }),
  (ZkcExamples.Structured.GkrSourceData.snapshot,
    { moduleName := "Zkc.Applications.IR.Structured.Generated.Bindings.GkrRounds"
      namespaceName := "ZkcExamples.Structured.Generated.Bindings.GkrRounds"
      sourceModule := "Zkc.Applications.IR.Structured.GkrSourceViews"
      programExpression := "ZkcExamples.Structured.GkrSourceViews.program"
      importedExpression := "ZkcExamples.Structured.GkrSourceViews.imported" }, some Tests.Generators.SourceConfigurations.Gkr.configure, none)]

private def require (result : Except String String) : IO String :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

def main (args : List String) : IO Unit := do
  let (directory, selected) ← match args with
    | [directory] => pure (directory, none)
    | [directory, "--only", client] => do
      unless clients.any (fun (_, output, _, _) => output.moduleName.endsWith ("." ++ client)) do
        throw (IO.userError "unknown bindings client")
      pure (directory, some client)
    | _ => throw (IO.userError "expected output directory [--only client]")
  if selected.isNone then
    let generic := Tests.StructuredBindingsGeneric.program
    let genericOutput : Output := {
      moduleName := "Zkc.Tests.IR.Generated.StructuredBindingsGeneric"
      namespaceName := "Tests.Generated.StructuredBindingsGeneric"
      sourceModule := "Zkc.Tests.IR.Generated.StructuredBindingsGenericInputs"
      programExpression := "Tests.Generated.StructuredBindingsGenericInputs.program"
      importedExpression := "Tests.Generated.StructuredBindingsGenericInputs.imported" }
    let genericPath := System.FilePath.mk directory / "Zkc/Tests/IR/Generated/StructuredBindingsGeneric.lean"
    IO.FS.createDirAll genericPath.parent.get!
    IO.FS.writeFile (genericPath.withExtension "inputs.lean") (inputsSource generic
      genericOutput.sourceModule "Zkc.Tests.IR.StructuredBindingsGeneric"
      "Tests.Generated.StructuredBindingsGenericInputs" "Tests.StructuredBindingsGeneric.snapshot")
    IO.FS.writeFile genericPath (← require (source generic genericOutput))
    IO.FS.writeFile (genericPath.withExtension "present.lean") (← require (PresentInputs.source generic
      { genericOutput with
        moduleName := "Zkc.Tests.IR.Generated.StructuredBindingsGenericPresent"
        namespaceName := "Tests.Generated.StructuredBindingsGenericPresent" } 0))
    IO.FS.writeFile (genericPath.withExtension "callbacks.lean") (← require (callbacksSource generic genericOutput))
    IO.println "generated no-helper default callback fixture"
  for (snapshot, output, configuration, inputs) in clients do
    if selected.any (fun client => !output.moduleName.endsWith ("." ++ client)) then continue
    let program ← match check snapshot with
      | .ok program => pure program
      | .error reason => throw (IO.userError reason)
    let installation ← match configuration with
      | none => pure none
      | some configure => match configure program with
        | .ok installation => pure (some installation)
        | .error reason => throw (IO.userError reason)
    let output := installation.map (fun selected => { output with protocols := selected.protocols }) |>.getD output
    let path := System.FilePath.mk directory / (output.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    if let some inputs := inputs then
      IO.FS.writeFile (path.withExtension "inputs.lean") (inputsSource program output.sourceModule inputs.dataModule
        inputs.namespaceName inputs.snapshotExpression)
    IO.FS.writeFile path (← require (source program output))
    IO.FS.writeFile (path.withExtension "callbacks.lean") (← require (if installation.isSome then
      callbacksSource program output else Tests.Generators.SumcheckBindings.sumcheckCallbacksSource program output))
    let template ← require (match installation with
      | some selected => helperAssociationsSource program output selected.templates selected.namespaceSuffix selected.associations
      | none => Tests.Generators.SumcheckBindings.sumcheckSource program output)
    if let some selected := installation then
      let templatePath := System.FilePath.mk directory / (selected.templates.moduleName.replace "." "/" ++ ".lean")
      IO.FS.createDirAll templatePath.parent.get!
      IO.FS.writeFile templatePath (← require (helperTemplatesSource program selected.templates selected.associations))
      IO.FS.writeFile (path.withExtension "caller.lean") (← require (selected.callerSource output))
    IO.FS.writeFile (path.withExtension "template.lean") template
    IO.FS.writeFile (path.withExtension "obligations.json") ((obligationLedger program output).pretty ++ "\n")
    IO.println s!"generated {output.moduleName}"

private def subjectDescriptor : ZkcTools.StructuredSource.Root.FixedSubjectOutput := {
  connectionModule := "Generated.Connection"
  moduleName := "Generated.Subject", sourceModule := "Source", pairModule := "Pair", modelModule := "Model"
  originalExpression := "snapshot", importedExpression := "imported", artifactsExpression := "artifacts"
  modelExpression := "model", targetName := "fixed_target"
  registryExpression := "registry"
  originalExportExpression := "sourceExport"
  producerExportExpression := "producerExport", validatorExportExpression := "validatorExport" }

-- The existing builder fills the fixed Subject; exports remain request data.
#guard ((ZkcTools.StructuredSource.Root.fixedSubjectSource subjectDescriptor).splitOn "bind_authored_subject").length = 2
#guard ((ZkcTools.StructuredSource.Root.fixedSubjectSource subjectDescriptor).splitOn "exports sourceExport, producerExport, validatorExport").length = 2

end Tests.StructuredBindingsGenerator
