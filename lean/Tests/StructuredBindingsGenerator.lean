import Tests.Generators.SumcheckBindings
import ZkcTools.StructuredSource.Bindings.Gkr
import ZkcTools.StructuredSource.Root
import ZkcTools.StructuredSource.Bindings.Inputs
import ZkcTools.StructuredSource.Bindings.Ledger
import Tests.StructuredBindingsGeneric
import ZkcExamples.Structured.SumcheckSourceData
import ZkcExamples.Structured.Generated.Bindings.TwoSumsData
import ZkcExamples.Structured.Generated.Bindings.GkrRoundsData

namespace Tests.StructuredBindingsGenerator

/-! Reproducible Lean-owned generation of the three actual-source clients.
Python, when used by a caller, only runs this command and serializes artifacts.
No old Python execution AST or evaluator participates in this route. -/

open Zkc.Source.Structured ZkcTools.StructuredSource.Bindings

private def clients : List (Snapshot × Output × Bool × String) := [
  (ZkcExamples.Structured.SumcheckSourceData.snapshot,
    { moduleName := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheck"
      sourceModule := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs"
      programExpression := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program"
      importedExpression := "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported" }, false, "ZkcExamples.Structured.SumcheckSourceData"),
  (ZkcExamples.Structured.Generated.Bindings.TwoSumsData.snapshot,
    { moduleName := "ZkcExamples.Structured.Generated.Bindings.TwoSums"
      sourceModule := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs"
      programExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program"
      importedExpression := "ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported" }, false, "ZkcExamples.Structured.Generated.Bindings.TwoSumsData"),
  (ZkcExamples.Structured.Generated.Bindings.GkrRoundsData.snapshot,
    { moduleName := "ZkcExamples.Structured.Generated.Bindings.GkrRounds"
      sourceModule := "ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs"
      programExpression := "ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs.program"
      importedExpression := "ZkcExamples.Structured.Generated.Bindings.GkrRoundsInputs.imported" }, true,
      "ZkcExamples.Structured.Generated.Bindings.GkrRoundsData")]

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
  let generic := Tests.StructuredBindingsGeneric.program
  let genericOutput : Output := {
    moduleName := "Tests.Generated.StructuredBindingsGeneric"
    sourceModule := "Tests.Generated.StructuredBindingsGenericInputs"
    programExpression := "Tests.Generated.StructuredBindingsGenericInputs.program"
    importedExpression := "Tests.Generated.StructuredBindingsGenericInputs.imported" }
  let genericPath := System.FilePath.mk directory / "Tests/Generated/StructuredBindingsGeneric.lean"
  IO.FS.createDirAll genericPath.parent.get!
  IO.FS.writeFile (genericPath.withExtension "inputs.lean") (inputsSource generic
    genericOutput.sourceModule "Tests.StructuredBindingsGeneric")
  IO.FS.writeFile genericPath (← require (source generic genericOutput))
  IO.FS.writeFile (genericPath.withExtension "callbacks.lean") (← require (callbacksSource generic genericOutput))
  IO.println "generated no-helper default callback fixture"
  for (snapshot, output, gate, dataModule) in clients do
    if selected.any (fun client => !output.moduleName.endsWith ("." ++ client)) then continue
    let program ← match check snapshot with
      | .ok program => pure program
      | .error reason => throw (IO.userError reason)
    let output ← if gate then do
      let selected ← match gkrProtocols program with
        | .ok indices => pure indices
        | .error reason => throw (IO.userError reason)
      pure { output with protocols := selected }
      else pure output
    let path := System.FilePath.mk directory / (output.moduleName.replace "." "/" ++ ".lean")
    IO.FS.createDirAll path.parent.get!
    IO.FS.writeFile (path.withExtension "inputs.lean") (inputsSource program output.sourceModule dataModule)
    IO.FS.writeFile path (← require (source program output))
    IO.FS.writeFile (path.withExtension "callbacks.lean") (← require (if gate then callbacksSource program output else
      Tests.Generators.SumcheckBindings.sumcheckCallbacksSource program output))
    let template ← require (if gate then do gateSource program output (← gkrGateOutput program) else
      Tests.Generators.SumcheckBindings.sumcheckSource program output)
    if gate then
      IO.FS.writeFile (path.withExtension "caller.lean") (← require (gkrCallerSource program output))
    IO.FS.writeFile (path.withExtension "template.lean") template
    IO.FS.writeFile (path.withExtension "obligations.json") ((obligationLedger program output).pretty ++ "\n")
    IO.println s!"generated {output.moduleName}"

private def subjectDescriptor : ZkcTools.StructuredSource.Root.FixedSubjectOutput := {
  moduleName := "Generated.Subject", sourceModule := "Source", pairModule := "Pair", modelModule := "Model"
  originalExpression := "snapshot", importedExpression := "imported", artifactsExpression := "artifacts"
  modelExpression := "model", targetName := "fixed_target"
  originalExportExpression := "sourceExport"
  producerExportExpression := "producerExport", validatorExportExpression := "validatorExport" }

-- The existing builder fills the fixed Subject; exports remain request data.
#guard ((ZkcTools.StructuredSource.Root.fixedSubjectSource subjectDescriptor).splitOn "bind_authored_subject").length = 2
#guard ((ZkcTools.StructuredSource.Root.fixedSubjectSource subjectDescriptor).splitOn "exports sourceExport, producerExport, validatorExport").length = 2

end Tests.StructuredBindingsGenerator
