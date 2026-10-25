import ZkcSecurity.Generation.Roots.Catalogue
import ZkcSecurity.Generation.RoundDescriptors

/-! Explicit comparison fixture for the retired compiled matcher. Production
receipts use OriginalEndpoint; the catalogue still owns the admitted inputs. -/
namespace TestsSecurity.GenerateRoundDescriptors
open ZkcSecurity.Generation ZkcSecurity.Generation.Roots

run_cmd do
  let mut sources := []
  for root in ← evaluateSelections do
    let output : RoundDescriptors.Output := {
      moduleName := root.componentModule "Rounds"
      producerModule := root.constructedModule "Producer"
      validatorModule := root.constructedModule "Validator"
      contextModule := root.subjectModule
      contextExpression := root.subjectModule ++ ".subject.selection.context" }
    let source ← match RoundDescriptors.source root.artifacts.producer root.artifacts.validator output with
      | .ok source => pure source
      | .error reason => Lean.throwError reason
    sources := sources ++ [(output.moduleName, source)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `regressionSources) : List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  ZkcSecurity.Generation.Roots.writeSources directory regressionSources

end TestsSecurity.GenerateRoundDescriptors
