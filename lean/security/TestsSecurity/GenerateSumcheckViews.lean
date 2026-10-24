import ZkcSecurity.Generation.Roots.Catalogue
import ZkcSecurity.Generation.SumcheckViews

/-! Retired matcher comparison fixtures, outside production receipt generation. -/
namespace TestsSecurity.GenerateSumcheckViews
open ZkcSecurity.Generation ZkcSecurity.Generation.Roots

run_cmd do
  let mut sources := []
  for root in ← evaluateSelections do
    let output : SumcheckViews.Output := {
      moduleName := root.componentModule "ValidatorView"
      subjectModule := root.subjectModule
      validatorModule := root.constructedModule "Validator"
      roundsModule := root.componentModule "Rounds" }
    let source ← match SumcheckViews.source root.artifacts.producer root.artifacts.validator output with
      | .ok source => pure source
      | .error reason => Lean.throwError reason
    sources := sources ++ [(output.moduleName, source)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `regressionSources) : List (String × String) := $(Lean.quote sources)))

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "expected output directory")
  ZkcSecurity.Generation.Roots.writeSources directory regressionSources

end TestsSecurity.GenerateSumcheckViews
