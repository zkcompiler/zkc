module

public import ZkcSecurityExamples.Generation.Roots.Catalogue
public meta import ZkcSecurityExamples.Generation.Roots.Catalogue
public import ZkcTools.StructuredSource.Methods.SumcheckRoot
public meta import ZkcTools.StructuredSource.Methods.SumcheckRoot
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

@[expose] public section

/-! Original realization generation reuses the production root selections.
The installed Sumcheck method owns the template and typed static selection. Root
bodies, helper selectors, sites, bounds and continuation layouts are derived. -/
namespace ZkcSecurity.Generation.OriginalRootCatalogue
open ZkcTools.StructuredSource.OriginalRoot ZkcTools.StructuredSource.Methods.SumcheckRoot

/-- Method installation is shared by every selected root, including both
SmallSumcheck and TwoSums. No root name selects a library template. -/
def installedLibraries := [sumcheckLibrary]

run_cmd do
  let mut sources : List (String × String) := []
  for root in ← Roots.evaluateSelections do
    let program ← match Zkc.Source.Structured.check root.snapshot with
      | .ok program => pure program
      | .error reason => throwError "{root.name}: admission failed: {reason}"
    let moduleName := "ZkcExamples.Structured.Generated.Original." ++ root.name
    let generated ← match source program {
        moduleName
        sourceModule := root.sourceModule
        libraries := installedLibraries } with
      | .ok text => pure text
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(moduleName, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

end ZkcSecurity.Generation.OriginalRootCatalogue
