module

public import Zkc.Applications.Security.Generation.Roots.Catalogue
public meta import Zkc.Applications.Security.Generation.Roots.Catalogue
public import Zkc.Tools.Verification.StructuredSource.Methods.SumcheckRoot
public meta import Zkc.Tools.Verification.StructuredSource.Methods.SumcheckRoot
public import Zkc.Applications.IR.Structured.Generated.Bindings.SmallSumcheckInputs
public import Zkc.Applications.IR.Structured.Generated.Bindings.TwoSumsInputs

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
    let moduleName := "Zkc.Applications.IR.Structured.Generated.Original." ++ root.name
    let namespaceName := "ZkcExamples.Structured.Generated.Original." ++ root.name
    let generated ← match source program {
        moduleName, namespaceName
        sourceModule := root.sourceModule, sourceNamespace := root.sourceNamespace
        libraries := installedLibraries } with
      | .ok text => pure text
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(moduleName, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

end ZkcSecurity.Generation.OriginalRootCatalogue
