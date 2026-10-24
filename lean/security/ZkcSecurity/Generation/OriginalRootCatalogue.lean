module

public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue
public import ZkcTools.StructuredSource.OriginalRoot
public meta import ZkcTools.StructuredSource.OriginalRoot
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs

@[expose] public section

/-! Original realization generation reuses the production root selections.
The installed source Sumcheck body is the one explicit family choice. Root
bodies, helper selectors, sites, bounds and continuation layouts are derived. -/
namespace ZkcSecurity.Generation.OriginalRootCatalogue
open ZkcTools.StructuredSource.OriginalRoot

run_cmd do
  let mut sources : List (String × String) := []
  for root in ← Roots.evaluateSelections do
    let program ← match Zkc.Source.Structured.check root.snapshot with
      | .ok program => pure program
      | .error reason => throwError "{root.name}: admission failed: {reason}"
    let moduleName := "ZkcExamples.Structured.Generated.Original." ++ root.name
    let generated ← match source program { moduleName, sourceModule := root.sourceModule } with
      | .ok text => pure text
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(moduleName, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

end ZkcSecurity.Generation.OriginalRootCatalogue
