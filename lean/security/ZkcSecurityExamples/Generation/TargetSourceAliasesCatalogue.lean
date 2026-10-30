module

public import ZkcSecurityExamples.Generation.Roots.Catalogue
public meta import ZkcSecurityExamples.Generation.Roots.Catalogue
public import ZkcTools.StructuredSource.MathematicsAliases
public meta import ZkcTools.StructuredSource.MathematicsAliases

@[expose] public section

/-! Source mathematics aliases use the existing production target selections.
There is no second target list or root-name dispatch. The parent pipeline owns
stage ordering and the final regeneration inventory. -/
namespace ZkcSecurity.Generation.TargetSourceAliasesCatalogue

run_cmd do
  let mut sources : List (String × String) := []
  for root in ← Roots.evaluateSelections do
    let program ← match Zkc.Source.Structured.check root.snapshot with
      | .ok program => pure program
      | .error reason => throwError "{root.name}: admission failed: {reason}"
    let moduleName := "ZkcExamples.Structured.Generated.Mathematics." ++ root.name
    let generated ← match ZkcTools.StructuredSource.MathematicsAliases.source program root.target
        { moduleName, sourceModule := root.sourceModule } with
      | .ok text => pure text
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(moduleName, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

end ZkcSecurity.Generation.TargetSourceAliasesCatalogue
