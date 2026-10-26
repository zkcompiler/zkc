module

public import ZkcSecurity.Generation.Roots.Catalogue
public meta import ZkcSecurity.Generation.Roots.Catalogue
public import ZkcSecurity.Generation.ConstructionBindings
public meta import ZkcSecurity.Generation.ConstructionBindings
public import ZkcTools.ConstructionBindings.Source
public meta import ZkcTools.ConstructionBindings.Source
public import ZkcSecurity.Generation.ConstructionBindingsRoots
public meta import ZkcSecurity.Generation.ConstructionBindingsRoots

@[expose] public section

/-! Reuse the unchanged production selections. No per-root structural metadata
or mathematical choices are introduced in the catalogue or in tests. -/
namespace ZkcSecurity.Generation.ConstructionBindingsCatalogue

run_cmd do
  let mut sources : List (String × String) := []
  for root in ← Roots.evaluateSelections do
    let program ← match Zkc.Source.Structured.check root.snapshot with
      | .ok program => pure program
      | .error reason => throwError "{root.name}: {reason}"
    let moduleName := "ZkcExamples.Structured.OriginalArtifacts." ++ root.name
    let generated ← match ConstructionBindings.source program root.artifacts.validator
        root.artifacts.producer moduleName root.sourceModule root.pairModule with
      | .ok text => pure text
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(moduleName, generated)]
    let producerModule := "ZkcExamples.Structured.Generated.OriginalArtifacts." ++ root.name ++ "ProducerSource"
    let producerSource ← match ZkcTools.ConstructionBindings.Source.source program producerModule
        ("ZkcExamples.Structured.Generated.Original." ++ root.name) with
      | .ok text => pure text
      | .error reason => throwError "{root.name}: {reason}"
    sources := sources ++ [(producerModule, producerSource)]
    let layout ← match ZkcTools.ConstructionBindings.analyze program root.artifacts.validator with
      | .ok layout => pure layout
      | .error reason => throwError "{root.name}: {reason}"
    for (role, artifact) in [(0, root.artifacts.producer), (1, root.artifacts.validator)] do
      let selected ← match ZkcTools.ConstructionBindings.analyzeWithContext program layout.context artifact with
        | .ok layout => pure layout
        | .error reason => throwError "{root.name}: {reason}"
      let rootModule := moduleName ++
        (if role == 0 then "ProducerRoot" else "ValidatorRoot")
      let generated ← match ConstructionBindingsRoots.source program artifact selected role rootModule moduleName
          ("ZkcExamples.Structured.Generated.Original." ++ root.name) producerModule with
        | .ok text => pure text
        | .error reason => throwError "{root.name}: {reason}"
      sources := sources ++ [(rootModule, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))

end ZkcSecurity.Generation.ConstructionBindingsCatalogue
