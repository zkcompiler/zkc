module

public import ZkcSecurityTools.Generation.Roots.Interface
public meta import ZkcSecurityTools.Generation.Roots.Interface
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcExamples.Construction.Generated.TwoSumsPair

@[expose] public section

/-! The closed production catalogue. Generic generators consume Selection;
only this client selects exact source artifacts and installed mathematics. -/
namespace ZkcSecurity.Generation.Roots
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.StructuredSource.Root

noncomputable def selections : List Selection := [
  { name := "SmallSumcheck"
    snapshot := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.snapshot
    helpers := ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.program.payload.definitions.map (·.name)
    artifacts := ZkcExamples.Construction.Generated.SmallSumcheckPair.artifacts
    target := "public_sum", mathematics := primeField
    formulaNamespace := "ZkcSecurity.Examples.Components.SmallSumcheck.Formula"
    registryExpression := "Zkc.Source.Structured.OpaqueRegistry.empty" },
  { name := "TwoSums"
    snapshot := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.snapshot
    helpers := ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.program.payload.definitions.map (·.name)
    artifacts := ZkcExamples.Construction.Generated.TwoSumsPair.artifacts
    target := "public_sums", mathematics := primeField
    formulaNamespace := "ZkcSecurity.Examples.Components.TwoSums.Formula"
    registryExpression := "Zkc.Source.Structured.OpaqueRegistry.empty" }]

/-- Materialize only closed selection data. Proof records and the source
interpreter are not reimplemented or evaluated by a second language. -/
meta unsafe def evaluateSelections : Lean.Elab.Command.CommandElabM (List Selection) :=
  Lean.Elab.Command.liftTermElabM do
    let expression ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce (Lean.mkConst ``selections)
    Lean.Meta.evalExpr (List Selection) (Lean.mkApp (Lean.mkConst ``List [0]) (Lean.mkConst ``Selection)) expression

/- A generated transport manifest exposes the author selections to the narrow
pipeline without duplicating a root list in Python or in a test module. -/
run_cmd do
  let mut manifest : List Lean.Json := []
  for root in ← evaluateSelections do
    manifest := manifest ++ [Lean.Json.mkObj [
      ("name", Lean.toJson root.name), ("target", Lean.toJson root.target),
      ("formulaNamespace", Lean.toJson root.formulaNamespace),
      ("model", Lean.toJson root.mathematics.model), ("sourceModule", Lean.toJson root.sourceModule),
      ("pairModule", Lean.toJson root.pairModule), ("subjectModule", Lean.toJson root.subjectModule),
      ("subjectNamespace", Lean.toJson root.subjectNamespace),
      ("aliasesModule", Lean.toJson (root.componentModule "Sources"))]]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `catalogueManifest) : String :=
    $(Lean.quote ((Lean.Json.arr manifest.toArray).compress))))


end ZkcSecurity.Generation.Roots
