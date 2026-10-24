module

public import TestsSecurity.ArtifactSlotsLayout
public meta import TestsSecurity.ArtifactSlotsLayout
public import ZkcSecurity.Generation.ConstructionBindingsCatalogue
public meta import ZkcSecurity.Generation.ConstructionBindingsCatalogue
public import ZkcTools.StructuredSource.Constructed
public meta import ZkcTools.StructuredSource.Constructed

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ArtifactSlotsGenerate
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Generation

private meta def accepted {α : Type} (result : Except String α) : Lean.Elab.Command.CommandElabM α :=
  match result with
  | .ok value => pure value
  | .error reason => Lean.throwError m!"{reason}"

run_cmd do
  let roots ← Roots.evaluateSelections
  let some root := roots.head? | Lean.throwError "no production construction selection"
  let program ← accepted (check root.snapshot)
  let validator := ArtifactSlotsLayout.shiftCallback root.artifacts.validator
  let producer := ArtifactSlotsLayout.shiftCallback root.artifacts.producer
  -- The fixture is the first production selection, with its body layout changed.
  -- No family choice or callback output index is installed in a test catalogue.
  unless root.sourceModule == "ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs" do
    Lean.throwError "layout fixture no longer matches first production selection"
  let pairModule := "TestsSecurity.ArtifactSlotsLayout"
  let bindingModule := "ZkcSecurity.Examples.Generated.OriginalArtifacts.LayoutControl"
  let mut sources := []
  for (role, artifact) in [("Validator", validator), ("Producer", producer)] do
    let moduleName := "ZkcExamples.Structured.Generated.Constructed.LayoutControl" ++ role
    let generated ← accepted (ZkcTools.StructuredSource.Constructed.source artifact
      ⟨moduleName, pairModule, pairModule ++ "." ++ role ++ ".participant"⟩)
    sources := sources ++ [(moduleName, generated)]
  let generated ← accepted (ConstructionBindings.source program validator producer
    bindingModule root.sourceModule pairModule)
  sources := sources ++ [(bindingModule, generated)]
  let layout ← accepted (ZkcTools.ConstructionBindings.analyze program validator)
  let original ← accepted (ZkcTools.ConstructionBindings.analyze program root.artifacts.validator)
  let shifted ← accepted (ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.verifierOutputs layout.context.suite validator
    (← accepted (ZkcTools.ConstructionBindings.unique "control-loop" layout.loops)).instruction)
  let old ← accepted (ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.verifierOutputs original.context.suite root.artifacts.validator
    (← accepted (ZkcTools.ConstructionBindings.unique "control-loop" original.loops)).instruction)
  unless shifted.references != old.references do Lean.throwError "callback output references did not change"
  let producerLayout ← accepted (ZkcTools.ConstructionBindings.analyzeWithContext program layout.context producer)
  let oldProducerLayout ← accepted (ZkcTools.ConstructionBindings.analyzeWithContext program layout.context root.artifacts.producer)
  let shiftedProducer ← accepted (ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.producerOutputs layout.context.suite producer
    (← accepted (ZkcTools.ConstructionBindings.unique "control-loop" producerLayout.loops)).instruction)
  let oldProducer ← accepted (ZkcSecurity.Realizations.Sumcheck.ArtifactOutputs.producerOutputs layout.context.suite root.artifacts.producer
    (← accepted (ZkcTools.ConstructionBindings.unique "control-loop" oldProducerLayout.loops)).instruction)
  unless shiftedProducer.references != oldProducer.references do
    Lean.throwError "producer callback output references did not change"
  for (role, artifact) in [(0, producer), (1, validator)] do
    let selected ← accepted (ZkcTools.ConstructionBindings.analyzeWithContext program layout.context artifact)
    let moduleName := bindingModule ++ (if role == 0 then "ProducerRoot" else "ValidatorRoot")
    let generated ← accepted (ConstructionBindingsRoots.source program artifact selected role moduleName
      bindingModule ("ZkcExamples.Structured.Generated.Original." ++ root.name)
      ("ZkcExamples.Structured.Generated.OriginalArtifacts." ++ root.name ++ "ProducerSource"))
    sources := sources ++ [(moduleName, generated)]
  Lean.Elab.Command.elabCommand (← `(def $(Lean.mkIdent `sources) : List (String × String) := $(Lean.quote sources)))
  Lean.logInfo "PASS shifted callback SSA/output layout generation"

end TestsSecurity.ArtifactSlotsGenerate

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: ArtifactSlotsGenerate OUTPUT_DIRECTORY")
  ZkcSecurity.Generation.Roots.writeSources directory TestsSecurity.ArtifactSlotsGenerate.sources
