module

import ZkcSecurity.Generation.ConstructionBindingsCatalogue
meta import ZkcSecurity.Generation.ConstructionBindingsCatalogue

/-! Actual-yield derivation controls for both production roots and both roles.
The catalogue supplies the unchanged source/family choices; these are mutations
of untrusted candidate layout metadata, never additional installation data. -/
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 50000
namespace TestsSecurity.ArtifactSlotsGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Generation

private meta def accepted {α : Type} (result : Except String α) : Lean.Elab.Command.CommandElabM α :=
  match result with
  | .ok value => pure value
  | .error reason => Lean.throwError m!"{reason}"

private meta def refuses {α : Type} (expected : String) (result : Except String α) :
    Lean.Elab.Command.CommandElabM Unit :=
  match result with
  | .error reason => unless reason == expected do Lean.throwError m!"expected {expected}, got {reason}"
  | .ok _ => Lean.throwError m!"accepted invalid candidate: {expected}"

run_cmd do
  for root in ← Roots.evaluateSelections do
    let program ← accepted (Zkc.Source.Structured.check root.snapshot)
    let shared ← accepted (ConstructionBindings.source program root.artifacts.validator
      root.artifacts.producer "Candidate" root.sourceModule root.pairModule)
    let explicitShared ← accepted (ConstructionBindings.source program root.artifacts.validator
      root.artifacts.producer "Candidate" root.sourceModule root.pairModule .sharedTemplate)
    unless shared == explicitShared && !shared.contains "derive_artifact_binding" &&
        !shared.contains "respectTransparency" && shared.contains "body_instance" &&
        !shared.contains "body_correspondence" do
      Lean.throwError "production default must select shared proofs without occurrence derivation"
    let derived ← accepted (ConstructionBindings.source program root.artifacts.validator
      root.artifacts.producer "Candidate" root.sourceModule root.pairModule .checkedDerivation)
    unless derived.contains "derive_artifact_binding" && !derived.contains "theorem body_instance" &&
        derived.contains "body_correspondence" && derived.contains "outputs_derived" do
      Lean.throwError "explicit derivation must certify the actual body and output interface"
    let layout ← accepted (ZkcTools.ConstructionBindings.analyze program root.artifacts.validator)
    for (producer, artifact) in [(false, root.artifacts.validator), (true, root.artifacts.producer)] do
      let selected ← accepted (ZkcTools.ConstructionBindings.analyzeWithContext program layout.context artifact)
      for loop in selected.loops do
        let references ← if producer then do
          pure (← accepted (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.producerOutputs selected.context.suite artifact loop.instruction)).references
        else do
          pure (← accepted (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.verifierOutputs selected.context.suite artifact loop.instruction)).references
        unless references == loop.yielded do Lean.throwError "selected outputs differ from actual yields"
        let replace (yielded : List Nat) := { artifact with instructions := (artifact.instructions.mapIdx
          fun index instruction => if index == loop.instruction then
            { instruction with operation := .loop loop.site loop.maximum yielded } else instruction) }
        refuses "construction-binding-loop-yield-sort"
          (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.loopYieldLayout (replace loop.yielded.tail) loop.instruction)
        refuses "construction-binding-loop-yield-reference"
          (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.loopYieldLayout (replace [1000000]) loop.instruction)
        refuses "construction-binding-loop-yield-sort"
          (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.loopYieldLayout (replace loop.yielded.reverse) loop.instruction)
        if producer then
          refuses "construction-binding-producer-output-abi"
            (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.producerOutputs "wrong-suite" artifact loop.instruction)
        else
          refuses "construction-binding-verifier-output-abi"
            (ZkcExamples.Structured.SumcheckArtifacts.ArtifactOutputs.verifierOutputs "wrong-suite" artifact loop.instruction)
    for method in [ConstructionBindings.ProofMethod.sharedTemplate, .checkedDerivation] do
      let .error _ := ConstructionBindings.source program root.artifacts.validator
          { root.artifacts.producer with policy := { root.artifacts.producer.policy with suite := "wrong-suite" } }
          "Candidate" root.sourceModule root.pairModule method
        | Lean.throwError "wrong policy accepted"
  Lean.logInfo "PASS explicit proof methods, exact actual yields, both roots/roles, arity/sort/reference/suite/policy refusals"

end TestsSecurity.ArtifactSlotsGeneration
