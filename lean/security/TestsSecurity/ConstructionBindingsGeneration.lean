module

import Tests.ConstructionBindingsAnalysis
meta import Tests.ConstructionBindingsAnalysis
import ZkcSecurity.Generation.ConstructionBindingsCatalogue
meta import ZkcSecurity.Generation.ConstructionBindingsCatalogue
meta import ZkcSecurity.Generation.Roots.Catalogue
meta import ZkcSecurity.Generation.ConstructionBindings
meta import ZkcSecurity.Generation.ConstructionBindingsRoots

/-! The production catalogue is the sole root selection. Analysis is a
proposal: final source and structural proof modules are checked separately. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
namespace TestsSecurity.ConstructionBindingsGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcTools.ConstructionBindings
open ZkcSecurity.Generation

run_cmd do
  let roots ← Roots.evaluateSelections
  for root in roots do
    let .ok program := Structured.check root.snapshot | Lean.throwError "source admission"
    Tests.ConstructionBindingsAnalysis.run program root.artifacts.validator root.artifacts.producer
    let moduleName := "ZkcExamples.Structured.OriginalArtifacts." ++ root.name
    let .ok generated := ConstructionBindings.source program root.artifacts.validator root.artifacts.producer
      moduleName root.sourceModule root.pairModule | Lean.throwError "binding generation refused"
    let .ok renamed := ConstructionBindings.source program root.artifacts.validator root.artifacts.producer
      ("Renamed." ++ moduleName) root.sourceModule root.pairModule | Lean.throwError "namespace dispatch"
    unless generated.replace moduleName ("Renamed." ++ moduleName) == renamed do
      Lean.throwError "namespace affects applicability"
    let policy := { root.artifacts.producer.policy with suite := "changed" }
    match ConstructionBindings.source program root.artifacts.validator
        { root.artifacts.producer with policy := policy } moduleName root.sourceModule root.pairModule with
    | .error "construction-binding-policy-mismatch" => pure ()
    | _ => Lean.throwError "policy mismatch accepted"
    let .ok layout := analyze program root.artifacts.validator | Lean.throwError "layout refused"
    match ConstructionBindingsRoots.source program root.artifacts.validator layout 2
        moduleName moduleName ("ZkcExamples.Structured.Generated.Original." ++ root.name) "unused" with
    | .error "construction-binding-root-role" => pure ()
    | _ => Lean.throwError "unsupported root role accepted"
  let outputs := ConstructionBindingsCatalogue.sources
  unless outputs.length == roots.length * 4 do Lean.throwError "output inventory"
  unless outputs.all (fun (_, source) =>
      !source.contains "Examples.Components" && !source.contains "pattern17" &&
      !source.contains "pattern23" && !source.contains "RoundDescriptors" &&
      !source.contains "sorry" && !source.contains "admit" && !source.contains "native_decide") do
    Lean.throwError "legacy certificate authority or unchecked proof in generated output"
  Lean.logInfo "PASS construction bindings: production roots, naming, policy and output authority"

end TestsSecurity.ConstructionBindingsGeneration
