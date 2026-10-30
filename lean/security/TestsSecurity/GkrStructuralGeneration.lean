import ZkcExamples.Structured.Generated.Connections.Gkr
import ZkcSecurityExamples.Gkr.CanonicalCompleteness
import ZkcSecurityExamples.Gkr.CanonicalSoundness
import ZkcSecurityExamples.Gkr.LayoutVariant

/-! The actual pair uses the shared root connection. Physical layout changes
remain distinct formal artifacts; no alternate native identity is asserted. -/
set_option autoImplicit false
set_option maxRecDepth 50000
noncomputable section
namespace TestsSecurity.GkrStructuralGeneration
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Realizations.Gkr
open ZkcExamples.Structured.Generated.Connections.Gkr

example : capabilities = [(7, 7)] := by kernel_rfl
example : validator.inputs.abi.locations[7]? = some (.capability 7) := by kernel_rfl
example : producer.inputs.abi.locations[7]? = some .absent := by kernel_rfl
example : validator.inputs.abi.locations[7]? ≠ some (.capability 0) := by
  change some (Original.Location.capability 7) ≠ some (.capability 0)
  decide

example : LayoutVariant.validator ≠ ZkcExamples.Construction.Generated.GkrPair.Validator.participant := LayoutVariant.validator_changed
example : LayoutVariant.producer ≠ ZkcExamples.Construction.Generated.GkrPair.Producer.participant := LayoutVariant.producer_changed

-- Missing physical inputs refuse before the source participant is invoked.
example (model : DomainModel) : validator.source model [] = .halt .refused := by kernel_rfl
example (model : DomainModel) : producer.source model [] = .halt .refused := by kernel_rfl

-- Full all-input simulation and reached-source coverage are available before
-- any property premise. The pair property retains both full return relations.
#check producer.simulation
#check validator.simulation
#check producerFacts
#check validatorFacts
#check producerConnected
#check validatorConnected
#check CanonicalCompleteness.abi_readback
#check CanonicalSoundness.reductionExport
#print axioms CanonicalCompleteness.compiled_ideal_complete
#print axioms CanonicalSoundness.reductionExport
end TestsSecurity.GkrStructuralGeneration
