import ZkcExamples.Structured.Generated.Connections.BatchOpening

/-! The retained native plain aggregate export uses the same root proposer as
scalar protocols. Arbitrary nominal records, complete aggregate returns and
malformed physical rows stay inside the common simulation theorem. No
commitment-security property or aggregate encoder is assumed here. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace Tests.RetainedAggregateConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings

open ZkcExamples.Structured.Generated.Connections.BatchOpening

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 0 producerArtifact)
      (InputFrames producer.inputs.abi program.payload.entry.inputs physical)
      (producer.source model physical)
      (Domain.participant model program context producerArtifact physical) := producer.simulation model physical

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 1 validatorArtifact)
      (InputFrames validator.inputs.abi program.payload.entry.inputs physical)
      (validator.source model physical)
      (Domain.participant model program context validatorArtifact physical) := validator.simulation model physical

example (model : DomainModel) : validator.source model [] = .halt .refused := rfl

#print axioms producer
#print axioms validator
end Tests.RetainedAggregateConnection
