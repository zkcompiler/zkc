import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
import ZkcExamples.Structured.Generated.Connections.TwoSums

/-! Retained controls consume the production generated certificates. They do
not derive another copy of the same source/artifact connection in the test
suite. Both roles retain all nominal outputs and independent action coverage. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRetainedRoots
open Zkc.Source Zkc.Source.Structured Zkc.Construction

namespace Small
abbrev program := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.program
abbrev validatorArtifact := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validatorArtifact
abbrev producerArtifact := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producerArtifact
abbrev context := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.context
abbrev capabilities := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.capabilities
abbrev library := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.sourceLibrary
abbrev validatorRouting := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validatorRouting
abbrev producerRouting := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producerRouting
abbrev validator := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validator
abbrev producer := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producer
abbrev validatorFacts := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validatorFacts
abbrev producerFacts := ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producerFacts

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  validatorFacts.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  validatorFacts.coverage model physical
example (model : DomainModel) : validator.occurrenceSource model [] = .halt .refused := rfl
#print axioms validator
#print axioms validatorFacts

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  producerFacts.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  producerFacts.coverage model physical
example (model : DomainModel) : producer.occurrenceSource model [] = .halt .refused := rfl
#print axioms producer
#print axioms producerFacts
end Small

namespace Two
abbrev program := ZkcExamples.Structured.Generated.Connections.TwoSums.program
abbrev validatorArtifact := ZkcExamples.Structured.Generated.Connections.TwoSums.validatorArtifact
abbrev producerArtifact := ZkcExamples.Structured.Generated.Connections.TwoSums.producerArtifact
abbrev context := ZkcExamples.Structured.Generated.Connections.TwoSums.context
abbrev capabilities := ZkcExamples.Structured.Generated.Connections.TwoSums.capabilities
abbrev library := ZkcExamples.Structured.Generated.Connections.TwoSums.sourceLibrary
abbrev validatorRouting := ZkcExamples.Structured.Generated.Connections.TwoSums.validatorRouting
abbrev producerRouting := ZkcExamples.Structured.Generated.Connections.TwoSums.producerRouting
abbrev validator := ZkcExamples.Structured.Generated.Connections.TwoSums.validator
abbrev producer := ZkcExamples.Structured.Generated.Connections.TwoSums.producer
abbrev validatorFacts := ZkcExamples.Structured.Generated.Connections.TwoSums.validatorFacts
abbrev producerFacts := ZkcExamples.Structured.Generated.Connections.TwoSums.producerFacts

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  validatorFacts.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  validatorFacts.coverage model physical
example (model : DomainModel) : validator.occurrenceSource model [] = .halt .refused := rfl
#print axioms validator
#print axioms validatorFacts

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  producerFacts.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  producerFacts.coverage model physical
example (model : DomainModel) : producer.occurrenceSource model [] = .halt .refused := rfl
#print axioms producer
#print axioms producerFacts
end Two
end Tests.ConnectionRetainedRoots
