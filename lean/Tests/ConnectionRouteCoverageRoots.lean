import Zkc.Construction.ConnectionRouteCoverageRoot
import ZkcExamples.Structured.Generated.Connections.SchnorrRandomized
import ZkcExamples.Structured.Generated.Connections.BatchOpening

/-! Actual retained roots consume one generic produced fact. No protocol
coverage scripts, input restrictions or new nominal-model axioms are supplied. -/
set_option autoImplicit false
noncomputable section
namespace Tests.ConnectionRouteCoverageRoots
open Zkc.Source.Structured Zkc.Construction
open ZkcExamples.Structured.Generated.Connections

def schnorrProducer := SchnorrRandomized.producer.facts
def schnorrValidator := SchnorrRandomized.validator.facts
def batchProducer := BatchOpening.producer.facts
def batchValidator := BatchOpening.validator.facts

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  schnorrProducer.coverage model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  schnorrValidator.coverage model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  batchProducer.coverage model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  batchValidator.coverage model physical

-- These all-input laws include malformed ABI rows before source actions.
example (model : DomainModel) : Original.RouteCoverage SchnorrRandomized.producerRouting [] []
    (SchnorrRandomized.producer.occurrenceSource model []) := schnorrProducer.coverage model []
example (model : DomainModel) : Original.RouteCoverage BatchOpening.validatorRouting [] []
    (BatchOpening.validator.occurrenceSource model []) := batchValidator.coverage model []

example (model : DomainModel) : SchnorrRandomized.producer.occurrenceSource model [] = .halt .refused := rfl
example (model : DomainModel) : BatchOpening.validator.occurrenceSource model [] = .halt .refused := rfl

#print axioms ConnectionRoot.RootCertificate.routeCoverage
#print axioms ConnectionRoot.RootCertificate.facts
end Tests.ConnectionRouteCoverageRoots
