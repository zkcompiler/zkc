import Tests.ConnectionRetainedRoots

/-! Complete connections replace the earlier manually selected placements.
Both roles share the generated source library, use canonical capabilities and
actual target syntax, and derive full simulation and independent coverage.
No per-call layout, argument map, target slice or routing constant is authored.
-/
set_option autoImplicit false
noncomputable section
namespace Tests.RetainedSumcheckConnection
open Zkc.Source.Structured Zkc.Construction
open Tests.ConnectionRetainedRoots

example : Small.validator.library = Small.producer.library := rfl
example : Two.validator.library = Two.producer.library := rfl

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  Small.validatorFacts.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  Small.producerFacts.coverage model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  Two.validatorFacts.simulation model physical
example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  Two.producerFacts.coverage model physical

#print axioms Small.validator
#print axioms Small.producer
#print axioms Two.validator
#print axioms Two.producer
end Tests.RetainedSumcheckConnection
