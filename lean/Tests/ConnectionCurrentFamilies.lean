import Tests.ConnectionFamilyMetrics
import Tests.ReusableAggregateTwoBatchesConnection
import ZkcExamples.Structured.Generated.Connections.Gkr

/-! Current exported participants use the shared body families at every actual
application. No old complete root or per-call body derivation is a prerequisite.
The generic audit inspects both alignment and extent fields, retaining the
existing full-return simulation and independent route-coverage consumers. -/
open Zkc.Construction
open ZkcTools.ConstructionBindings

noncomputable section

namespace Tests.ConnectionCurrentFamilies

audit_family_interfaces
audit_family_root Tests.ReusableAggregateTwoBatchesConnection.producer 1
audit_family_root Tests.ReusableAggregateTwoBatchesConnection.validator 1
audit_family_root ZkcExamples.Structured.Generated.Connections.Gkr.producer 2
audit_family_root ZkcExamples.Structured.Generated.Connections.Gkr.validator 3

example (model : Zkc.Source.Structured.DomainModel)
    (environment : Domain.Environment model.toCarriers) :=
  ZkcExamples.Structured.Generated.Connections.Gkr.producer.simulation model environment

example (model : Zkc.Source.Structured.DomainModel)
    (environment : Domain.Environment model.toCarriers) :=
  ZkcExamples.Structured.Generated.Connections.Gkr.validator.simulation model environment

example (model : Zkc.Source.Structured.DomainModel)
    (environment : Domain.Environment model.toCarriers) :=
  ZkcExamples.Structured.Generated.Connections.Gkr.producerFacts.coverage model environment

example (model : Zkc.Source.Structured.DomainModel)
    (environment : Domain.Environment model.toCarriers) :=
  ZkcExamples.Structured.Generated.Connections.Gkr.validatorFacts.coverage model environment

#print axioms ZkcExamples.Structured.Generated.Connections.Gkr.producer
#print axioms ZkcExamples.Structured.Generated.Connections.Gkr.validator
end Tests.ConnectionCurrentFamilies
