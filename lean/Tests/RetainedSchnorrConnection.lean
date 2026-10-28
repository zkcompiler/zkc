import ZkcTools.ConstructionBindings.Root
import ZkcTools.ConstructionBindings.RootRoutes
import ZkcExamples.Construction.SchnorrArtifact
import ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator
import ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer

/-! Actual retained compiler exports. Both roles use one root proposer and
one route discovery function, without reordered instructions or per-instance
source equations. The supplied numbers are runtime capability associations.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
noncomputable section
namespace Tests.RetainedSchnorrConnection
open Zkc.Source Zkc.Source.Structured Zkc.Construction ConnectionRoot
open ZkcTools.ConstructionBindings

abbrev program := ZkcExamples.Construction.SchnorrProof.program
abbrev context := ZkcExamples.Construction.SchnorrProof.context
abbrev validatorArtifact := ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.artifact
abbrev producerArtifact := ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer.artifact

def capabilities : List (Nat × Nat) := [(3, 13), (4, 73)]
def validatorRouting : Original.Routing :=
  RootRoutes.routing program.snapshot context .validator capabilities validatorArtifact
    (by decide +kernel)
def producerRouting : Original.Routing :=
  RootRoutes.routing program.snapshot context .producer capabilities producerArtifact
    (by decide +kernel)

def validator : RootCertificate program validatorRouting 1 validatorArtifact := by
  derive_root_connection
    target (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.body model program context)
    correspondence (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.body_eq model program context)
    services capabilities

def producer : RootCertificate program producerRouting 0 producerArtifact := by
  derive_root_connection
    target (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer.body model program context)
    correspondence (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer.body_eq model program context)
    services capabilities

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 1 validatorArtifact)
      (InputFrames validator.inputs.abi program.payload.entry.inputs physical)
      (validator.source model physical)
      (Domain.participant model program context validatorArtifact physical) :=
  validator.simulation model physical

example (model : DomainModel) (physical : Domain.Environment model.toCarriers) :
    Original.Simulation (Original.CompleteReturns program.payload.entry.signature context 0 producerArtifact)
      (InputFrames producer.inputs.abi program.payload.entry.inputs physical)
      (producer.source model physical)
      (Domain.participant model program context producerArtifact physical) :=
  producer.simulation model physical

example : (RootRoutes.propose program.snapshot context .validator [(3, 13)] validatorArtifact).toOption = none := by
  decide +kernel
example : (RootRoutes.propose program.snapshot context .producer [(4, 73)] producerArtifact).toOption = none := by
  decide +kernel

/-- Omitted source message routes cannot be rescued by matching refusals. -/
example : True := by
  fail_if_success
    have : RootCertificate program { validatorRouting with messages := [] } 1 validatorArtifact := by
      derive_root_connection
        target (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.body model program context)
        correspondence (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedValidator.body_eq model program context)
        services capabilities
  trivial

example : True := by
  fail_if_success
    have : RootCertificate program { producerRouting with deliveries := [] } 0 producerArtifact := by
      derive_root_connection
        target (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer.body model program context)
        correspondence (fun model => ZkcExamples.Structured.Generated.Constructed.SchnorrRandomizedProducer.body_eq model program context)
        services capabilities
  trivial

end Tests.RetainedSchnorrConnection
