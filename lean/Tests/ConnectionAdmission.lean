import Zkc.Construction.ConnectionCertificateAdmission
import ZkcExamples.Structured.Generated.Connections.SmallSumcheck

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace Tests.ConnectionAdmission
open Zkc.Construction
open ZkcExamples.Structured.Generated.Connections.SmallSumcheck

-- Selection is data-only and cannot depend on a chosen proof implementation.
theorem validator : ConnectionAdmission.Required program context .validator validatorArtifact :=
  ConnectionAdmission.ofRootCertificate
    ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validator (by kernel_rfl)

theorem producer : ConnectionAdmission.Required program context .producer producerArtifact :=
  ConnectionAdmission.ofRootCertificate
    ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producer (by kernel_rfl)

-- A direct semantic proof can use the same fixed requirement without exposing
-- its certificate or making the proof method part of the request meaning.
theorem direct (boundary : ConnectionAdmission.Boundary)
    (selected : ConnectionAdmission.select program context .validator validatorArtifact = .ok boundary)
    (proof : SourceConnection.Connected program boundary.routing context.validator boundary.abi validatorArtifact) :
    ConnectionAdmission.Required program context .validator validatorArtifact :=
  ConnectionAdmission.ofConnected selected proof

#print axioms validator
#print axioms producer
end Tests.ConnectionAdmission
