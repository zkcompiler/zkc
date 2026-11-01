module

public import ZkcExamples.Structured.Generated.Bindings.SampledAbortInputs
public import ZkcExamples.Construction.Generated.SampledAbortPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SampledAbort
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SampledAbort
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SampledAbortData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SampledAbortInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SampledAbortPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "equality").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "equality" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SampledAbort.producer, ZkcExamples.Structured.Generated.Connections.SampledAbort.validator
    exports "sha256:0fd013bed60b984fd92953aa9d7feff8aa2ea209e322d64796c038248d02a406", "sha256:cd3f5646e727dd4c28d28b86755bebc84f9a046a33377a053a04dfa20bfa3478", "sha256:caa06563e059ff6f25e35bf8b5904098520de72e147bd43ad7442b00eb2e2cd5"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SampledAbort
