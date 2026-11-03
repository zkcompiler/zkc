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
    exports "sha256:55105f4d5526d39bfeca9641e23ea8190f32e1a825de33f3b38161c6f682669b", "sha256:23577d145366394a27786c97ecc656c3de2ccb8c2727d669ee2c4a2e3f3c40cb", "sha256:ac9bb6e59b78eeffc6dcd14a1f8a75d71d5cbe40b1a09e2c9b54c05fe926065b"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SampledAbort
