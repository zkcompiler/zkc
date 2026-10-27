module

public import ZkcExamples.Structured.Generated.Bindings.SampledAbortInputs
public import ZkcExamples.Construction.Generated.SampledAbortPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

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
    exports "sha256:245ab21ea13d02b2b1442402628ec178eca23df3aef0537c7dbc863fac8c90eb", "sha256:cd254b61ffeccb77cdc3da4e4137bcb376fdf21b320a23e41e5c7522606eb141", "sha256:78a29ecdc5b44a0609257409d1043cf63a8a4f37ee32c539614cedc360c97fda"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SampledAbort
