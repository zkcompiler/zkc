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
  bind_authored_subject "equality"
    exports "sha256:ef0af2b02f1269fc2cac4e9ef71209246df5ce9213ef8a8bb5e83b4f31681776", "sha256:8d4e7ec899c4e488a4971d02c0f5ac3f1dca21b56ced3c72fb9a9995785b49b6", "sha256:ede1faf8f1083b2aa69314a7993cb77fbda0ebf48ecd47eb42d072ac33471884"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SampledAbort
