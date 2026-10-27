module

public import ZkcExamples.Structured.Generated.Bindings.SequentialSigmaInputs
public import ZkcExamples.Construction.Generated.SequentialSigmaPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SequentialSigma
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SequentialSigmaData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SequentialSigmaInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SequentialSigmaPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "equality").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "equality"
    exports "sha256:e9ff8c20566b330bb1b5df00ba30126efd31a093520c4cc720f1dc40ce5b0c9c", "sha256:5c144573b150513df26e9768e00d0d8548536354486af19fb7e5a77b17452a81", "sha256:13fb7afbb4546f82415496fd818604e481581c3d5043206ac37899a126aac09c"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SequentialSigma
