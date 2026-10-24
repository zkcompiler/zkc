module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs
public import ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SchnorrAndRandomized
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "knowledge").toOption.get (by decide +kernel)

def inputPolicy : ZkcSecurity.Claims.HonestPair.InputPolicy imported.program.payload.entry.inputs :=
  ⟨[]⟩

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" using inputPolicy
    exports "sha256:38886e48c95e08ed0368765f6c4e3b6b8a8927007ad5a3781ecf11d436abf420", "sha256:76ad20b63266a9e52b6749f0195ac2966a0188df052b4b3b1c134a9b3ae6c798", "sha256:20c88621b68939166296bc2930e1bea4e09639256324390f09af8c4e4e8a983a"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndRandomized
