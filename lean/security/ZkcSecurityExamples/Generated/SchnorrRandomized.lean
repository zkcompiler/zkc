module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs
public import ZkcExamples.Construction.Generated.SchnorrRandomizedPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SchnorrRandomized
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SchnorrRandomized
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SchnorrRandomizedPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "knowledge").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.producer, ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validator
    exports "sha256:0cbec0aa0f21d140a9cd26730a2c5a60b9b3dd2561a25939a885e66c3abc4065", "sha256:a15a52d45559cfdb484682a8d11eba4d3a117182960019d049c39a9884d80162", "sha256:ff8b1b8df4735c08917191fc12272ecf05648514498bc8c8ede71647f44d16e4"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrRandomized
