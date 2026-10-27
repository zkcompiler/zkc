module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs
public import ZkcExamples.Construction.Generated.SchnorrRandomizedPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

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
  bind_authored_subject "knowledge"
    exports "sha256:96e7911cc0127e0d751223fec8d3d4fb6f2b6f518f1fd884290251e35893be4a", "sha256:6ac5ef190edef56bcd19e0fa7d0ad425e84a79b58ead4a9d3ff3552eeaaf6dc4", "sha256:81f6400d41f8d2cf31323c0f8f248e8de498b261a98b32a44253eae3854bd87c"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrRandomized
