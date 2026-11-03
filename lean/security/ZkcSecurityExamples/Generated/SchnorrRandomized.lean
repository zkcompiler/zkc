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
    exports "sha256:b1d9b0d6d172578cf23ab89ace9c0188e11d937ef8c332257abc922fefd828e1", "sha256:5b30d9853dbba84a9dad0cddda1afa54009f9a80782c01eb713682b1d2576d85", "sha256:34e9fc6980bda7ed3ee198856f30e2ecbcfb3bd5b5c9863ab2c1b9997cec0c35"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrRandomized
