module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrAndAliasedInputs
public import ZkcExamples.Construction.Generated.SchnorrAndAliasedPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SchnorrAndAliased
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SchnorrAndAliased
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SchnorrAndAliasedData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SchnorrAndAliasedInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SchnorrAndAliasedPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "knowledge").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SchnorrAndAliased.producer, ZkcExamples.Structured.Generated.Connections.SchnorrAndAliased.validator
    exports "sha256:b78ef55572e78298209c42ae3e72b1777c36d71264dc43b6fd4e5208804ae617", "sha256:3b65db8b0a00000dbbc7389ad9c9f1819af432ea515d17b4130454ebb6ba5cd2", "sha256:e73a4d6f32305c6cf1e0f514ee04ef8c700430bacee71a5f5bec9cd15b6f3ae3"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndAliased
