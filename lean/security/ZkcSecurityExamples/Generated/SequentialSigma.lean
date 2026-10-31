module

public import ZkcExamples.Structured.Generated.Bindings.SequentialSigmaInputs
public import ZkcExamples.Construction.Generated.SequentialSigmaPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SequentialSigma
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

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
  bind_authored_subject "equality" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SequentialSigma.producer, ZkcExamples.Structured.Generated.Connections.SequentialSigma.validator
    exports "sha256:237ba35f3d71a8e9f6178f2935229003e7c88095d46bb8ae4e3048b1403cda24", "sha256:5c63a7f05f75933feea15973ca2dbd8f6c628cfca17d10f576aea3d815c56534", "sha256:743b0334c6f98b2abd0cd04e0fa70d1c82847a662fa8f407cfef8421b0d70913"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SequentialSigma
