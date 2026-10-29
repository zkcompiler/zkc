module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs
public import ZkcExamples.Construction.Generated.SchnorrRandomizedPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SchnorrRandomized
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
  bind_authored_subject "knowledge" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.producer, ZkcExamples.Structured.Generated.Connections.SchnorrRandomized.validator
    exports "sha256:d6dba60869f15565c7b0b23bdeb1087f42f015329b1a3100b0819a75df8e7272", "sha256:711dcf284e700ee23fd8c232d7b80311975d80dedb92de63ea13f1d3cee98502", "sha256:be7f8a6fa933d9a8979a999ef083f3cd4cec0767f75c19d67ca03bbdaa83d628"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrRandomized
