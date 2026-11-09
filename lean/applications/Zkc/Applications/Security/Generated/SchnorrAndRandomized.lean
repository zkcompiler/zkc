module

public import Zkc.Applications.IR.Structured.Generated.Bindings.SchnorrAndRandomizedInputs
public import Zkc.Applications.IR.Construction.Generated.SchnorrAndRandomizedPair
public import Zkc.Verification.Bindings.Models.PrimeField
public import Zkc.Applications.IR.Structured.Generated.Connections.SchnorrAndRandomized
public import Zkc.Tools.Verification.PairConstruction
public import Zkc.Verification.Bindings.Subjects.ChargeSites

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

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SchnorrAndRandomized.producer, ZkcExamples.Structured.Generated.Connections.SchnorrAndRandomized.validator
    exports "sha256:fbe81f8a9eb276cf6dc00761813f430392abec5cd44a02f21343f8177c940054", "sha256:3cd86bc674f743041408b3b107a8dd1b300beee7cbcc765570a06c60c0ee5a6a", "sha256:38a59057a8d034a39b94cc8cdc342fbb1864e5fd313b3017d089d167fdfa5070"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndRandomized
