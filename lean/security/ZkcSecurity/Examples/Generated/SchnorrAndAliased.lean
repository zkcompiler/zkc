module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrAndAliasedInputs
public import ZkcExamples.Construction.Generated.SchnorrAndAliasedPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

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

def inputPolicy : ZkcSecurity.Claims.HonestPair.InputPolicy imported.program.payload.entry.inputs :=
  ⟨[]⟩

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" using inputPolicy
    exports "sha256:1f33ee8a49d46f936eb1b3b72b8b2d097a59b1937d6a163f02b1053a75011332", "sha256:8902ca80d29b3971edf4410abcce1e1566eec48a745a0cfa5415372ef5a8f775", "sha256:01a155c1f8aa9a388f6cdaa69ef53472372229c8d21ee859a2f20271b31881b8"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndAliased
