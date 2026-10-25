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

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge"
    exports "sha256:9c80af7a4bb2c0ef32406d6f46e6c798e6337660c8113549d2fb4d99295383c3", "sha256:e0d004e3f67b14b90b78378e915975ff79c2217e20fded9ce7177c8f019775ca", "sha256:a228f7d50badb2529797b0da349a91fce652fc927f2ee99656583357b9eb7d2c"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndAliased
