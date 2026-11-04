module

public import ZkcSecurityExamples.Generated.Components.SmallSumcheckSources
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SmallSumcheck
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcSecurity.Examples.Generated.Components.SmallSumcheckSources.original
abbrev imported : Imported original := ZkcSecurity.Examples.Generated.Components.SmallSumcheckSources.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SmallSumcheckPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "public_sum").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "public_sum" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producer, ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validator
    exports "sha256:a97cec552c7c3eb40577b93eb195965de358090ac6b786cd718ffae4847ed51e", "sha256:9b4215eb172dd7fe907314e8e67a47018f55fca07693b1cda96da6538128699c", "sha256:c7698d09e1962c0b0c5d5f13ece4ce9fd307f824bab26e86bbd696e7932f84aa"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "reduce.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SmallSumcheck
