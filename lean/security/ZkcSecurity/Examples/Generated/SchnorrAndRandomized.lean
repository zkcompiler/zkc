module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrAndRandomizedInputs
public import ZkcExamples.Construction.Generated.SchnorrAndRandomizedPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

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
  bind_authored_subject "knowledge"
    exports "sha256:caa1f6f2253041b1592fe89382e19e68e6da204292e0fbe054e00c110dcb41b8", "sha256:e8cce346ce796be712570644bbae6f774319992b5fffde40d5c1955d96d46461", "sha256:b729a1578eb23887e0ad9f21588336bf68891c7ea413669aa99e8481b3033dc3"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndRandomized
