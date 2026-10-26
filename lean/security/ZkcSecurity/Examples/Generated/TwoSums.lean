module

public import ZkcSecurity.Examples.Generated.Components.TwoSumsSources
public import ZkcExamples.Construction.Generated.TwoSumsPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.TwoSums
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcSecurity.Examples.Generated.Components.TwoSumsSources.original
abbrev imported : Imported original := ZkcSecurity.Examples.Generated.Components.TwoSumsSources.imported
abbrev artifacts := ZkcExamples.Construction.Generated.TwoSumsPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "public_sums").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "public_sums"
    exports "sha256:b7c445ced5507c57ef64313edb9e3a4e9871246ae79cd06e70f6fbf45cba856d", "sha256:2746cb64f9b490c75c9050a5e0059c6535325f49b007428c2b0d92fe6f1c18ef", "sha256:8a3ad598b0ef67b7f790a34afde2c4a8d5d7ceb148dc99535fe7b32e4f3c22d9"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "left.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "right.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.TwoSums
