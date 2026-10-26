module

public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckSources
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

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
  bind_authored_subject "public_sum"
    exports "sha256:fb282fe4e154be4758a77367ab78fbf1ee2208fc7b228265bfade3b0156c38ea", "sha256:55df6c32aa4373247b79a57ba0d6619723e9c259e4faae2f9b14f907e5bbb353", "sha256:ca64cb6b215b4df039f48121ab4fc732b77003ab43c072755123dd5f746028c0"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "reduce.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SmallSumcheck
