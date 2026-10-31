module

public import ZkcSecurityExamples.Generated.Components.TwoSumsSources
public import ZkcExamples.Construction.Generated.TwoSumsPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.TwoSums
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

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
  bind_authored_subject "public_sums" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.TwoSums.producer, ZkcExamples.Structured.Generated.Connections.TwoSums.validator
    exports "sha256:d599edea4215f7f3349457a06480c86d19cb7492ed5f0707264e9159367dc939", "sha256:13fa19f0bd32f0e4ac65649705b74d2b4844368ab5cdc210c789c84c0bd3e77d", "sha256:60fa4320e8a4e3b5fc39cdbdd68fc181c7128971935ececba23be11dbc18db35"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "left.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "right.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.TwoSums
