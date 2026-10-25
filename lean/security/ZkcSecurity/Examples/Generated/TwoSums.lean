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

def inputPolicy : ZkcSecurity.Claims.HonestPair.InputPolicy imported.program.payload.entry.inputs :=
  ⟨[.cubeTable .here (.there (.there (.there (.there .here)))) 1, .cubeTable (.there .here) (.there (.there (.there (.there .here)))) 1, .boundedIndex (.there (.there (.there (.there .here)))) 4]⟩

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "public_sums" using inputPolicy
    exports "sha256:ff5b4060dd0ad94db9061d59d7560152b8db7dc820b1d25f3b358433a6e78732", "sha256:0bd526cfbc6d29aef756e4b0389d9fb6fe40d3ba76c557aab569266471957942", "sha256:f1110f3e53e1ab652a83adb2c5e4311a42961b4c21b4ed6c9ed6cbda3efe9fe0"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "left.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "right.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.TwoSums
