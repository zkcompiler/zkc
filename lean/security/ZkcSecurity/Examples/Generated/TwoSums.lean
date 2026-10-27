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
  bind_authored_subject "public_sums" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    exports "sha256:7d2908d3289b179b13c3f076a28469bfe48e31f4555c3de227a2cecd0b4850b5", "sha256:e3a01344251e0dec9cd26c2f3ffa5196803446d2dc690e151ec9a5c7cfd1dc6c", "sha256:3dd7c3e1657ea6b89f6a25cc378ae3a11b33a85d13c27cb88a4e31793ec4137f"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "left.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "right.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.TwoSums
