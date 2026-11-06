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
    exports "sha256:2a0351c54dc5de3d1b3cebb46e0172df3fff348683601797ad7fe58e349a2a96", "sha256:2bcc01b85b6ea57e3b71fb6c4f4fa3b7797ee4d1b1d0e09bfd1cda8fea18883e", "sha256:106ab6342905e53d8ecd73b1c1c87a5cd176a2019840a04ae705c7595c53bbf6"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "left.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "right.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.TwoSums
