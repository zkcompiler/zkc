module

public import ZkcSecurityExamples.Gkr.Canonical
public import ZkcExamples.Construction.Generated.GkrPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.Gkr
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Realizations.Gkr.Generated.Subject
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcSecurity.Realizations.Gkr.Canonical.original
abbrev imported : Imported original := ZkcSecurity.Realizations.Gkr.Canonical.imported
abbrev artifacts := ZkcExamples.Construction.Generated.GkrPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "circuit_outputs").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "circuit_outputs" with_registry (ZkcSecurity.Realizations.Gkr.Relations.registry ZkcSecurity.Domains.PrimeField.blsScalarModel)
    connections ZkcExamples.Structured.Generated.Connections.Gkr.producer, ZkcExamples.Structured.Generated.Connections.Gkr.validator
    exports "sha256:22db60d5e42b2a5a78aff7282b43e48ecb93b1d1a7ffddb23cadc6ebaaa82a2e", "sha256:7773e8e729a9f5d6e30497791f245f726e0a72601b50b2a6835b7d3d591eb4bd", "sha256:2a65472a388ebca4ed47dcb1f7879a903b7a1c9f0f4dfe1b308f561b113b0e37"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "output").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "left.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "right.challenge").toOption.get (by decide +kernel),
   (ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "line_challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Realizations.Gkr.Generated.Subject
