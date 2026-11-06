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
    exports "sha256:d7e4dd28461c16c9d8d294768991358538b733e3e8214b44dc606ee46af4031f", "sha256:ee9b21fe16f97b7a083f8c3c0ebde8cf3c2fdab80c47e61849715bdfc4af1d0e", "sha256:70bb6aa114cdee5f89f786f0f9fa95ff19c876d143707dcf592e7d1014769ee7"

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
