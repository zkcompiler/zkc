module

public import ZkcSecurity.Realizations.Gkr.Canonical
public import ZkcExamples.Construction.Generated.GkrPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcExamples.Structured.Generated.Connections.Gkr
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

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
    exports "sha256:624ace13f9ec65913feab37af7f567746f268585252e9c3bb0708e61e84a70dd", "sha256:f829be33b7fbf7688a97068f3e195f109cc8021bc40f90719a27510f630d25fc", "sha256:fd0bdc7ff8c6e5279e5e0d89df36aa36b3a9180f4ac027c2afb3cd7b9de6bd4b"

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
