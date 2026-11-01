module

public import ZkcSecurityExamples.Generated.Components.SmallSumcheckSources
public import ZkcExamples.Construction.Generated.SmallSumcheckPair
public import ZkcSecurity.Bindings.Models.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
public import ZkcSecurityTools.PairConstruction
public import ZkcSecurity.Bindings.Subjects.ChargeSites

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
  bind_authored_subject "public_sum" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SmallSumcheck.producer, ZkcExamples.Structured.Generated.Connections.SmallSumcheck.validator
    exports "sha256:2570cea125278771a8451ddc403d67d3cd7080315e457c4adc175a89508e1356", "sha256:5592d46a92e6c1df4f875dcee0566bb3e5bba510580b3bd2de6e35e511fbee4d", "sha256:319f01c59dea31eafdcc8512da7a195a34173c5ffbfd558c91d56b9093ba3108"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "reduce.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SmallSumcheck
