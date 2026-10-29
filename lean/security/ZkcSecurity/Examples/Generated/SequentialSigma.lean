module

public import ZkcExamples.Structured.Generated.Bindings.SequentialSigmaInputs
public import ZkcExamples.Construction.Generated.SequentialSigmaPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcExamples.Structured.Generated.Connections.SequentialSigma
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SequentialSigma
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SequentialSigmaData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SequentialSigmaInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SequentialSigmaPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "equality").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "equality" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SequentialSigma.producer, ZkcExamples.Structured.Generated.Connections.SequentialSigma.validator
    exports "sha256:031968ff98150ab3135b51b6981204bc781827aff630060125ed443075d93f7a", "sha256:9cb4463c1dabf465daaebec1d46752a4f0722d09c73edf99c7455c85249039a7", "sha256:95018adc0e2eb63434260cec7b4c0bd642c7f95abb22c1e7c1e2125b4793a57d"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SequentialSigma
