module

public import ZkcExamples.Structured.Generated.Bindings.SequentialSigmaInputs
public import ZkcExamples.Construction.Generated.SequentialSigmaPair
public import ZkcSecurity.Domains.PrimeField
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

def inputPolicy : ZkcSecurity.Claims.HonestPair.InputPolicy imported.program.payload.entry.inputs :=
  ⟨[]⟩

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "equality" using inputPolicy
    exports "sha256:36528f90ea9b2feb3d9ea3d63813736fa064cbb8656470399350d97818b67c19", "sha256:92de401d591a49027238d1a9e37fa62fe16c2a54700176abc80408c44387d3fe", "sha256:0f2535f2d50045c763b398aa75e12e077fbe506c201fb4246a5c9893eed31cee"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SequentialSigma
