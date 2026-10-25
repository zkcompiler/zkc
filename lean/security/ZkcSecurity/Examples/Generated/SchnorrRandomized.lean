module

public import ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs
public import ZkcExamples.Construction.Generated.SchnorrRandomizedPair
public import ZkcSecurity.Domains.PrimeField
public import ZkcSecurity.Tools.PairConstruction
public import ZkcSecurity.Claims.SourceChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SchnorrRandomized
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SchnorrRandomizedInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SchnorrRandomizedPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "knowledge").toOption.get (by decide +kernel)

def inputPolicy : ZkcSecurity.Claims.HonestPair.InputPolicy imported.program.payload.entry.inputs :=
  ⟨[]⟩

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" using inputPolicy
    exports "sha256:7c4214ba8b6291c17f70289eda113d07b9d5a25c95aa1e3e9e1986189559364e", "sha256:71cfe9cd5353284e034ba7dc2f3605b6a31b594a5972032d744058925f2d50e2", "sha256:06815be04bad322a8148c076445cbf9d981b16c9cde0996b3af7ccb8e47c1ca4"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrRandomized
