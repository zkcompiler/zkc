module

public import ZkcTools.ConstructionBindings.Admission
public import ZkcExamples.Structured.Generated.Connections.Schnorr

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section
namespace Tests.ConnectionAdmissionBuilder
open Zkc.Construction
open ZkcExamples.Structured.Generated.Connections.Schnorr

theorem automatic : ConnectionAdmission.Required program context .validator validatorArtifact := by
  derive_source_connection

theorem imported : ConnectionAdmission.Required program context .validator validatorArtifact := by
  derive_source_connection using validator

/- The same producer is usable inside an optional record field. The nested
`exact` can annotate its proposition; metadata is not a different requirement. -/
def optional : Option (PLift (ConnectionAdmission.Required program context .validator validatorArtifact)) := by
  exact some ⟨by derive_source_connection⟩

example : optional.isSome = true := rfl

#print axioms automatic
#print axioms imported
end Tests.ConnectionAdmissionBuilder
