module

public import Zkc.Applications.Security.Generated.Components.SmallSumcheckSources
public import Zkc.Applications.IR.Construction.Generated.SmallSumcheckPair
public import Zkc.Verification.Bindings.Models.PrimeField
public import Zkc.Applications.IR.Structured.Generated.Connections.SmallSumcheck
public import Zkc.Tools.Verification.PairConstruction
public import Zkc.Verification.Bindings.Subjects.ChargeSites

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
    exports "sha256:76491dbfe0d0d4ce888fe45e0b7bfe329ae6446201a1bca31ad864304035c97f", "sha256:694479c30ff4872aab5f26f7ca9c6bb483a49e2acbee415f27dfc47330bf29c9", "sha256:2443672f4de15c8fbc2cde0400ef343ff08637c40b14fded6d6d716ee8cad54b"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  [(ZkcSecurity.Claims.Domain.ChargeSite.selectLabel validatorCompiled "reduce.challenge").toOption.get (by decide +kernel)]

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SmallSumcheck
