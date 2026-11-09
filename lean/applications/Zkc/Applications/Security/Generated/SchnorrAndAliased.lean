module

public import Zkc.Applications.IR.Structured.Generated.Bindings.SchnorrAndAliasedInputs
public import Zkc.Applications.IR.Construction.Generated.SchnorrAndAliasedPair
public import Zkc.Verification.Bindings.Models.PrimeField
public import Zkc.Applications.IR.Structured.Generated.Connections.SchnorrAndAliased
public import Zkc.Tools.Verification.PairConstruction
public import Zkc.Verification.Bindings.Subjects.ChargeSites

@[expose] public section

/-! Generated fixed request data and checked Subject assembly. -/
namespace ZkcSecurity.Examples.Generated.SchnorrAndAliased
open Zkc.Source.Structured
set_option maxRecDepth 50000
set_option maxHeartbeats 16000000
noncomputable section

abbrev original : Snapshot := ZkcExamples.Structured.Generated.Bindings.SchnorrAndAliasedData.snapshot
abbrev imported : Imported original := ZkcExamples.Structured.Generated.Bindings.SchnorrAndAliasedInputs.imported
abbrev artifacts := ZkcExamples.Construction.Generated.SchnorrAndAliasedPair.artifacts

def selected : Zkc.Construction.AuthoredPair.Selection original :=
  (Zkc.Construction.AuthoredPair.select original artifacts "knowledge").toOption.get (by decide +kernel)

def subject : ZkcSecurity.Claims.HonestPair.Subject
    (ZkcSecurity.Domains.PrimeField.blsScalarModel) original imported selected := by
  bind_authored_subject "knowledge" with_registry Zkc.Source.Structured.OpaqueRegistry.empty
    connections ZkcExamples.Structured.Generated.Connections.SchnorrAndAliased.producer, ZkcExamples.Structured.Generated.Connections.SchnorrAndAliased.validator
    exports "sha256:e1ff4f63caeca365121d61f45f7535ea10c414dfcfbd9888c2c105be7c4ae106", "sha256:8d7237fd873f97e3b0861974969bafb196c65b94b9dd952162d67cbe63e40b40", "sha256:450965840fa3085291262fd5e44b38e790d23ef101ad3630336bbb35c12ce6cc"

abbrev validatorArtifacts := subject.validatorArtifacts
abbrev validatorCompiled := subject.validatorCompiled

def validatorSites : List (ZkcSecurity.Claims.Domain.ChargeSite validatorCompiled) :=
  []

def validatorSubject := subject.validatorSubject validatorSites

end
end ZkcSecurity.Examples.Generated.SchnorrAndAliased
