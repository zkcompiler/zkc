module

public import Zkc.Claims.Registry
public import Zkc.Source.Structured.ContractBinding

@[expose] public section

/-! Interactive declarations are retained and structurally resolved even while
their registered security models have no interpretation. No such request is
silently treated as a compiled soundness request. -/

set_option autoImplicit false
namespace Zkc.Claims
open Zkc.Source Zkc.Source.Structured

structure InteractiveSubject where
  reference : SubjectRef
  interactive : reference.stage = .interactive
  noArtifacts : reference.artifacts = []
  snapshot : Snapshot
  imported : Imported snapshot
  owner : ContractBinding imported
  entry : owner.protocol = imported.program.payload.entry
  clauseIndex : Fin owner.contract.clauses.length
  target : (owner.clause clauseIndex).kind = .target
  acceptancePort : Fin owner.protocol.outputs.length
  acceptanceRole : Fin owner.protocol.roles.length
  boolean : owner.protocol.outputs.get acceptancePort = .boolean
  decision : (owner.clause clauseIndex).decision =
    some ⟨.output, acceptancePort.val, owner.protocol.roles.get acceptanceRole⟩

namespace InteractiveSubject

def targetReference (subject : InteractiveSubject) : Wire.TargetRef :=
  .retained subject.owner.contract.owner subject.clauseIndex.val (subject.owner.clause subject.clauseIndex).name

def acceptance (subject : InteractiveSubject) : Wire.Acceptance :=
  ⟨true, subject.acceptancePort.val, subject.acceptanceRole.val, []⟩

def check (subject : InteractiveSubject) (request : Wire.Request) : Except ResolutionError Unit := do
  if request.subject != subject.reference then throw .subjectMismatch
  if !request.target.matches subject.targetReference then throw .targetMismatch
  if request.accept != subject.acceptance then throw .acceptanceMismatch

/-- These versions are registered, and their missing interpretations are
explicit. New interactive meanings can replace them in their owning package. -/
def properties : Registry (PropertyExport InteractiveSubject) := ⟨[
  ⟨⟨"completeness", 0⟩, "zkc.property.interactive-completeness/0", none⟩,
  ⟨⟨"special_soundness", 0⟩, "zkc.property.interactive-special-soundness/0", none⟩]⟩

def resolveRequest (models : Registry Unit) (subject : InteractiveSubject) (request : Wire.Request) :
    Except ResolutionError (Except Incomplete (Resolved properties reference subject request)) :=
  match subject.check request with
  | .error error => .error error
  | .ok () => match models.lookup request.model.identifier with
    | .error error => .error error
    | .ok _ => resolve properties reference subject request

end InteractiveSubject
end Zkc.Claims
