module

public import Zkc.Construction.Projection
public import Zkc.Construction.DomainCorrespondence
public import Zkc.Source.Structured.OutputSelection

@[expose] public section

/-! Admission of exact constructed participants in either explicit profile.
The structural rule and projection check retain the original subject. Generic
semantic evidence uses full nominal Process equations (`Domain.Correspondence`).
Scalar consumers reuse this admission and require their own actual Domain
connection; admission alone supplies no execution correspondence. -/
set_option autoImplicit false
namespace Zkc.Construction
open Zkc.Source

def checkCompiled {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) : Except String Unit :=
  match checkExport original participant, exportContext original participant with
  | .ok (), some context => project imported.program context participant
  | .error error, _ => .error error
  | .ok (), none => .error "construction-context"

/-- An admission token is structural. Property consumers must additionally
supply the complete actual Process binding and their property-specific laws. -/
structure Checked {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) : Prop where
  checked : checkCompiled imported participant = .ok ()

/-- Typed return and public-input selection derived from the actual source. -/
structure Selection (outputs : List Structured.Ty) where
  context : Context
  position : Nat
  publics : List Structured.Ty
  slots : List Slot
  output : Var outputs .boolean

open Structured in
def select {original : Snapshot} (imported : Imported original) (participant : Participant) :
    Option (Selection imported.program.payload.entry.outputs) :=
  match exportContext original participant, exportAcceptance original participant,
      Var.decode imported.program.payload.entry.outputs .boolean participant.policy.acceptance with
  | some context, some position, some output =>
      some ⟨context, position,
        participant.policy.publicInputs.filterMap (imported.program.payload.entry.inputs[·]?),
        inputSlots context participant.policy imported.program.payload.entry.inputs, output⟩
  | _, _, _ => none

def Selection.check {original : Structured.Snapshot} (imported : Structured.Imported original)
    (selection : Selection imported.program.payload.entry.outputs) (participant : Participant) : Bool :=
  let entry := imported.program.payload.entry
  selection.publics.all (fun ty => !ty.isHandle) &&
    (decide (selection.position < (selection.context.dataPorts participant.returned).length) &&
    selection.publics.length == participant.policy.publicInputs.length &&
    Structured.inScope selection.context.validator entry.outputScopes selection.output &&
    Structured.scopePosition selection.context.validator entry.outputScopes selection.output == selection.position)

theorem select_sound {original : Structured.Snapshot} (imported : Structured.Imported original)
    (participant : Participant) {selection : Selection imported.program.payload.entry.outputs}
    (selected : select imported participant = some selection) :
    exportContext original participant = some selection.context ∧
      exportAcceptance original participant = some selection.position ∧
      selection.slots = inputSlots selection.context participant.policy imported.program.payload.entry.inputs := by
  unfold select at selected
  split at selected
  · rename_i context position output foundContext foundPosition _
    cases selected
    exact ⟨foundContext, foundPosition, rfl⟩
  · cases selected

end Zkc.Construction
