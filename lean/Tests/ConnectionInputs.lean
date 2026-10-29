import ZkcTools.ConstructionBindings.Inputs
import Zkc.Construction.ConnectionPresence
import Zkc.Construction.ConnectionInputSchema

/-! Full ABI assembly with hidden data, a fixed capability, nominal data and
history. A changed service handle or a stale physical selector cannot match. -/
set_option autoImplicit false
namespace Tests.ConnectionInputs
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionInputs ConnectionFrame

def pattern : InputPattern [.service "random.f/0", .field "f", .index, .boolean] :=
  .cons (.capability "random.f/0" 73) (.cons .present (.cons .absent (.cons .present .nil)))
def locations : List Original.Location := [.capability 73, .data 1, .absent, .data 0]
def shape : Shape pattern locations := by derive_connection_inputs

def layout : Layout pattern.scope :=
  [.data (.present (.var (.there .here))), .data (.present (.var .here)), .history "suite"]
def initialized : InitialLayout pattern locations "suite" (some 2) 0 layout := by
  derive_connection_inputs

example (model : DomainModel) (value : model.Field "f") (accepted : Bool)
    (history : Domain.History model.toCarriers) :
    Holds model (.cons value (.cons accepted .nil)) history layout
      [.data (.boolean accepted), .data (.field "f" value), .transcript "suite" history] := by
  apply initialized.sound
  · rfl
  · exact ⟨rfl, ⟨⟨value, rfl, rfl⟩, rfl, ⟨accepted, rfl, rfl⟩, trivial⟩⟩
  · intro slot same
    cases same
    rfl

example (model : DomainModel) (frame : Domain.Environment model.toCarriers)
    (values : Values (Component model.Value) [.service "random.f/0", .field "f", .index, .boolean])
    (decoded : Original.ValuesHolds frame locations values) :
    ∃ binders : Binders model pattern.scope, pattern.environment model binders = values :=
  shape.binders frame values decoded

/-- error: input pattern does not match the fixed source ABI -/
#guard_msgs in
example : Shape pattern [.capability 91, .data 1, .absent, .data 0] := by
  derive_connection_inputs

/-- error: input frame cell has no matching source ABI input -/
#guard_msgs in
example : InitialLayout pattern locations "suite" (some 2) 0
    [.data (.present (.var .here)), .data (.present (.var (.there .here))), .history "suite"] := by
  derive_connection_inputs

/-- error: input history is not at its fixed slot or suite -/
#guard_msgs in
example : InitialLayout pattern locations "suite" (some 0) 0 layout := by
  derive_connection_inputs

def inputSorts : List ValueSort := [.data .boolean, .data (.field "f"), .transcript "suite"]

example : shape.sortsValid inputSorts = true := rfl
-- Same host carrier does not permit a different nominal field in this ABI.
example : shape.sortsValid [.data .boolean, .data (.field "other"), .transcript "suite"] = false := by decide
example : shape.sortsValid [.data .boolean] = false := by decide
example : shape.sortsValid [.data (.field "f"), .data .boolean, .transcript "suite"] = false := by decide

example (model : DomainModel) (frame : Domain.Environment model.toCarriers)
    (sorted : Domain.sortsMatch inputSorts frame = true) :
    ∃ binders : Binders model pattern.scope,
      Original.ValuesHolds frame locations (pattern.environment model binders) :=
  shape.binders_of_sorts rfl frame sorted

example (model : DomainModel) (frame : Domain.Environment model.toCarriers)
    (sorted : Domain.sortsMatch inputSorts frame = true) :
    Original.LocationsBound frame.length locations := shape.physicalBounds rfl sorted

-- Presence refinement cannot silently erase a source value with physical data.
example (model : DomainModel) (value : model.Field "f") (history : Domain.History model.toCarriers) :
    Holds model (.cons value (.cons (some value) .nil)) history
      (([.data (.input .here), .history "suite"] : Layout [.component (.field "f")]).map
        (Cell.presentAt (.input .here)))
      [.data (.field "f" value), .transcript "suite" history] := by
  exact Holds.presentAt (model := model) (scope := [.component (.field "f")])
    (binders := .cons (some value) .nil) (.input .here) value rfl
    (.cons ⟨value, rfl, rfl⟩ (.cons rfl .nil))

end Tests.ConnectionInputs
