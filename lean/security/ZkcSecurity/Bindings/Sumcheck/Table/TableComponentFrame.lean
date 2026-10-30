module

public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentNominal

@[expose] public section

/-! Caller frame updates for the nominal table component. A frame can retain
the complete generated SSA environment and transcript. Its update is ordinary
caller data; every message and challenge still uses the same mathematical
table representation. No frame update can change the represented entries.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir

variable {F G Frame : Type} [Field F] [DecidableEq F]

abbrev FrameUpdate (F Frame : Type) [Field F] (field : String) :=
  {n : Nat} → Schedule field → PrefixState F Frame (n + 1) → (F × F) → F → Frame

noncomputable def programWithFrame (field : String) (update : FrameUpdate F Frame field) :
    Program (NominalField.signature F field) (Schedule field) (PrefixState F Frame) (Message.endpoints F) :=
  { program field with
    advance := fun schedule state message challenge =>
      { state.advance message challenge with frame := update schedule state message challenge } }

noncomputable def layoutWithFrame (field : String) (update : FrameUpdate F Frame field) :
    Layout (programWithFrame field update) where
  entries := PrefixState.entries
  shape := PrefixState.entries_shape
  advance _ state message challenge := PrefixState.advance_entries state message challenge
  claim _ _ _ _ := rfl

noncomputable def queriesWithFrame (field : String) (update : FrameUpdate F Frame field) :
    QueryInterface (programWithFrame field update) (NominalField.interface (G := G) field) where
  event schedule state _ := .challenge (schedule.query state.point.length)
  decode schedule state _ raw := by
    change Option F
    exact some (by simpa only [Domain.Raw, schedule.request _, Request.draw] using raw)
  challenge schedule state _ raw :=
    by simpa only [Domain.Raw, schedule.request _, Request.draw] using raw
  absorbed _ _ _ := rfl
  decoded schedule state message raw reply same := by
    dsimp only [programWithFrame, program] at same ⊢
    exact Option.some.inj same.symm

omit [DecidableEq F] in
theorem advance_frame (field : String) (update : FrameUpdate F Frame field)
    {n : Nat} (schedule : Schedule field) (state : PrefixState F Frame (n + 1))
    (message : F × F) (challenge : F) :
    ((programWithFrame field update).advance schedule state message challenge).frame =
      update schedule state message challenge := rfl

end ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
