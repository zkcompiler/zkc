module

public import Zkc.Realization.QueryControllerReturn

@[expose] public section
set_option autoImplicit false
namespace Tests.QueryControllerReturnPrefix
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def parentLayout : RecordProjection.Layout := ⟨"Parent", "Record", .cons .index .nil⟩
def frameBody (count : Nat) := QueryContinuation.loadInstructions "SavedParent" count 14 8 4
def frame (count : Nat) : QueryContinuation.Loaded (frameBody count) := ⟨"SavedParent", count, 14, 8, 4, rfl⟩
def lookupPlacement (count : Nat) : RecordLookup.Placement := ⟨14 + 6 + count, 14 + 5 + count, 17, 9, "parent"⟩
def lookupBody (count : Nat) := RecordLookup.instructions ⟨3, parentLayout.type⟩ (lookupPlacement count) ++
  RecordProjection.instructions parentLayout (14 + 6 + count + 2) (RecordProjection.allFields parentLayout.fields)
def lookup (count : Nat) : RecordLookupProjection.Recognized (lookupBody count) :=
  ⟨_, _, ⟨⟨3, parentLayout.type⟩, lookupPlacement count, rfl⟩,
    ⟨parentLayout, 14 + 6 + count + 2, RecordProjection.allFields parentLayout.fields, rfl⟩, rfl, rfl, rfl⟩
def state := List.range 9
def body (count : Nat) := RequiredIndices.constantInstructions 10 3 7 "continuation" ++
  RequiredIndices.constantInstructions 12 5 0 "kind" ++ frameBody count ++
  IndexLiterals.instructions [3] ++ lookupBody count
def checked (count : Nat) : ReturnPrefix.Recognized (body count) :=
  ⟨10, state, 7, 3, "continuation", 0, 5, "kind", frameBody count, frame count,
    lookupBody count, lookup count, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def header : Header := ⟨⟨9, 17, 19, 7, 0⟩, 0, 1, 5⟩
def parent (model : DomainModel) (rows : Nat) : model.Value parentLayout.type := (rows, ())
def stores (model : DomainModel) (count : Nat)
    (record : model.Value (QueryContinuation.layout "SavedParent" count).type) : Domain.Environment model.toCarriers :=
  [.data ⟨.sequence (QueryContinuation.layout "SavedParent" count).type,
    QueryContinuation.frameData "SavedParent" count, [record]⟩]
def environment (model : DomainModel) (count : Nat)
    (record : model.Value (QueryContinuation.layout "SavedParent" count).type) (rows : Nat) :
    Domain.Environment model.toCarriers :=
  header.encode (stores model count record) ++
    [.data ⟨.sequence parentLayout.type, rfl, [parent model rows]⟩]

theorem recognized_first : (ReturnPrefix.recognize 10 state (body 0)).isSome = true := by decide +kernel
theorem recognized_later : (ReturnPrefix.recognize 10 state (body 2)).isSome = true := by decide +kernel

/-- The child is instance 17 at position 19. Parent lookup instead uses the
actual saved instance 0, retaining arbitrary outer coordinates and prior replies. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (count outer outerInstance position rows : Nat) (answers : List Nat)
    (record : model.Value (QueryContinuation.layout "SavedParent" count).type)
    (encoded : QueryContinuation.Encodes "SavedParent" count
      ⟨outer, outerInstance, 0, position, answers⟩ record) :
    ∃ recovered, QueryContinuation.Encodes "SavedParent" count
        ⟨outer, outerInstance, 0, position, answers⟩ recovered ∧
      Nonempty (Original.Simulation Eq (fun _ live ↦ environment model count record rows <+: live)
        (.done (ReturnPrefix.projected (checked count) model rfl (environment model count record rows)
          recovered ⟨outer, outerInstance, 0, position, answers⟩ (parent model rows)))
        (Domain.evaluate model program context (body count) (environment model count record rows))) := by
  exact (checked count).simulation model program context header (stores model count record)
    (environment model count record rows) rfl rfl rfl rfl
    (by change 7 < indexLimit; decide) (by change 0 < indexLimit; decide)
    [record] ⟨outer, outerInstance, 0, position, answers⟩ ⟨record, rfl, encoded⟩ rfl rfl
    (RecordProjection.allFields_local _ rfl) [parent model rows] (parent model rows) rfl rfl
    (by change 3 < indexLimit; decide)

/-- Loading the parent using the current child's same-typed instance is rejected. -/
theorem wrong_parent_instance :
    (ReturnPrefix.recognize 10 state
      (RequiredIndices.constantInstructions 10 3 7 "continuation" ++
        RequiredIndices.constantInstructions 12 5 0 "kind" ++ frameBody 0 ++ IndexLiterals.instructions [3] ++
        RecordLookup.instructions ⟨3, parentLayout.type⟩ ⟨20, 19, 1, 9, "parent"⟩ ++
        RecordProjection.instructions parentLayout 22 (RecordProjection.allFields parentLayout.fields))).isNone = true := by
  decide +kernel

theorem wrong_frame_slot :
    (ReturnPrefix.recognize 10 state
      (RequiredIndices.constantInstructions 10 3 7 "continuation" ++
        RequiredIndices.constantInstructions 12 5 0 "kind" ++
        QueryContinuation.loadInstructions "SavedParent" 0 14 8 1 ++
        IndexLiterals.instructions [3] ++ lookupBody 0)).isNone = true := by decide +kernel

#print axioms actual
#print axioms wrong_parent_instance
#print axioms wrong_frame_slot
end Tests.QueryControllerReturnPrefix
