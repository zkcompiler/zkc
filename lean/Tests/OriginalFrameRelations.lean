module

public import Zkc.Construction.OriginalFrameRelations

@[expose] public section
set_option autoImplicit false
namespace Tests.OriginalFrameRelations
open Zkc.Source Zkc.Construction Zkc.Construction.Original
variable {carriers : Structured.Carriers}

/-- A non-GKR client retains an absent component and a private capability while
arbitrary later allocations extend the physical frame. -/
theorem extended_input (value handle : Nat) (suffix : Domain.Environment carriers) :
    ValuesHolds ([.data (.index value)] ++ suffix)
      [.data 0, .absent, .capability handle]
      (.cons (some value) (.cons none (.cons (some handle) .nil)) :
        Values (Component carriers.Value) [.index, .boolean, .service "random"]) := by
  apply valuesHolds_of_captures (captured := [.data (.index value)])
  · intro reference present
    simp only [List.mem_cons, List.not_mem_nil, or_false, Location.data.injEq,
      reduceCtorEq, or_false] at present
    subst reference
    simp
  · simp [ValuesHolds, ComponentHolds, Domain.Value.decode, Domain.Payload.value]
  · exact ArtifactBinding.captures_append _ _

/-- A hidden original component cannot be certified at a physical data slot. -/
theorem absent_is_not_data (frame : Domain.Environment carriers) (reference : Nat) :
    ¬ ValuesHolds frame [.data reference]
      (.cons none .nil : Values (Component carriers.Value) [.index]) := by
  simp [ValuesHolds, ComponentHolds]

end Tests.OriginalFrameRelations
