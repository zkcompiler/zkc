module

public import Zkc.Construction.DomainExecution

@[expose] public section

/-! The scalar oracle interface uses the six static fields of an occurrence.
Nominal execution retains dynamic coordinates; this projection belongs only
at the installed scalar handler boundary. It does not identify random-oracle
games or authorize erasing coordinates from the nominal transcript. -/
set_option autoImplicit false
namespace Zkc.Construction.Origin

/-- Remove a coordinate suffix only after the six static occurrence fields.
A site, role or other data field may itself have the spelling `indices`. -/
def withoutCoordinates (origin : Origin) : Origin :=
  { origin with event := match origin.event with
    | kind :: entry :: site :: port :: contract :: owner :: "indices" :: _ =>
        [kind, entry, site, port, contract, owner]
    | fields => fields }

@[simp] theorem withoutCoordinates_entry (origin : Origin) :
    origin.withoutCoordinates.entry = origin.entry := rfl

@[simp] theorem withoutCoordinates_request (origin : Origin) :
    origin.withoutCoordinates.request = origin.request := rfl

@[simp] theorem withoutCoordinates_message (entry site sender receiver : String) :
    (message entry site sender receiver).withoutCoordinates = message entry site sender receiver := rfl

@[simp] theorem withoutCoordinates_query (entry site port contract owner : String) (request : Request) :
    (query entry site port contract owner request).withoutCoordinates =
      query entry site port contract owner request := rfl

/-- Every static template occurrence has six fields. Only its appended suffix
is projected, for arbitrary coordinate values and static field contents. -/
theorem withoutCoordinates_atCoordinates (origin : Origin) (coordinates : List Nat)
    (static : origin.event.length = 6) :
    (Domain.atCoordinates origin coordinates).withoutCoordinates = origin := by
  rcases origin with ⟨entry, fields, request⟩
  rcases fields with _ | ⟨a, fields⟩
  · simp at static
  rcases fields with _ | ⟨b, fields⟩
  · simp at static
  rcases fields with _ | ⟨c, fields⟩
  · simp at static
  rcases fields with _ | ⟨d, fields⟩
  · simp at static
  rcases fields with _ | ⟨e, fields⟩
  · simp at static
  rcases fields with _ | ⟨f, fields⟩
  · simp at static
  have empty : fields = [] := by
    apply List.length_eq_zero_iff.mp
    simpa using static
  subst fields
  cases coordinates <;> rfl

end Zkc.Construction.Origin
