module

public import Zkc.Realization.ClearStorageRead
public import Tests.ClearStorage

@[expose] public section

namespace Tests.ClearStorageRead
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization

abbrev kind (domain : String) : OracleKind := .table (.field domain) (some 2)

def layout (domain : String) : ClearStorage.Layout (kind domain) :=
  ⟨7, "field-word-record", "field-word-reference", ClearStorage.location 0 0, 0, [1]⟩

def word (model : DomainModel) (domain : String) (first second : model.Field domain) :
    PublishedWords.Word model (.field domain) :=
  ⟨kind domain, (ClearStorage.location 2 7).anchor, 2, 0, [1], ClearStorage.location 2 7, [first, second]⟩

def record (model : DomainModel) (domain : String) (first second : model.Field domain) :
    model.Value (layout domain).recordType := (2, 7, 2, 1, [first, second], ())

def state (model : DomainModel) (domain : String) (first second : model.Field domain) :
    PublishedWords.State model Unit := ⟨[⟨.field domain, word model domain first second⟩], ()⟩

theorem stored (model : DomainModel) (domain : String) (first second : model.Field domain) :
    ClearStorage.Stored (layout domain) (state model domain first second).words
      [record model domain first second] (7, 0) (word model domain first second) :=
  ClearStorage.stored_append (layout domain) [] [] (word model domain first second)
    (record model domain first second) ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fixed-size publication is read through an unsized handle, at any
query location and position. The same execution law covers refusal as well. -/
noncomputable def physical_read (model : DomainModel) (domain : String)
    (first second : model.Field domain) (position : Nat) (location : OracleLocation)
    (program : Program) (context : Context) :
    let environment : Domain.Environment model.toCarriers :=
      [.data ⟨.vector domain, rfl, [first, second]⟩, .data (.index 2), .data (.index position)]
    let request : OracleRead := ⟨.table (.field domain) none,
      (word model domain first second).anchor, position, location, []⟩
    Original.Simulation Eq (fun _ frame ↦ environment <+: frame)
      (((primitiveOutcome (I := closedInterface)
        (PublishedWords.read (E := Unit) request (state model domain first second)).outcome).interpret
          (closedLift (I := Domain.effects model.toCarriers))).bind
            (fun value ↦ .done (environment ++ [.data (.boolean true),
              .data ⟨.field domain, rfl, value⟩])))
      (Domain.evaluate model program context (TableRead.instructions domain ⟨3, 0, 1, 2, "read"⟩)
        environment) :=
  (stored model domain first second).read_simulation
    (by kernel_rfl) (by kernel_rfl) rfl position location [] program context _ 0 1 2 "read" rfl rfl rfl

set_option backward.isDefEq.respectTransparency false in
/-- Query coordinates are independent of the publication coordinates. The
anchor selects the already published word, and the query selects its second cell. -/
theorem query_at_new_location (model : DomainModel) (domain : String)
    (first second : model.Field domain) (location : OracleLocation) :
    (PublishedWords.read (E := Unit)
      ⟨.table (.field domain) none, (word model domain first second).anchor, 1, location, []⟩
      (state model domain first second)).outcome = .returned second := by
  have law := ClearStorage.published_read (word model domain first second)
    (state model domain first second) (by simp [state, PublishedWords.find]) rfl
    (by kernel_rfl) (by kernel_rfl) rfl 1 location [] (requestedShape := none) (E := Unit)
  simpa [word, TableRead.read_eq, indexLimit, Domain.closedOutcome] using law

#print axioms physical_read
#print axioms query_at_new_location
#print axioms ClearStorage.Stored.read_simulation
end Tests.ClearStorageRead
