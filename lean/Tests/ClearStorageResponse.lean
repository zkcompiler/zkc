module

public import Zkc.Realization.ClearStorageResponse
public import Tests.ClearStorageRead

@[expose] public section
set_option autoImplicit false
namespace Tests.ClearStorageResponse
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization
open ClearStorageRead

def selections (domain : String) : List (RecordProjection.Selection (layout domain).fields) :=
  [⟨.index, .here⟩, ⟨.index, .there .here⟩, ⟨.index, .there (.there .here)⟩,
    ⟨.index, .there (.there (.there .here))⟩,
    ⟨.vector domain, .there (.there (.there (.there .here)))⟩]

def lookupPlacement : RecordLookup.Placement := ⟨10, 0, 1, 9, "constructor"⟩
def readPlacement : TableRead.Placement := ⟨18, 17, 15, 2, "rows"⟩
def responsePlacement : QueryResumption.Placement :=
  ⟨20, 6, 5, ⟨0, 1, 2, 3, 4⟩, ⟨0, 1, 2, 3, 4⟩, 8, 19,
    "phase", "kind", !["constructor", "instance", "position", "continuation", "frame"]⟩

theorem geometry (domain : String) : ClearStorage.ResponseGeometry
    (layout domain) (selections domain) lookupPlacement readPlacement responsePlacement :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, ⟨2, rfl, rfl⟩, ⟨4, rfl, rfl⟩⟩

def pending (position : Nat) : QueryResumption.Coordinates := ⟨7, 0, position, 3, 4⟩

def environment (model : DomainModel) (domain : String) (first second : model.Field domain)
    (position : Nat) (answers : List (model.Field domain)) : Domain.Environment model.toCarriers :=
  [.data (.index 7), .data (.index 0), .data (.index position), .data (.index 3), .data (.index 4),
    .data (.index 0), .data (.index 2), .data (.index 0),
    .data ⟨.sequence (.field domain), rfl, answers⟩,
    .data ⟨.sequence (layout domain).recordType, rfl, [record model domain first second]⟩]

/-- The actual complete arm consumes the immutable publication at arbitrary
query positions and preserves a retained store in its output. A fixed-size
word can be read through the unsized request. Every refusal is retained. -/
theorem actual_response (model : DomainModel) (domain : String)
    (first second : model.Field domain) (position : Nat) (answers : List (model.Field domain))
    (location : OracleLocation) (program : Program) (context : Context) :
    let env := environment model domain first second position answers
    let request : OracleRead := ⟨.table (.field domain) none,
      (word model domain first second).anchor, position, location, []⟩
    let retained : Domain.Environment model.toCarriers :=
      [.data ⟨.sequence (layout domain).recordType, rfl, [record model domain first second]⟩]
    Nonempty (Original.Simulation Eq (fun _ frame ↦ env <+: frame)
      (((primitiveOutcome (I := closedInterface)
          (PublishedWords.read (E := Unit) request
            (state model domain first second)).outcome).interpret
            (closedLift (I := Domain.effects model.toCarriers))).bind fun answer ↦
        QueryReadResponse.response model domain 0 2 0 (pending position) (pending position)
          answers answer [] retained)
      ((Domain.evaluate model program context
          ((layout domain).responseInstructions (selections domain)
            lookupPlacement readPlacement 0 responsePlacement) env).bind fun final ↦
        match Domain.read final (QueryResumption.outputReferences responsePlacement [] [9]) with
        | some values => .done values
        | none => .halt .refused)) := by
  apply (stored model domain first second).response_simulation
    (pending position) (pending position) (by kernel_rfl) none (by kernel_rfl) rfl location []
    (selections domain) (by
      intro selection present
      simp only [selections, List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with rfl | rfl | rfl | rfl | rfl <;> rfl)
    lookupPlacement readPlacement responsePlacement (geometry domain)
    program context rfl _ 0 rfl (by change 7 < indexLimit; decide) (by decide)
    _ rfl 2 0 answers [] [9] [] _
    rfl rfl rfl _ rfl rfl rfl
  exact .cons rfl rfl (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl (.cons rfl rfl .nil))))

/-- The leaf count and row count share a type. Reading the former as the
latter fails the source association even though the arm is well typed. -/
theorem leaf_count_is_not_rows (domain : String) :
    ¬ ClearStorage.ResponseGeometry (layout domain) (selections domain) lookupPlacement
      { readPlacement with rows := 16 } responsePlacement := by
  intro wrong
  obtain ⟨ordinal, selected, address⟩ := wrong.rows
  have ordinalEq : ordinal = 3 := by
    change 16 = 10 + 3 + ordinal at address
    omega
  subst ordinal
  have impossible : some (3 : Nat) = some 2 :=
    congrArg (fun choice ↦ choice.map (fun field ↦ field.field.index)) selected
  cases impossible

#print axioms actual_response
#print axioms leaf_count_is_not_rows
end Tests.ClearStorageResponse
