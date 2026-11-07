module

public import Zkc.Realization.QueryControllerEnter

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.QueryControllerEnter
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization QueryController

def layout : RecordProjection.Layout :=
  ⟨"PublishedRows", "Record", .cons .index (.cons .index (.cons .index .nil))⟩
def selections := RecordProjection.allFields layout.fields
def placement : RecordLookup.Placement := ⟨11, 0, 1, 8, "anchor"⟩
def lookupBody := RecordLookup.instructions ⟨7, layout.type⟩ placement ++
  RecordProjection.instructions layout 13 selections
def lookup : RecordLookupProjection.Recognized lookupBody :=
  ⟨_, _, ⟨⟨7, layout.type⟩, placement, rfl⟩, ⟨layout, 13, selections, rfl⟩, rfl, rfl, rfl⟩
def state := List.range 8
def body := RequiredIndices.constantInstructions 9 5 0 "kind" ++ lookupBody ++
  DomainGuard.instructions 17 2 15 "domain" ++ Phase.instructions 2
def yielded := Phase.output state 18
def checked : BaseEntry.Recognized body yielded :=
  ⟨9, 0, 5, "kind", 2, 15, "domain", state, lookupBody, lookup, rfl, rfl, rfl, rfl, rfl⟩
def header (position : Nat) : Header := Header.initial 7 0 position
def record (model : DomainModel) (rows : Nat) : model.Value layout.type := (1, rows, 1, ())
def environment (model : DomainModel) (position rows : Nat) : Domain.Environment model.toCarriers :=
  (header position).encode [] ++ [.data ⟨.sequence layout.type, rfl, [record model rows]⟩]

theorem recognized : (BaseEntry.recognize 9 state body yielded).isSome = true := by decide +kernel

/-- Arbitrary positions and row bounds use the complete emitted entry, not
only a hand-picked successful guard. The immutable store is a caller capture,
while the returned controller retains its original eight header coordinates. -/
theorem actual (model : DomainModel) (program : Program) (context : Context) (position rows : Nat) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment model position rows <+: frame)
      (if DomainGuard.Accepted position rows then
        .done ({header position with phase := 2}.encode []) else .halt .refused)
      ((Domain.evaluate model program context body (environment model position rows)).bind fun final ↦
        match Domain.read final yielded with
        | some values => .done values
        | none => .halt .refused)) := by
  exact checked.simulation model program context (header position) []
    (environment model position rows) rfl rfl rfl (by decide) rfl
    (RecordProjection.allFields_local layout.fields rfl)
    0 [record model rows] (record model rows) rfl rfl rfl rfl (by decide) rows rfl

theorem in_range (model : DomainModel) (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment model 1 2 <+: frame)
      (.done ({header 1 with phase := 2}.encode []))
      ((Domain.evaluate model program context body (environment model 1 2)).bind fun final ↦
        match Domain.read final yielded with
        | some values => .done values
        | none => .halt .refused)) := by
  simpa only [show DomainGuard.Accepted 1 2 from by decide, ↓reduceIte] using
    actual model program context 1 2

theorem out_of_range (model : DomainModel) (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment model 2 2 <+: frame)
      (.halt .refused)
      ((Domain.evaluate model program context body (environment model 2 2)).bind fun final ↦
        match Domain.read final yielded with
        | some values => .done values
        | none => .halt .refused)) := by
  simpa only [show ¬ DomainGuard.Accepted 2 2 from by decide, ↓reduceIte] using
    actual model program context 2 2

theorem oversized_rows (model : DomainModel) (program : Program) (context : Context) :
    Nonempty (Original.Simulation Eq (fun _ frame ↦ environment model 0 indexLimit <+: frame)
      (.halt .refused)
      ((Domain.evaluate model program context body (environment model 0 indexLimit)).bind fun final ↦
        match Domain.read final yielded with
        | some values => .done values
        | none => .halt .refused)) := by
  simpa only [show ¬ DomainGuard.Accepted 0 indexLimit from by decide, ↓reduceIte] using
    actual model program context 0 indexLimit

/-- Same-typed coordinate changes cannot silently alter the pending query. -/
theorem wrong_position :
    (BaseEntry.recognize 9 state
      (RequiredIndices.constantInstructions 9 5 0 "kind" ++ lookupBody ++
        DomainGuard.instructions 17 3 15 "domain" ++ Phase.instructions 2) yielded).isNone = true :=
  by decide +kernel

theorem wrong_state :
    (BaseEntry.recognize 9 state body [0, 1, 2, 3, 4, 5, 18, 2]).isNone = true := by decide +kernel

#print axioms actual
#print axioms in_range
#print axioms out_of_range
#print axioms oversized_rows
#print axioms wrong_position
#print axioms wrong_state
end Tests.QueryControllerEnter
