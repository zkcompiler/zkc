module

public import Zkc.Realization.RecordProjection

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Tests.RecordProjection
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Realization.RecordProjection

def layout : Layout := ⟨"Example.Record", "Record", .cons .index (.cons .index .nil)⟩
def ordered : List (Selection layout.fields) := [⟨.index, .here⟩, ⟨.index, .there .here⟩]
def swapped : List (Selection layout.fields) := [⟨.index, .there .here⟩, ⟨.index, .here⟩]
def repeated : List (Selection layout.fields) := [⟨.index, .here⟩, ⟨.index, .here⟩]

/-- One proof connects a new nominal record at every caller placement. -/
theorem actual (model : DomainModel) (program : Program) (context : Context)
    (a b : Nat) (before after : Domain.Environment model.toCarriers) :
    let frame := before ++ [.data ⟨layout.type, rfl, (a, b, ())⟩] ++ after
    Nonempty (Original.Simulation Eq (fun _ live ↦ frame <+: live)
      (.done (frame ++ [.data (.index a), .data (.index b)]))
      (Domain.evaluate model program context
        (instructions layout before.length ordered) frame)) := by
  dsimp only
  rw [correspondence]
  have derived :=
    simulation model layout rfl ordered
      (by intro selected present; simp only [ordered, List.mem_cons, List.not_mem_nil,
            or_false] at present; rcases present with rfl | rfl <;> rfl)
      (before ++ [.data ⟨layout.type, rfl, (a, b, ())⟩] ++ after)
      (before ++ [.data ⟨layout.type, rfl, (a, b, ())⟩] ++ after)
      (List.prefix_refl _) before.length (a, b, ()) (by simp)
  have valuesEq : results model layout (a, b, ()) ordered =
      [.data (.index a), .data (.index b)] := by rfl
  rw [valuesEq] at derived
  exact derived


theorem recognizes_repeated_fields :
    (recognize (instructions layout 7 repeated)).isSome = true := by decide +kernel

/-- Swapping two same-typed fields is represented faithfully, not identified
with the original layout merely because the output types agree. -/
theorem swap_changes_output (model : DomainModel) :
    results model layout (3, 5, ()) ordered ≠ results model layout (3, 5, ()) swapped := by
  intro equal
  have impossible : (3 : Nat) = 5 := by
    simpa [results, ordered, swapped, layout, Layout.type, Original.encodeHelperResult,
      Domain.encodeValues_cons, Domain.encodeValues_nil, Domain.Value.encode,
      Domain.Payload.ofValue, Domain.Value.decode, Domain.Payload.value, Ty.isHandle,
      ProductFields.unpack, Values.get] using
      congrArg (fun values ↦ values.head?.bind (Domain.Value.decode .index)) equal
  contradiction

theorem mixed_records_refused :
    (recognize ((instructions layout 7 ordered).set 1
      ⟨.calculate (.getProduct layout.identity layout.constructor layout.fields
        .index (.there .here)), [8], [.data .index], []⟩)).isNone = true := by decide +kernel

#print axioms actual
#print axioms swap_changes_output
end Tests.RecordProjection
