module

public import Zkc.Source.Structured.ReferenceLibrary

@[expose] public section

/-! Nominal optional-component projection laws. Exact body association checks
all output positions. Absent operands remain absent; no strict sequencing or
unproved whole-table equation replaces this component interpretation. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.ReferenceLibrary
open Zkc.Source

variable (model : DomainModel) {I : PIR.Signature}

private theorem components_suffix (observations : SiteObservations I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) (definitions : List CheckedDefinition)
    (helper : Helper) (fresh : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model observations) tables).components helper =
      invoke tables.components helper := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => fresh d (List.mem_cons_of_mem _ member))]
    simp [invoke, Evaluation.ComponentTablesOn.extend, CheckedDefinition.helper,
      fresh _ List.mem_cons_self]

/-- A projection uses no helper table, so its captured prefix may be arbitrary.
Linking is used only to prove that subsequent declarations cannot shadow it. -/
theorem projection_components (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (helper : Helper)
    (selected : Operands helper.inputs helper.outputs)
    (associated : BodyIn definitions helper (.ret selected))
    (arguments : Values (Component model.Value) helper.inputs) :
    invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩).components
      helper arguments = .done (Operands.eval arguments.get selected) := by
  obtain ⟨definition, member, signature, raw⟩ := associated
  subst helper
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have linking := linked
  rw [split] at linking
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linking |>.2
  have fresh : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other present
    exact tail.2.2.fresh List.mem_cons_self present
  rw [split, List.foldl_append, List.foldl_cons,
    components_suffix model (.silent I) _ after definition.helper fresh]
  have body := definition.body_eq_of_raw (.ret selected) raw
  simp [Evaluation.ComponentTablesOn.extend, invoke, body]
  rfl

end Zkc.Source.Structured.ReferenceLibrary
