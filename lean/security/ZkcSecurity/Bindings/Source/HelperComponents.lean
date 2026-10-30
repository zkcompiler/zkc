module

public import Zkc.Source.Structured.DomainLinking

@[expose] public section

/-! Install optional helper laws at their actual captured declaration prefix.
The law must hold for arbitrary paired tables; no assumed source equation or
name-only helper identity can replace complete membership and body evidence. -/
set_option autoImplicit false
namespace ZkcSecurity.Source.HelperComponents
open Zkc.Source Zkc.Source.Structured
variable (model : DomainModel) {I : PIR.Signature}

private theorem invoke_fold_other (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (definitions : List CheckedDefinition) (helper : Helper)
    (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) tables).components helper =
      invoke tables.components helper := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact invoke_cons_other _ _ helper (different _ List.mem_cons_self)

theorem invoke (definitions : List CheckedDefinition) (linked : DeclarationsLinked [] definitions)
    (helper : Helper) (body : Region dialect helper.inputs helper.outputs)
    (associated : BodyIn definitions helper body)
    (arguments : Values (Component model.Value) helper.inputs)
    (result : PIR.Process I (Values (Component model.Value) helper.outputs))
    (law : ∀ tables : Evaluation.ComponentTablesOn model.toCarriers I,
      body.component (Evaluation.meaningOn model (.silent I) tables.closed)
        (Evaluation.componentOperationOn model (.silent I) tables) arguments.get = result) :
    Structured.invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩).components
      helper arguments = result := by
  obtain ⟨definition, member, signature, raw⟩ := associated
  subst helper
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [split] at linked ⊢
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have fresh : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other present
    exact tail.2.2.fresh List.mem_cons_self present
  simp only [List.foldl_append, List.foldl_cons]
  rw [invoke_fold_other model _ after definition.helper fresh]
  simp only [Evaluation.ComponentTablesOn.extend]
  rw [invoke_cons_same]
  rw [definition.body_eq_of_raw body raw]
  exact law _

end ZkcSecurity.Source.HelperComponents
