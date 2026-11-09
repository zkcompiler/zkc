module

public import Zkc.IR.Source.Structured.ReferenceLaws

@[expose] public section

/-! Install a mathematical law for an optional helper at its actual lexical
prefix. Missing operands need not make the entire helper absent. -/
set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation
variable (model : DomainModel) {I : PIR.Signature} (observations : SiteObservations I)

private theorem component_suffix (tables : ComponentTablesOn model.toCarriers I)
    (suffix : List CheckedDefinition) (helper : Helper)
    (fresh : ∀ definition ∈ suffix, definition.name ≠ helper.name) :
    invoke (suffix.foldl (ComponentTablesOn.extend model observations) tables).components helper =
      invoke tables.components helper := by
  induction suffix generalizing tables with
  | nil => rfl
  | cons head tail ih =>
    rw [List.foldl_cons, ih _ (fun d member => fresh d (List.mem_cons_of_mem _ member))]
    apply invoke_cons_other
    exact fresh head List.mem_cons_self

/-- Exact signature and body membership select the stored implementation.
The reference must hold on every captured prefix and every optional input. -/
theorem component_invoke_associated {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) {helper : Helper}
    {body : Region dialect helper.inputs helper.outputs}
    (associated : BodyIn definitions helper body)
    (reference : HelperFunction (Component model.Value) I helper)
    (law : ∀ (tables : ComponentTablesOn model.toCarriers I) args,
      body.component (meaningOn model observations tables.closed)
        (componentOperationOn model observations tables) args.get = reference args)
    (args : Values (Component model.Value) helper.inputs) :
    invoke (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).components
      helper args = reference args := by
  obtain ⟨definition, member, signature, tree⟩ := associated
  subst helper
  have bodyExact := definition.body_eq_of_raw body tree
  obtain ⟨before, suffix, split⟩ := List.mem_iff_append.mp member
  rw [split] at linked ⊢
  have tail := (DeclarationsLinked.append [] before (definition :: suffix)).mp linked |>.2
  simp only [List.foldl_append, List.foldl_cons]
  rw [component_suffix model observations _ suffix definition.helper
    (fun d member => tail.2.2.fresh List.mem_cons_self member)]
  change invoke (_ :: _) definition.helper args = _
  rw [invoke_cons_same]
  change definition.body.component _ _ _ = _
  rw [bodyExact]
  exact law _ args

end Zkc.Source.Structured.Evaluation
