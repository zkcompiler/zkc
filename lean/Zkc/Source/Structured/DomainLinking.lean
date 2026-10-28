module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.DomainInterpretation

@[expose] public section

/-! Exact helper lookup and closed interpretation over nominal domain models.
These laws preserve each declaration's captured prefix and every stopped
outcome. Structural connection builders need no per-helper mathematical law.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured.Evaluation
variable (model : DomainModel) {interface : PIR.Signature}

private theorem find_foldl_otherOn (observations : SiteObservations interface)
    (table : MeaningsOn model.toCarriers interface) (definitions : List CheckedDefinition)
    (name : String) (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl (extendMeaningsOn model observations) table).find?
        (fun entry => entry.helper.name == name) =
      table.find? (fun entry => entry.helper.name == name) := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    simp [extendMeaningsOn, CheckedDefinition.helper, different _ List.mem_cons_self]

/-- Admission's declaration linking selects the full helper signature and
implementation, even if its body rejects, refuses or exhausts a domain. -/
theorem linked_lookupOn (observations : SiteObservations interface)
    {definitions : List CheckedDefinition} (linked : DeclarationsLinked [] definitions)
    (helper : Helper) (present : helper ∈ definitions.map CheckedDefinition.helper) :
    ∃ entry : HelperDefinition model.Value interface,
      (definitions.foldl (extendMeaningsOn model observations) []).find?
        (fun entry => entry.helper.name == helper.name) = some entry ∧ entry.helper = helper := by
  obtain ⟨definition, member, same⟩ := List.mem_map.mp present
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [split] at linked ⊢
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  subst helper
  simp only [List.foldl_append, List.foldl_cons]
  rw [find_foldl_otherOn model observations _ after definition.helper.name different]
  exact ⟨⟨definition.helper, fun args => definition.body.denote
    (meaningOn model observations (before.foldl (extendMeaningsOn model observations) [])) args.get⟩,
    by simp [extendMeaningsOn], rfl⟩

/-- The component table's closed half is the same captured declaration fold,
not an independently supplied helper implementation. -/
theorem ComponentTablesOn.closed_fold (observations : SiteObservations interface)
    (definitions : List CheckedDefinition) (tables : ComponentTablesOn model.toCarriers interface) :
    (definitions.foldl (ComponentTablesOn.extend model observations) tables).closed =
      definitions.foldl (extendMeaningsOn model observations) tables.closed := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih => exact ih _

/-- A silent helper in an occurrence or other effect interface is precisely
its actual closed computation lifted into that interface. -/
theorem closed_invoke_componentTablesOn (definitions : List CheckedDefinition)
    (helper : Helper) (arguments : Values model.Value helper.inputs) :
    invoke (definitions.foldl
        (ComponentTablesOn.extend model (.silent interface)) ⟨[], []⟩).closed helper arguments =
      (invoke (definitions.foldl (extendMeaningsOn model SiteObservations.closed) [])
        helper arguments).interpret (closedLift (I := interface)) := by
  rw [ComponentTablesOn.closed_fold]
  exact (foldMeaningsOn_interpret (model := model) (closedLift (I := interface))
    (SiteObservations.silent_interpret _) (HelperTable.Interprets.empty _) definitions
    helper arguments).symm

end Zkc.Source.Structured.Evaluation
