module

public import Zkc.Source.Structured.Linking
public import Zkc.Source.Structured.DomainFrame

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

/-- Adding a declaration with a different name leaves an existing lookup intact. -/
theorem invoke_extend_otherOn (observations : SiteObservations interface) (table : HelperTable model.Value interface) (definition : CheckedDefinition)
    (helper : Helper) (different : definition.name ≠ helper.name) :
    invoke (extendMeaningsOn model observations table definition) helper = invoke table helper := by
  simp [invoke, extendMeaningsOn, CheckedDefinition.helper, different]

theorem invoke_foldl_otherOn (observations : SiteObservations interface) (table : HelperTable model.Value interface) (definitions : List CheckedDefinition)
    (helper : Helper) (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl (extendMeaningsOn model observations) table) helper = invoke table helper := by
  induction definitions generalizing table with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact invoke_extend_otherOn model observations table definition helper (different _ List.mem_cons_self)

/-- A linked definition list supplies the body equation under any site observation.
The stored closure uses its own prefix; linking preserves all referenced helpers. -/
theorem definitions_invoke_bodyOn (observations : SiteObservations interface) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (definition : CheckedDefinition)
    (member : definition ∈ definitions)
    (arguments : Values model.Value definition.inputs) :
    invoke (definitions.foldl (extendMeaningsOn model observations) []) definition.helper arguments =
      definition.body.denote
        (meaningOn model observations (definitions.foldl (extendMeaningsOn model observations) [])) arguments.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have linking := linked
  rw [split] at linking
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linking |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other present
    exact tail.2.2.fresh List.mem_cons_self present
  have stored : invoke (definitions.foldl (extendMeaningsOn model observations) []) definition.helper arguments =
      definition.body.denote (meaningOn model observations
        (before.foldl (extendMeaningsOn model observations) [])) arguments.get := by
    simp only [split, List.foldl_append, List.foldl_cons]
    rw [invoke_foldl_otherOn model observations _ after definition.helper different]
    simp [extendMeaningsOn, invoke]
    rfl
  rw [stored]
  refine congrFun (region_denoteOn_table_congr model observations
    (before.foldl (extendMeaningsOn model observations) [])
    (definitions.foldl (extendMeaningsOn model observations) []) definition.body ?_) arguments.get
  intro helper used
  have present : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] :=
    tail.2.1 helper (by simpa only [definition.helpers_eq_body] using used)
  have fresh : ∀ other ∈ definition :: after, other.name ≠ helper.name := by
    intro other member
    exact tail.fresh present member
  simp only [split, List.foldl_append]
  exact (invoke_foldl_otherOn model observations _ (definition :: after) helper fresh).symm

/-- Membership, the full signature and the entire raw tree identify a body view.
No closed entry or equality with another client's table is required. -/
theorem definitions_invoke_body_view_asOn (observations : SiteObservations interface) (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (definition : CheckedDefinition)
    (member : definition ∈ definitions) (helper : Helper)
    (signature : definition.helper = helper)
    (body : Region dialect helper.inputs helper.outputs)
    (exactRaw : definition.raw = body.erase)
    (arguments : Values model.Value helper.inputs) :
    invoke (definitions.foldl (extendMeaningsOn model observations) []) helper arguments =
      body.denote (meaningOn model observations
        (definitions.foldl (extendMeaningsOn model observations) [])) arguments.get := by
  subst helper
  rw [definitions_invoke_bodyOn model observations definitions linked definition member arguments,
    definition.body_eq_of_raw body exactRaw]
  rfl

end Zkc.Source.Structured.Evaluation
