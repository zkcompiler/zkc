module

public import Zkc.Source.Structured.Component
public import Zkc.Source.Structured.Linking
public import Zkc.Source.ComponentCongruence

@[expose] public section

/-! Component invocation resolves the same exact checked helper inventory.
Framing requires both tables: named calls use optional closures, while strict
operations and nested callbacks use the closed table. No formation or totality
assumption is hidden in these process equalities.
-/
set_option autoImplicit false
namespace Zkc.Source.Structured

variable {F : Type} [CommRing F] [DecidableEq F]

theorem componentOperation_table_congr (left right : ComponentTables F) (op : Op)
    (closedAgree : ∀ helper ∈ op.helpers, invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ op.helpers,
      invoke left.components helper = invoke right.components helper) :
    componentOperation left op = componentOperation right op := by
  have closedOperation := operation_table_congr left.closed right.closed op closedAgree
  have strictSame : strictComponent (meaning F left.closed) op =
      strictComponent (meaning F right.closed) op := by
    funext args bodies
    cases present : RoleFamily.sequence args with
    | none => simp only [strictComponent, present]
    | some values =>
      simp only [strictComponent, present]
      exact congrArg (fun process => process.bind (fun results => .done results.present))
        (congrFun (congrFun closedOperation values) bodies)
  cases op <;> try exact strictSame
  case invoke helper =>
    funext args bodies
    cases bodies
    exact congrFun (componentAgree helper (by simp [Op.helpers])) args

theorem region_component_table_congr (left right : ComponentTables F) {Γ out}
    (region : Region dialect Γ out)
    (closedAgree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left.components helper = invoke right.components helper) :
    region.component (meaning F left.closed) (componentOperation left) =
      region.component (meaning F right.closed) (componentOperation right) := by
  apply Region.component_congr
  · intro op member
    apply operation_table_congr
    intro helper used
    exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro op member
    apply componentOperation_table_congr
    · intro helper used
      exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
    · intro helper used
      exact componentAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

theorem component_invoke_extended (tables : ComponentTables F) (definition : CheckedDefinition)
    (args : Values (Component (scalarAssignment F)) definition.inputs) :
    invoke (tables.extend definition).components definition.helper args =
      definition.body.component (meaning F tables.closed) (componentOperation tables) args.get := by
  simp [ComponentTables.extend, invoke]
  rfl

theorem component_invoke_extend_other (tables : ComponentTables F)
    (definition : CheckedDefinition) (helper : Helper)
    (different : definition.name ≠ helper.name) :
    invoke (tables.extend definition).components helper = invoke tables.components helper := by
  simp [ComponentTables.extend, invoke, CheckedDefinition.helper, different]

theorem component_invoke_foldl_other (tables : ComponentTables F)
    (definitions : List CheckedDefinition) (helper : Helper)
    (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl ComponentTables.extend tables).components helper =
      invoke tables.components helper := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact component_invoke_extend_other tables definition helper (different _ List.mem_cons_self)

private theorem component_find_foldl_other (tables : ComponentTables F)
    (definitions : List CheckedDefinition) (name : String)
    (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl ComponentTables.extend tables).components.find?
        (fun entry => entry.helper.name == name) =
      tables.components.find? (fun entry => entry.helper.name == name) := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    simp [ComponentTables.extend, CheckedDefinition.helper, different _ List.mem_cons_self]

theorem component_linked_lookup {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (helper : Helper)
    (present : helper ∈ definitions.map CheckedDefinition.helper) :
    ∃ entry : HelperDefinition (Component (scalarAssignment F)) closedInterface,
      (definitions.foldl ComponentTables.extend (⟨[], []⟩ : ComponentTables F)).components.find?
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
  rw [component_find_foldl_other _ after definition.helper.name different]
  exact ⟨⟨definition.helper, fun args => definition.body.component
    (meaning F (before.foldl ComponentTables.extend ⟨[], []⟩).closed)
    (componentOperation (before.foldl ComponentTables.extend ⟨[], []⟩)) args.get⟩,
    by simp [ComponentTables.extend], rfl⟩

/-- Exact resolution includes references inside dormant nonoptional callbacks. -/
theorem Payload.component_reference_resolves (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (helper : Helper) (used : helper ∈ definition.helpers) :
    ∃ entry : HelperDefinition (Component (scalarAssignment F)) closedInterface,
      (before.foldl ComponentTables.extend (⟨[], []⟩ : ComponentTables F)).components.find?
        (fun entry => entry.helper.name == helper.name) = some entry ∧ entry.helper = helper := by
  have linked := payload.linked
  rw [split] at linked
  exact component_linked_lookup ((DeclarationsLinked.append [] before (definition :: after)).mp linked).1
    helper (payload.declaration_helpers before definition after split helper used)

theorem Payload.component_invoke_declaration (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (args : Values (Component (scalarAssignment F)) definition.inputs) :
    invoke (payload.componentTables F).components definition.helper args =
      let captured := before.foldl ComponentTables.extend (⟨[], []⟩ : ComponentTables F)
      definition.body.component (meaning F captured.closed) (componentOperation captured) args.get := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  simp only [Payload.componentTables, split, List.foldl_append, List.foldl_cons]
  rw [component_invoke_foldl_other _ after definition.helper different]
  exact component_invoke_extended _ definition args

theorem Payload.component_prefix_agrees (payload : Payload)
    (before after : List CheckedDefinition) (split : payload.definitions = before ++ after)
    (helper : Helper) (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl ComponentTables.extend (⟨[], []⟩ : ComponentTables F)).components helper =
      invoke (payload.componentTables F).components helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ helper.name := by
    intro definition member
    exact tail.fresh available member
  simp only [Payload.componentTables, split, List.foldl_append]
  exact (component_invoke_foldl_other _ after helper different).symm

/-- A full-table helper equation, preserving the original captured prefix through
both closed and optional framing. No body is expanded at a call site. -/
theorem Payload.component_invoke_body (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (args : Values (Component (scalarAssignment F)) definition.inputs) :
    invoke (payload.componentTables F).components definition.helper args =
      definition.body.component (meaning F (payload.componentTables F).closed)
        (componentOperation (payload.componentTables F)) args.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [payload.component_invoke_declaration before definition after split]
  refine congrFun (region_component_table_congr
    (before.foldl ComponentTables.extend ⟨[], []⟩) (payload.componentTables F) definition.body ?_ ?_) args.get
  · intro helper used
    have present := payload.declaration_helpers before definition after split helper
      (by simpa only [definition.helpers_eq_body] using used)
    simp only [ComponentTables.closed_fold, payload.componentTables_closed]
    exact payload.prefix_agrees before (definition :: after) split helper present
  · intro helper used
    have present := payload.declaration_helpers before definition after split helper
      (by simpa only [definition.helpers_eq_body] using used)
    exact payload.component_prefix_agrees before (definition :: after) split helper present

theorem Payload.component_body_view (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase)
    (args : Values (Component (scalarAssignment F)) definition.inputs) :
    invoke (payload.componentTables F).components definition.helper args =
      body.component (meaning F (payload.componentTables F).closed)
        (componentOperation (payload.componentTables F)) args.get := by
  rw [payload.component_invoke_body definition member args, definition.body_eq_of_raw body exactRaw]

theorem Payload.component_entry (payload : Payload)
    (args : Values (Component (scalarAssignment F)) payload.entry.inputs) :
    payload.component F args =
      payload.entry.body.component (meaning F (payload.componentTables F).closed)
        (componentOperation (payload.componentTables F)) args.get :=
  payload.component_invoke_body payload.entry (List.get_mem _ _) args

end Zkc.Source.Structured
