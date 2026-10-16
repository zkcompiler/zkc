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

namespace Evaluation

variable {F G : Type} {interface : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
variable (observations : SiteObservations interface)

theorem componentOperation_table_congr (left right : ComponentTables F G interface) (op : Op)
    (closedAgree : ∀ helper ∈ op.helpers, invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ op.helpers,
      invoke left.components helper = invoke right.components helper) :
    componentOperation observations left op = componentOperation observations right op := by
  have closedOperation := operation_table_congr observations left.closed right.closed op closedAgree
  have strictSame : strictComponent (meaning observations left.closed) op =
      strictComponent (meaning observations right.closed) op := by
    funext args bodies
    cases present : RoleFamily.sequence args with
    | none => simp only [strictComponent, present]
    | some values =>
      simp only [strictComponent, present]
      exact congrArg (fun process => process.bind (fun results => .done results.present))
        (congrFun (congrFun closedOperation values) bodies)
  cases op <;> try exact strictSame
  case exec primitive =>
    funext args bodies
    cases bodies
    simp only [componentOperation]
    split <;> rfl
  case map spec =>
    funext args bodies
    cases bodies
    simp only [componentOperation]
    split
    · rfl
    · exact congrArg (fun process => process.bind (fun results => .done results.present))
        (denoteMap_table_congr left.closed right.closed spec
          (closedAgree spec.helper (by simp [Op.helpers])) _)
  case invoke helper =>
    funext args bodies
    cases bodies
    cases helper with
    | mk name kind inputs outputs =>
      cases kind with
      | math => exact congrFun (componentAgree _ (by simp [Op.helpers])) args
      | «local» => exact congrFun (congrFun strictSame args) .nil

theorem region_component_table_congr (left right : ComponentTables F G interface) {Γ out}
    (region : Region dialect Γ out)
    (closedAgree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left.components helper = invoke right.components helper) :
    region.component (meaning observations left.closed) (componentOperation observations left) =
      region.component (meaning observations right.closed) (componentOperation observations right) := by
  apply Region.component_congr
  · intro op member
    apply operation_table_congr observations
    intro helper used
    exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro op member
    apply componentOperation_table_congr observations
    · intro helper used
      exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
    · intro helper used
      exact componentAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

theorem component_invoke_extended (tables : ComponentTables F G interface) (definition : CheckedDefinition)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (tables.extend observations definition).components definition.helper args =
      definition.body.component (meaning observations tables.closed) (componentOperation observations tables) args.get := by
  simp [ComponentTables.extend, invoke]
  rfl

theorem component_invoke_extend_other (tables : ComponentTables F G interface)
    (definition : CheckedDefinition) (helper : Helper)
    (different : definition.name ≠ helper.name) :
    invoke (tables.extend observations definition).components helper = invoke tables.components helper := by
  simp [ComponentTables.extend, invoke, CheckedDefinition.helper, different]

theorem component_invoke_foldl_other (tables : ComponentTables F G interface)
    (definitions : List CheckedDefinition) (helper : Helper)
    (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl (ComponentTables.extend observations) tables).components helper =
      invoke tables.components helper := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact component_invoke_extend_other observations tables definition helper (different _ List.mem_cons_self)

private theorem component_find_foldl_other (tables : ComponentTables F G interface)
    (definitions : List CheckedDefinition) (name : String)
    (different : ∀ definition ∈ definitions, definition.name ≠ name) :
    (definitions.foldl (ComponentTables.extend observations) tables).components.find?
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
    ∃ entry : HelperDefinition (Component (assignment F G)) interface,
      (definitions.foldl (ComponentTables.extend observations) (⟨[], []⟩ : ComponentTables F G interface)).components.find?
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
  rw [component_find_foldl_other observations _ after definition.helper.name different]
  exact ⟨⟨definition.helper, fun args => definition.body.component
    (meaning observations (before.foldl (ComponentTables.extend observations) ⟨[], []⟩).closed)
    (componentOperation observations (before.foldl (ComponentTables.extend observations) ⟨[], []⟩)) args.get⟩,
    by simp [ComponentTables.extend], rfl⟩

/-- Exact resolution includes references inside dormant nonoptional callbacks. -/
theorem payload_component_reference_resolves (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (helper : Helper) (used : helper ∈ definition.helpers) :
    ∃ entry : HelperDefinition (Component (assignment F G)) interface,
      (before.foldl (ComponentTables.extend observations) (⟨[], []⟩ : ComponentTables F G interface)).components.find?
        (fun entry => entry.helper.name == helper.name) = some entry ∧ entry.helper = helper := by
  have linked := payload.linked
  rw [split] at linked
  exact component_linked_lookup observations ((DeclarationsLinked.append [] before (definition :: after)).mp linked).1
    helper (payload.declaration_helpers before definition after split helper used)

theorem payload_component_invoke_declaration (payload : Payload)
    (before : List CheckedDefinition) (definition : CheckedDefinition)
    (after : List CheckedDefinition) (split : payload.definitions = before ++ definition :: after)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (payloadComponentTables observations payload).components definition.helper args =
      let captured := before.foldl (ComponentTables.extend observations) (⟨[], []⟩ : ComponentTables F G interface)
      definition.body.component (meaning observations captured.closed) (componentOperation observations captured) args.get := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linked |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other member
    exact tail.2.2.fresh List.mem_cons_self member
  simp only [payloadComponentTables, split, List.foldl_append, List.foldl_cons]
  rw [component_invoke_foldl_other observations _ after definition.helper different]
  exact component_invoke_extended observations _ definition args

theorem payload_component_prefix_agrees (payload : Payload)
    (before after : List CheckedDefinition) (split : payload.definitions = before ++ after)
    (helper : Helper) (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl (ComponentTables.extend observations) (⟨[], []⟩ : ComponentTables F G interface)).components helper =
      invoke (payloadComponentTables observations payload).components helper := by
  have linked := payload.linked
  rw [split] at linked
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  have different : ∀ definition ∈ after, definition.name ≠ helper.name := by
    intro definition member
    exact tail.fresh available member
  simp only [payloadComponentTables, split, List.foldl_append]
  exact (component_invoke_foldl_other observations _ after helper different).symm

/-- A full-table helper equation, preserving the original captured prefix through
both closed and optional framing. No body is expanded at a call site. -/
theorem payload_component_invoke_body (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (payloadComponentTables observations payload).components definition.helper args =
      definition.body.component (meaning observations (payloadComponentTables observations payload).closed)
        (componentOperation observations (payloadComponentTables observations payload)) args.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  rw [payload_component_invoke_declaration observations payload before definition after split]
  refine congrFun (region_component_table_congr observations
    (before.foldl (ComponentTables.extend observations) ⟨[], []⟩) (payloadComponentTables observations payload) definition.body ?_ ?_) args.get
  · intro helper used
    have present := payload.declaration_helpers before definition after split helper
      (by simpa only [definition.helpers_eq_body] using used)
    simp only [ComponentTables.closed_fold observations, payload_componentTables_closed observations payload]
    exact payload_prefix_agrees observations payload before (definition :: after) split helper present
  · intro helper used
    have present := payload.declaration_helpers before definition after split helper
      (by simpa only [definition.helpers_eq_body] using used)
    exact payload_component_prefix_agrees observations payload before (definition :: after) split helper present

theorem payload_component_body_view (payload : Payload) (definition : CheckedDefinition)
    (member : definition ∈ payload.definitions) (body : Region dialect definition.inputs definition.outputs)
    (exactRaw : definition.raw = body.erase)
    (args : Values (Component (assignment F G)) definition.inputs) :
    invoke (payloadComponentTables observations payload).components definition.helper args =
      body.component (meaning observations (payloadComponentTables observations payload).closed)
        (componentOperation observations (payloadComponentTables observations payload)) args.get := by
  rw [payload_component_invoke_body observations payload definition member args, definition.body_eq_of_raw body exactRaw]

theorem payload_component_entry (payload : Payload)
    (args : Values (Component (assignment F G)) payload.entry.inputs) :
    payloadComponent observations payload args =
      payload.entry.body.component (meaning observations (payloadComponentTables observations payload).closed)
        (componentOperation observations (payloadComponentTables observations payload)) args.get :=
  rfl

end Evaluation

end Zkc.Source.Structured
