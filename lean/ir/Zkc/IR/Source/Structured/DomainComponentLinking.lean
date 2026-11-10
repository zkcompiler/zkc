module

public import Zkc.IR.Source.Structured.DomainLinking
public import Zkc.Program.Source.ComponentCongruence

/-! Dependency framing for the same helper closure under nominal domain models.
Both optional and closed dependency meanings are preserved, including dormant callbacks.
Callers need only exact source membership; prefix selection and framing are shared laws. -/

@[expose] public section
namespace Zkc.Source.Structured.Evaluation
variable (model : DomainModel) {interface : PIR.Signature}
  (observations : SiteObservations interface)

theorem componentOperationOn_table_congr
    (left right : ComponentTablesOn model.toCarriers interface) (op : Op)
    (closedAgree : ∀ helper ∈ op.helpers, invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ op.helpers,
      invoke left.components helper = invoke right.components helper) :
    componentOperationOn model observations left op =
      componentOperationOn model observations right op := by
  have closedOperation :=
    operationOn_table_congr model observations left.closed right.closed op closedAgree
  have strictSame : strictComponent (meaningOn model observations left.closed) op =
      strictComponent (meaningOn model observations right.closed) op := by
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
    simp only [componentOperationOn]
    split <;> rfl
  case map spec =>
    funext args bodies
    cases bodies
    simp only [componentOperationOn]
    split
    · rfl
    · rename_i values present
      exact congrArg (fun process => process.bind (fun results => .done results.present))
        (congrFun (congrFun closedOperation values) .nil)
  case invoke helper =>
    funext args bodies
    cases bodies
    cases helper with
    | mk name kind inputs outputs =>
      cases kind with
      | math => exact congrFun (componentAgree _ (by simp [Op.helpers])) args
      | «local» => exact congrFun (congrFun strictSame args) .nil

theorem region_componentOn_table_congr
    (left right : ComponentTablesOn model.toCarriers interface) {Γ out}
    (region : Region dialect Γ out)
    (closedAgree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left.closed helper = invoke right.closed helper)
    (componentAgree : ∀ helper ∈ region.erase.operations.flatMap Op.helpers,
      invoke left.components helper = invoke right.components helper) :
    region.component (meaningOn model observations left.closed)
        (componentOperationOn model observations left) =
      region.component (meaningOn model observations right.closed)
        (componentOperationOn model observations right) := by
  apply Region.component_congr
  · intro op member
    apply operationOn_table_congr model observations
    intro helper used
    exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
  · intro op member
    apply componentOperationOn_table_congr model observations
    · intro helper used
      exact closedAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)
    · intro helper used
      exact componentAgree helper (List.mem_flatMap.mpr ⟨op, member, used⟩)

theorem component_invoke_extendedOn (tables : ComponentTablesOn model.toCarriers interface)
    (definition : CheckedDefinition)
    (args : Values (Component model.Value) definition.inputs) :
    invoke (tables.extend model observations definition).components definition.helper args =
      definition.body.component (meaningOn model observations tables.closed)
        (componentOperationOn model observations tables) args.get := by
  simp [ComponentTablesOn.extend, invoke]
  rfl

theorem component_invoke_extend_otherOn (tables : ComponentTablesOn model.toCarriers interface)
    (definition : CheckedDefinition) (helper : Helper)
    (different : definition.name ≠ helper.name) :
    invoke (tables.extend model observations definition).components helper =
      invoke tables.components helper := by
  simp [ComponentTablesOn.extend, invoke, CheckedDefinition.helper, different]

theorem component_invoke_foldl_otherOn (tables : ComponentTablesOn model.toCarriers interface)
    (definitions : List CheckedDefinition) (helper : Helper)
    (different : ∀ definition ∈ definitions, definition.name ≠ helper.name) :
    invoke (definitions.foldl (ComponentTablesOn.extend model observations) tables).components helper =
      invoke tables.components helper := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    rw [List.foldl_cons, ih _ (fun d member => different d (List.mem_cons_of_mem _ member))]
    exact component_invoke_extend_otherOn model observations tables definition helper
      (different _ List.mem_cons_self)

theorem component_prefix_agreesOn {definitions : List CheckedDefinition}
    (linked : DeclarationsLinked [] definitions) (before after : List CheckedDefinition)
    (split : definitions = before ++ after) (helper : Helper)
    (present : helper ∈ before.map CheckedDefinition.helper) :
    invoke (before.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).components helper =
      invoke (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).components
        helper := by
  rw [split] at linked ⊢
  have tail := (DeclarationsLinked.append [] before after).mp linked |>.2
  have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
    simpa using present
  rw [List.foldl_append]
  exact (component_invoke_foldl_otherOn model observations _ after helper
    (fun _ member => tail.fresh available member)).symm

/-- A body law can use the complete actual table; declaration order never becomes
an author-supplied frame. Captured prefixes are preserved by exact linking. -/
theorem component_invoke_bodyOn (definitions : List CheckedDefinition)
    (linked : DeclarationsLinked [] definitions) (definition : CheckedDefinition)
    (member : definition ∈ definitions)
    (args : Values (Component model.Value) definition.inputs) :
    invoke (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).components
        definition.helper args =
      definition.body.component
        (meaningOn model observations
          (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).closed)
        (componentOperationOn model observations
          (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩)) args.get := by
  obtain ⟨before, after, split⟩ := List.mem_iff_append.mp member
  have linkedSplit := linked
  rw [split] at linkedSplit
  have tail := (DeclarationsLinked.append [] before (definition :: after)).mp linkedSplit |>.2
  have different : ∀ other ∈ after, other.name ≠ definition.helper.name := by
    intro other present
    exact tail.2.2.fresh List.mem_cons_self present
  have captured : invoke
      (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).components
      definition.helper args = definition.body.component
        (meaningOn model observations
          (before.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩).closed)
        (componentOperationOn model observations
          (before.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩)) args.get := by
    rw [split, List.foldl_append, List.foldl_cons,
      component_invoke_foldl_otherOn model observations _ after definition.helper different]
    exact component_invoke_extendedOn model observations _ definition args
  rw [captured]
  refine congrFun (region_componentOn_table_congr model observations
    (before.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩)
    (definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩) definition.body ?_ ?_) args.get
  · intro helper used
    have present : helper ∈ before.map CheckedDefinition.helper := by
      simpa using tail.2.1 helper (by simpa only [definition.helpers_eq_body] using used)
    rw [ComponentTablesOn.closed_fold, ComponentTablesOn.closed_fold]
    have available : helper ∈ before.reverse.map CheckedDefinition.helper ++ [] := by
      simpa using present
    rw [split, List.foldl_append]
    exact (invoke_foldl_otherOn model observations _ (definition :: after) helper
      (fun _ member => tail.fresh available member)).symm
  · intro helper used
    have present : helper ∈ before.map CheckedDefinition.helper := by
      simpa using tail.2.1 helper (by simpa only [definition.helpers_eq_body] using used)
    exact component_prefix_agreesOn model observations linked before (definition :: after)
      split helper present

end Zkc.Source.Structured.Evaluation
