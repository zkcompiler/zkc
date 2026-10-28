module

public import Zkc.Source.Structured.DomainLinking

@[expose] public section

/-! Present operands connect the two actual nominal helper tables.

Each declaration captures the same prefix on both sides. The proof uses the
existing region evaluator and preserves the entire process, including every
stop and every possible reply to an observation. No helper result law is used.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Source.Structured.Evaluation
variable (model : DomainModel) {interface : PIR.Signature}

theorem componentOperationOn_adequate (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) (adequate : tables.Adequate) :
    ComponentOperations.Adequate (meaningOn model observations tables.closed)
      (componentOperationOn model observations tables) := by
  intro op args bodies
  cases op <;> try exact strictComponent_adequate (meaningOn model observations tables.closed) _ args bodies
  case exec primitive =>
    cases bodies
    simp only [componentOperationOn, RoleFamily.sequence_present]
    rfl
  case map spec =>
    cases bodies
    simp only [componentOperationOn, RoleFamily.sequence_present]
    rfl
  case invoke helper =>
    cases bodies
    cases helper with
    | mk name kind inputs outputs =>
      cases kind with
      | math => exact adequate _ args
      | «local» => exact strictComponent_adequate (meaningOn model observations tables.closed) _ args .nil

theorem ComponentTablesOn.adequate_empty :
    (⟨[], []⟩ : ComponentTablesOn model.toCarriers interface).Adequate := by
  intro helper args
  rfl

theorem ComponentTablesOn.adequate_extend (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) (adequate : tables.Adequate)
    (definition : CheckedDefinition) : (tables.extend model observations definition).Adequate := by
  intro helper args
  by_cases name : definition.helper.name = helper.name
  · by_cases signature : definition.helper = helper
    · subst helper
      simp only [extend, extendMeaningsOn]
      simp [invoke]
      have presentEnv : @Eq (Environment (Component model.Value) definition.inputs)
          args.present.get (fun ref => some (args.get ref)) := by
        funext ty ref
        exact Values.get_present args ref
      rw [presentEnv]
      exact definition.body.component_present (meaningOn model observations tables.closed)
        (componentOperationOn model observations tables)
        (componentOperationOn_adequate model observations tables adequate) args.get
    · simp [extend, extendMeaningsOn, invoke, name, signature, PIR.Process.bind]
  · simp only [extend, extendMeaningsOn]
    simp only [invoke, List.find?_cons, show (definition.helper.name == helper.name) = false from
      beq_eq_false_iff_ne.mpr name]
    exact adequate helper args

theorem ComponentTablesOn.adequate_fold (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) (adequate : tables.Adequate)
    (definitions : List CheckedDefinition) :
    (definitions.foldl (ComponentTablesOn.extend model observations) tables).Adequate := by
  induction definitions generalizing tables with
  | nil => exact adequate
  | cons definition rest ih =>
    exact ih _ (tables.adequate_extend model observations adequate definition)

/-- Exact kept-helper semantics on present inputs, including Math helpers.
The original definitions supply both closures and their dependency prefixes.
Optional Math inputs and transformed/inlined helper bodies are not covered.
-/
theorem component_invoke_closed (definitions : List CheckedDefinition) (helper : Helper)
    (arguments : Values model.Value helper.inputs) :
    componentOperationOn model (.silent interface)
        (definitions.foldl (ComponentTablesOn.extend model (.silent interface)) ⟨[], []⟩)
        (.invoke helper) arguments.present .nil =
      ((invoke (definitions.foldl (extendMeaningsOn model SiteObservations.closed) [])
        helper arguments).interpret (closedLift (I := interface))).bind
          (fun results => .done results.present) := by
  refine (componentOperationOn_adequate model (.silent interface) _
    (ComponentTablesOn.adequate_fold model _ _ (ComponentTablesOn.adequate_empty model) definitions)
    (.invoke helper) arguments .nil).trans ?_
  change (invoke _ helper arguments).bind _ = _
  rw [closed_invoke_componentTablesOn]
  rfl

end Zkc.Source.Structured.Evaluation
