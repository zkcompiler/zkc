module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Structured.Component
public import Zkc.Source.Structured.ProtocolOperations

@[expose] public section

/-! Paired closed and component meanings over domain models.

These are the component tables and component operations of `Component` with
the uniform values replaced by a domain model's. The uniform definitions are
their instances at `ringModel F G`, by the equations at the end of this module;
`ComponentTables.toOn` reads a uniform table pair as one over the uniform
carriers. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace Evaluation

abbrev ComponentMeaningsOn (carriers : Carriers) (interface : PIR.Signature) :=
  HelperTable (Component carriers.Value) interface

/-- Two instances of one generic table, built from the same stored bodies. -/
structure ComponentTablesOn (carriers : Carriers) (interface : PIR.Signature) where
  closed : HelperTable carriers.Value interface
  components : ComponentMeaningsOn carriers interface

section Model
variable (model : DomainModel) {interface : PIR.Signature}

/-- Only Math calls bypass operand sequencing. Local calls and all other
operations reuse the shared strict evaluator, including effects and stops. -/
def componentOperationOn (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) :
    ComponentOperations (meaningOn model observations tables.closed)
  | .exec primitive, args, .nil =>
      match RoleFamily.sequence args with
      | none => .halt .incomplete
      | some values => (primitiveOutcome (primitive.evaluateOn model.toFieldModel values)).bind
          fun result => .done result.present
  | .map spec, args, .nil =>
      match RoleFamily.sequence (Value := model.Value) (types := spec.arguments) args with
      | none => .halt .incomplete
      | some values => (denoteMapOn tables.closed spec values).bind fun result =>
          .done result.present
  | .invoke helper, args, .nil =>
      if helper.kind = .math then invoke tables.components helper args
      else strictComponent (meaningOn model observations tables.closed) (.invoke helper) args .nil
  | op, args, bodies => strictComponent (meaningOn model observations tables.closed) op args bodies

-- Materialize generated equations in their defining module so all consumers
-- share the same stored declarations without exporting a global simp rule.
section
attribute [local simp] componentOperationOn
end

def ComponentTablesOn.extend (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) (definition : CheckedDefinition) :
    ComponentTablesOn model.toCarriers interface where
  closed := extendMeaningsOn model observations tables.closed definition
  components := ⟨definition.helper, fun args =>
    definition.body.component (meaningOn model observations tables.closed)
      (componentOperationOn model observations tables) args.get⟩ :: tables.components

def payloadComponentTablesOn (observations : SiteObservations interface) (payload : Payload) :
    ComponentTablesOn model.toCarriers interface :=
  payload.definitions.foldl (ComponentTablesOn.extend model observations) ⟨[], []⟩

def payloadComponentOn (observations : SiteObservations interface) (payload : Payload)
    (inputs : Values (Component model.Value) payload.entry.inputs) :
    PIR.Process interface (Values (Component model.Value) payload.entry.outputs) :=
  payload.entry.body.component
    (meaningOn model observations (payloadComponentTablesOn model observations payload).closed)
    (componentOperationOn model observations (payloadComponentTablesOn model observations payload))
    inputs.get

end Model

/-- Present component operands agree with the closed helper table. -/
def ComponentTablesOn.Adequate {carriers : Carriers} {interface : PIR.Signature}
    (tables : ComponentTablesOn carriers interface) : Prop :=
  ∀ helper args, invoke tables.components helper args.present =
    (invoke tables.closed helper args).bind fun results => .done results.present

/-- Every admitted non-call calculation uses the existing strict lifting. -/
theorem componentOperationOn_strict_calculation (model : DomainModel)
    {interface : PIR.Signature} (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) (op : Op)
    (allowed : op.isCalculation = true) (notCall : ∀ helper, op ≠ .invoke helper) :
    componentOperationOn model observations tables op =
      strictComponent (meaningOn model observations tables.closed) op := by
  cases op <;> first | rfl | simp_all [Op.isCalculation]

/-- Erasure needs admitted domain data and a returning transition on every reached
invariant-preserving state. Presence alone cannot supply either premise. -/
theorem component_fold_returns_on (model : DomainModel) {interface : PIR.Signature}
    (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface) (spec : FoldSpec)
    (arguments : Values model.Value spec.domain.inputs)
    (initial : Values model.Value spec.state) (captures : Values model.Value spec.captures)
    (items : List (Values model.Value spec.domain.items))
    (admitted : spec.domain.admit arguments = .returned items)
    (total : Values model.Value spec.state → Values model.Value spec.domain.items →
      Values model.Value spec.state)
    (valid : Values model.Value spec.state → Prop) (start : valid initial)
    (law : ∀ state item, item ∈ items → valid state →
      foldTransitionOn tables.closed spec arguments captures state item = .done (total state item) ∧
        valid (total state item)) :
    componentOperationOn model observations tables (.fold spec)
      (arguments.append (initial.append captures)).present .nil =
      .done (items.foldl total initial).present := by
  change strictComponent (meaningOn model observations tables.closed) (.fold spec) _ .nil = _
  refine (strictComponent_adequate (meaningOn model observations tables.closed) (.fold spec)
    (arguments.append (initial.append captures)) .nil).trans ?_
  change (denoteFoldOn tables.closed spec (arguments.append (initial.append captures))).bind _ = _
  simp only [denoteFoldOn, Values.split_append, admitted, Finite.admitThen]
  rw [Finite.fold_total_on _ total valid items initial start law]
  rfl

section Adequacy
variable {interface : PIR.Signature}

theorem componentOperationOn_adequate (model : DomainModel)
    (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface)
    (adequate : tables.Adequate) :
    ComponentOperations.Adequate (meaningOn model observations tables.closed)
      (componentOperationOn model observations tables) := by
  intro op args bodies
  cases op <;>
    try exact strictComponent_adequate (meaningOn model observations tables.closed) _ args bodies
  case exec primitive =>
    cases bodies
    simp only [componentOperationOn]
    rw [RoleFamily.sequence_present]
    rfl
  case map spec =>
    cases bodies
    simp only [componentOperationOn]
    erw [RoleFamily.sequence_present (Value := model.Value) args]
    rfl
  case invoke helper =>
    cases bodies
    cases helper with
    | mk name kind inputs outputs =>
      cases kind with
      | math => exact adequate _ args
      | «local» =>
        exact strictComponent_adequate (meaningOn model observations tables.closed) _ args .nil

theorem ComponentTablesOn.adequate_empty {model : DomainModel} {interface : PIR.Signature} :
    (⟨[], []⟩ : ComponentTablesOn model.toCarriers interface).Adequate := by
  intro helper args
  rfl

theorem ComponentTablesOn.adequate_extend (model : DomainModel)
    (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface)
    (adequate : tables.Adequate) (definition : CheckedDefinition) :
    (ComponentTablesOn.extend model observations tables definition).Adequate := by
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

theorem ComponentTablesOn.adequate_fold (model : DomainModel)
    (observations : SiteObservations interface)
    (tables : ComponentTablesOn model.toCarriers interface)
    (adequate : tables.Adequate) (definitions : List CheckedDefinition) :
    (definitions.foldl (ComponentTablesOn.extend model observations) tables).Adequate := by
  induction definitions generalizing tables with
  | nil => exact adequate
  | cons definition rest ih =>
    exact ih _ (ComponentTablesOn.adequate_extend model observations tables adequate definition)

/-- The component table's closed half is the same captured declaration fold,
not an independently supplied helper implementation. -/
theorem ComponentTablesOn.closed_fold (model : DomainModel)
    (observations : SiteObservations interface)
    (definitions : List CheckedDefinition)
    (tables : ComponentTablesOn model.toCarriers interface) :
    (definitions.foldl (ComponentTablesOn.extend model observations) tables).closed =
      definitions.foldl (extendMeaningsOn model observations) tables.closed := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    exact ih (ComponentTablesOn.extend model observations tables definition)

/-- Domain-model tables use the same retained bodies on both sides. -/
theorem payload_componentTablesOn_adequate (model : DomainModel)
    (observations : SiteObservations interface) (payload : Payload) :
    (payloadComponentTablesOn model observations payload).Adequate :=
  ComponentTablesOn.adequate_fold model observations _ ComponentTablesOn.adequate_empty _

/-- All-present domain components preserve the entire closed source process. -/
theorem payload_componentOn_present (model : DomainModel)
    (observations : SiteObservations interface) (payload : Payload)
    (inputs : Values model.Value payload.entry.inputs) :
    payloadComponentOn model observations payload inputs.present =
      (payloadDenoteOn model observations payload inputs).bind
        (fun results => .done results.present) := by
  have presentEnv : @Eq (Environment (Component model.Value) payload.entry.inputs)
      inputs.present.get (fun ref => some (inputs.get ref)) := by
    funext ty ref
    exact Values.get_present inputs ref
  unfold payloadComponentOn
  rw [presentEnv]
  have adequate := payload.entry.body.component_present
    (meaningOn model observations (payloadComponentTablesOn model observations payload).closed)
    (componentOperationOn model observations (payloadComponentTablesOn model observations payload))
    (componentOperationOn_adequate model observations _
      (payload_componentTablesOn_adequate model observations payload)) inputs.get
  exact adequate.trans (congrArg
    (fun table => (payload.entry.body.denote (meaningOn model observations table) inputs.get).bind
      (fun results : Values model.Value payload.entry.outputs => .done results.present))
    (ComponentTablesOn.closed_fold model observations payload.definitions _))

end Adequacy

/-- A uniform table pair as one over the uniform carriers. -/
def ComponentTables.toOn {F G : Type} {interface : PIR.Signature}
    (tables : ComponentTables F G interface) : ComponentTablesOn (uniformCarriers F G) interface :=
  ⟨tables.closed, tables.components⟩

end Evaluation

/-- Closed component tables over carriers. -/
abbrev ComponentTablesOn (carriers : Carriers) := Evaluation.ComponentTablesOn carriers closedInterface

def Payload.componentTablesOn (payload : Payload) (model : DomainModel) :
    ComponentTablesOn model.toCarriers :=
  Evaluation.payloadComponentTablesOn model SiteObservations.closed payload

def Payload.componentOn (payload : Payload) (model : DomainModel)
    (inputs : Values (Component model.Value) payload.entry.inputs) :
    Closed (Values (Component model.Value) payload.entry.outputs) :=
  Evaluation.payloadComponentOn model SiteObservations.closed payload inputs

/-! The uniform component layer is the instance at the uniform model. -/

namespace Evaluation
section Uniform
variable {F G : Type} {interface : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- The uniform meaning, with the uniform evaluator replaced by the generic one
at the uniform model and the values spelled as before. Rewriting with this
equation keeps every dependent type, unlike the equation with `meaningOn`. -/
theorem meaning_eq_operationOn (observations : SiteObservations interface)
    (table : Meanings F G interface) :
    meaning observations table =
      (⟨assignment F G, operationOn (ringModel F G) observations table⟩ : RegionMeaning dialect interface) := by
  show (⟨assignment F G, operation observations table⟩ : RegionMeaning dialect interface) = _
  rw [operation_eq_operationOn]

/-- Component execution depends on the meaning's operations and the component
operations; with the same values, equal ones give equal executions. -/
theorem component_operation_congr {Value : Ty → Type} {I : PIR.Signature}
    {first second : (op : Op) → Values Value op.arguments →
      Values (RegionFunction Value I) op.regions → PIR.Process I (Values Value op.results)}
    (same : first = second)
    (firstComponents secondComponents :
      ComponentOperations (⟨Value, first⟩ : RegionMeaning dialect I))
    (sameComponents : firstComponents = secondComponents)
    {Γ out : List Ty} (region : Region dialect Γ out) (env : Environment (Component Value) Γ) :
    region.component ⟨Value, first⟩ firstComponents env =
      region.component ⟨Value, second⟩ secondComponents env := by
  subst same
  subst sameComponents
  rfl

/-- Strict component execution depends only on the values and operations of
the meaning. -/
theorem strictComponent_operation_congr {Value : Ty → Type} {I : PIR.Signature}
    {first second : (op : Op) → Values Value op.arguments →
      Values (RegionFunction Value I) op.regions → PIR.Process I (Values Value op.results)}
    (same : first = second) :
    strictComponent (⟨Value, first⟩ : RegionMeaning dialect I) =
      strictComponent (⟨Value, second⟩ : RegionMeaning dialect I) := by
  subst same
  rfl

theorem strictComponent_meaning_eq (observations : SiteObservations interface)
    (table : Meanings F G interface) :
    strictComponent (meaning observations table) =
      strictComponent (meaningOn (ringModel F G) observations table) :=
  strictComponent_operation_congr (operation_eq_operationOn observations table)

theorem componentOperation_eq_componentOperationOn (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) :
    componentOperation observations tables =
      componentOperationOn (ringModel F G) observations tables.toOn := by
  funext op args bodies
  cases op with
  | exec primitive =>
    rcases bodies with _ | _
    conv_lhs => whnf
    conv_rhs => whnf
    split <;> rename_i sequenced
    · simp only [sequenced]
    · simp only [sequenced, Primitive.evaluate_eq_evaluateOn]
  | map spec =>
    rcases bodies with _ | _
    conv_lhs => whnf
    conv_rhs => whnf
    split <;> rename_i sequenced
    · simp only [sequenced]
    · simp only [sequenced, denoteMap_eq_denoteMapOn, ComponentTables.toOn]
  | invoke helper =>
    rcases bodies with _ | _
    show (if helper.kind = .math then invoke tables.components helper args
      else strictComponent (meaning observations tables.closed) (.invoke helper) args .nil) =
      (if helper.kind = .math then invoke tables.components helper args
      else strictComponent (meaningOn (ringModel F G) observations tables.closed) (.invoke helper) args .nil)
    rw [strictComponent_meaning_eq]
  | _ =>
    show strictComponent (meaning observations tables.closed) _ args bodies =
      strictComponent (meaningOn (ringModel F G) observations tables.closed) _ args bodies
    rw [strictComponent_meaning_eq]

theorem ComponentTables.extend_toOn (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (definition : CheckedDefinition) :
    (tables.extend observations definition).toOn =
      ComponentTablesOn.extend (ringModel F G) observations tables.toOn definition := by
  unfold ComponentTables.extend ComponentTablesOn.extend ComponentTables.toOn
  congr 1
  · exact extendMeanings_eq_extendMeaningsOn observations tables.closed definition
  · dsimp only
    congr 1
    congr 1
    funext args
    exact component_operation_congr (operation_eq_operationOn observations tables.closed) _ _
      (componentOperation_eq_componentOperationOn observations tables) definition.body args.get

theorem ComponentTables.fold_toOn (observations : SiteObservations interface) :
    ∀ (definitions : List CheckedDefinition) (tables : ComponentTables F G interface),
      (definitions.foldl (ComponentTables.extend observations) tables).toOn =
        definitions.foldl (ComponentTablesOn.extend (ringModel F G) observations) tables.toOn
  | [], _ => rfl
  | definition :: rest, tables => by
    simp only [List.foldl_cons]
    rw [ComponentTables.fold_toOn observations rest, ComponentTables.extend_toOn]

theorem payloadComponentTables_toOn (observations : SiteObservations interface) (payload : Payload) :
    (payloadComponentTables (F := F) (G := G) observations payload).toOn =
      payloadComponentTablesOn (ringModel F G) observations payload :=
  ComponentTables.fold_toOn observations payload.definitions ⟨[], []⟩

theorem payloadComponent_eq_payloadComponentOn (observations : SiteObservations interface)
    (payload : Payload) (inputs : Values (Component (assignment F G)) payload.entry.inputs) :
    payloadComponent observations payload inputs =
      payloadComponentOn (ringModel F G) observations payload inputs := by
  unfold payloadComponent payloadComponentOn
  rw [← payloadComponentTables_toOn]
  exact component_operation_congr
    (operation_eq_operationOn observations (payloadComponentTables observations payload).closed) _ _
    (componentOperation_eq_componentOperationOn observations _) payload.entry.body inputs.get

end Uniform
end Evaluation

end Zkc.Source.Structured
