module

public import Zkc.Source.Structured.DomainEvaluation
public import Zkc.Source.Structured.Component

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
