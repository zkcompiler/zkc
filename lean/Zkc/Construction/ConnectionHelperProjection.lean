module

public import Zkc.Construction.ConnectionHelpers
public import Zkc.Construction.ConnectionSubstitution

@[expose] public section

/-! Exact structural projection helpers, including absent private operands.
The declaration body must be a return of typed input references. No result law
or chosen helper semantics is stored in the certificate. -/
set_option autoImplicit false
namespace Zkc.Construction.ConnectionHelpers
open Zkc.Source Zkc.Source.Structured NormalForm

structure Projection (definitions : List CheckedDefinition) (definition : CheckedDefinition) where
  before : List CheckedDefinition
  after : List CheckedDefinition
  declarations : definitions = before ++ definition :: after
  fresh : after.all (fun other => other.name != definition.name) = true
  positions : Operands definition.inputs definition.outputs
  body : definition.body = .ret positions

theorem component_find_other (model : DomainModel) {I : PIR.Signature}
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) (definitions : List CheckedDefinition)
    (name : String) (fresh : definitions.all (fun other => other.name != name) = true) :
    (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) tables).components.find?
        (fun entry => entry.helper.name == name) = tables.components.find? (fun entry => entry.helper.name == name) := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih =>
    have parts := Bool.and_eq_true_iff.mp fresh
    rw [List.foldl_cons, ih _ parts.2]
    simp only [Evaluation.ComponentTablesOn.extend, List.find?_cons, CheckedDefinition.helper]
    have different : (definition.name == name) = false := by simpa using parts.1
    rw [different]

theorem Projection.invoke (model : DomainModel) {I : PIR.Signature}
    {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (projection : Projection definitions definition)
    (values : Values (Component model.Value) definition.inputs) :
    invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩).components
      definition.helper values = .done (projection.positions.eval values.get) := by
  rcases projection with ⟨before,after,declarations,fresh,positions,body⟩
  subst definitions
  rw [List.foldl_append, List.foldl_cons]
  unfold Zkc.Source.Structured.invoke
  rw [component_find_other model (I := I) _ after definition.helper.name
    (by simpa only [CheckedDefinition.helper] using fresh)]
  simp [Evaluation.ComponentTablesOn.extend, body, Region.component]
  rfl

end Zkc.Construction.ConnectionHelpers

namespace Zkc.Construction.ConnectionSubstitution
open Zkc.Source Zkc.Source.Structured NormalForm

def valueHead {scope : Scope} {ty : Ty} (value : Term [] scope ty) :
    Substitution (.value ty :: scope) scope
  | _, .here => value
  | _, .there binder => identityArgument binder

theorem valueHead_denote {model : DomainModel} {I : PIR.Signature} {scope : Scope}
    {ty : Ty} {out : List Ty} {callees : List CalleeKey} (value : Term [] scope ty)
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    (next : Form [] callees (.value ty :: scope) out) (binders : Binders model scope) :
    (form next (valueHead value)).denoteOn model actions tables (LawResults.empty model) context runs processes binders =
    next.denoteOn model actions tables (LawResults.empty model) context runs processes
      (.cons (value.eval (LawResults.empty model) binders) binders) := by
  apply form_denote
  intro slot binder
  cases binder with
  | here => rfl
  | there binder => exact identityArgument_eval binder binders

def tupleHead {scope : Scope} {types : List Ty} (values : Values (Comp [] scope) types) :
    Substitution (.tuple types :: scope) scope
  | _, .here => values
  | _, .there binder => identityArgument binder

theorem tupleHead_denote {model : DomainModel} {I : PIR.Signature} {scope : Scope}
    {types out : List Ty} {callees : List CalleeKey} (values : Values (Comp [] scope) types)
    (actions : PIR.OperationInterpretation (Interface model) I) (tables : Tables model I)
    (context : ProtocolContext) (runs : Runs model I) (processes : CalleeProcesses model callees I)
    (next : Form [] callees (.tuple types :: scope) out) (binders : Binders model scope) :
    (form next (tupleHead values)).denoteOn model actions tables (LawResults.empty model) context runs processes binders =
    next.denoteOn model actions tables (LawResults.empty model) context runs processes
      (.cons (Comps.eval (LawResults.empty model) values binders) binders) := by
  apply form_denote
  intro slot binder
  cases binder with
  | here => rfl
  | there binder => exact identityArgument_eval binder binders

end Zkc.Construction.ConnectionSubstitution
