module

public import Zkc.IR.Construction.ConnectionHelperProjection
public import Zkc.IR.Construction.ConnectionComputation

@[expose] public section

/-! Exact expansion of a retained Math helper containing one total primitive.
Only the finite original declaration body is admitted. The result expression
is built from that primitive and its typed operand/return selections; no
mathematical law or supplied semantic callback is part of the certificate. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Zkc.Construction.ConnectionHelpers
open Zkc.Source Zkc.Source.Structured NormalForm ConnectionComputation

attribute [local implicit_reducible] CheckedDefinition.helper

def calculationSourceRegions (operation : Calculation) : Regions dialect operation.op.regions := by
  cases operation <;> exact .nil

structure CalculationBody (definitions : List CheckedDefinition) (definition : CheckedDefinition) where
  before : List CheckedDefinition
  after : List CheckedDefinition
  declarations : definitions = before ++ definition :: after
  fresh : after.all (fun other => other.name != definition.name) = true
  operation : Calculation
  total : operation.op.total = true
  inputs : Operands definition.inputs operation.op.arguments
  returned : Operands (operation.op.results ++ definition.inputs) definition.outputs
  body : definition.body = .letOp operation.op inputs (calculationSourceRegions operation) (.ret returned)

/-- Only operations whose existing component interpretation is strict can be
skipped for unavailable operands. An effectful call or service is not admitted
by this rule. A selected branch still owns both of its original regions. -/
inductive StrictStep : Op → Prop where
  | total {op : Op} (checked : op.total = true) : StrictStep op
  | branch (captures outputs : List Ty) : StrictStep (.branch captures outputs)

theorem StrictStep.component {op : Op} (checked : StrictStep op) (model : DomainModel)
    {I : PIR.Signature} (observations : SiteObservations I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (args : Values (Component model.Value) op.arguments)
    (bodies : Values (RegionFunction model.Value I) op.regions) :
    Evaluation.componentOperationOn model observations tables op args bodies =
      strictComponent (Evaluation.meaningOn model observations tables.closed) op args bodies := by
  cases checked with
  | total h => exact componentOperationOn_total model observations tables _ h _ _
  | branch captures outputs => rfl

structure StrictBody (definitions : List CheckedDefinition) (definition : CheckedDefinition) where
  before : List CheckedDefinition
  after : List CheckedDefinition
  declarations : definitions = before ++ definition :: after
  fresh : after.all (fun other => other.name != definition.name) = true
  operation : Op
  strict : StrictStep operation
  inputs : Operands definition.inputs operation.arguments
  regions : Regions dialect operation.regions
  returned : Operands (operation.results ++ definition.inputs) definition.outputs
  body : definition.body = .letOp operation inputs regions (.ret returned)

def selectTerms {scope : Scope} {inputs : List Ty} (terms : Terms [] scope inputs) :
    {selected : List Ty} → Operands inputs selected → Terms [] scope selected
  | _, .nil => .nil
  | _, .cons position rest => .cons (termsAt terms position) (selectTerms terms rest)

def CalculationBody.result {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (certificate : CalculationBody definitions definition) {scope : Scope}
    (arguments : Terms [] scope definition.inputs) : Values (Comp [] scope) definition.outputs :=
  lookup ((calculation certificate.operation.op certificate.total
    (selectTerms arguments certificate.inputs)).append (components arguments)) certificate.returned

/-- A missing operand skips this strict primitive but preserves any original
components explicitly selected by the helper's complete return row. -/
def StrictBody.missingResult {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (certificate : StrictBody definitions definition) {scope : Scope}
    (arguments : Values (Comp [] scope) definition.inputs) : Values (Comp [] scope) definition.outputs :=
  lookup ((absentComps certificate.operation.results).append arguments) certificate.returned

theorem selectTerms_eval {model : DomainModel} {scope : Scope} {inputs selected : List Ty}
    (arguments : Terms [] scope inputs) (positions : Operands inputs selected) (binders : Binders model scope) :
    Terms.eval (LawResults.empty model) (selectTerms arguments positions) binders =
      Operands.eval (Terms.eval (LawResults.empty model) arguments binders).get positions := by
  induction positions with
  | nil => rfl
  | cons position rest ih =>
    simp only [selectTerms, Terms.eval, Operands.eval, termsAt_eval, entryAt_eq_get, ih]

private theorem append_get {types rest : List Ty} {Value : Ty → Type}
    (first : Values Value types) (second : Values Value rest) :
    @Eq (Environment Value (types ++ rest)) (first.append second).get (Environment.prepend second.get first) := by
  induction first with
  | nil => rfl
  | cons value tail ih =>
    funext ty reference
    cases reference with
    | here => rfl
    | there reference => exact congrFun (congrFun ih _) reference

theorem CalculationBody.invoke (model : DomainModel) {I : PIR.Signature}
    {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (certificate : CalculationBody definitions definition) {scope : Scope}
    (arguments : Terms [] scope definition.inputs) (binders : Binders model scope) :
    invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩).components
      definition.helper (Comps.eval (LawResults.empty model) (components arguments) binders) =
        .done (Comps.eval (LawResults.empty model) (certificate.result arguments) binders) := by
  rcases certificate with ⟨before,after,declarations,fresh,operation,total,inputs,returned,body⟩
  subst definitions
  rw [List.foldl_append, List.foldl_cons]
  unfold Zkc.Source.Structured.invoke
  rw [component_find_other model (I := I) _ after definition.helper.name
    (by simpa only [CheckedDefinition.helper] using fresh)]
  simp only [Evaluation.ComponentTablesOn.extend, List.find?_cons, beq_self_eq_true]
  simp only [↓reduceDIte, body, Region.component]
  rw [componentOperationOn_total model (.silent I) _ operation.op total]
  rw [components_eval]
  have presentEnv : @Eq (Environment (Component model.Value) definition.inputs)
      (Terms.eval (LawResults.empty model) arguments binders).present.get
      (fun reference => some ((Terms.eval (LawResults.empty model) arguments binders).get reference)) := by
    funext ty reference
    exact Values.get_present _ reference
  rw [presentEnv, Operands.eval_present]
  rw [strictComponent_adequate]
  simp only [Evaluation.meaningOn]
  rw [operationOn_total model _ _ _ total]
  simp only [PIR.Process.bind]
  simp only [CalculationBody.result, lookup_eq_eval, comps_eval_operands,
    comps_eval_append, calculation_eval, components_eval, selectTerms_eval]
  rw [append_get, presentEnv]

theorem StrictBody.invokeMissing (model : DomainModel) {I : PIR.Signature}
    {definitions : List CheckedDefinition} {definition : CheckedDefinition}
    (certificate : StrictBody definitions definition) {scope : Scope}
    (arguments : Values (Comp [] scope) definition.inputs)
    (missing : anyAbsent (lookup arguments certificate.inputs) = true)
    (binders : Binders model scope) :
    Zkc.Source.Structured.invoke (definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent I)) ⟨[], []⟩).components
      definition.helper (Comps.eval (LawResults.empty model) arguments binders) =
        .done (Comps.eval (LawResults.empty model) (certificate.missingResult arguments) binders) := by
  rcases certificate with ⟨before,after,declarations,fresh,operation,strict,inputs,regions,returned,body⟩
  subst definitions
  rw [List.foldl_append, List.foldl_cons]
  unfold Zkc.Source.Structured.invoke
  rw [component_find_other model (I := I) _ after definition.helper.name
    (by simpa only [CheckedDefinition.helper] using fresh)]
  simp only [Evaluation.ComponentTablesOn.extend, List.find?_cons, beq_self_eq_true]
  simp only [↓reduceDIte, body, Region.component]
  rw [strict.component model (.silent I) _]
  have absent := anyAbsent_sequence (LawResults.empty model) binders (lookup arguments inputs) missing
  rw [lookup_eq_eval, comps_eval_operands] at absent
  simp only [strictComponent, absent, PIR.Process.bind]
  simp only [StrictBody.missingResult, lookup_eq_eval, comps_eval_operands,
    comps_eval_append, comps_eval_absent]
  rw [append_get]

end Zkc.Construction.ConnectionHelpers
