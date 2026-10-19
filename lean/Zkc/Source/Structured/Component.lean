module

public import Zkc.Source.Structured.Meaning
public import Zkc.Source.Component

@[expose] public section

/-! Paired meanings of the same retained bodies. Math calls preserve optional
operand dependencies; Local calls sequence every operand through the closed
meaning. Nested callbacks always use the original nonoptional interpreter. -/

set_option autoImplicit false
namespace Zkc.Source.Structured
namespace Evaluation

abbrev ComponentMeanings (F G : Type) (interface : PIR.Signature) :=
  HelperTable (Component (assignment F G)) interface

/-- Two instances of one generic table, built from the same stored bodies. -/
structure ComponentTables (F G : Type) (interface : PIR.Signature) where
  closed : HelperTable (assignment F G) interface
  components : ComponentMeanings F G interface

variable {F G : Type} {interface : PIR.Signature}
variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

/-- Only Math calls bypass operand sequencing. Local calls and all other
operations reuse the shared strict evaluator, including effects and stops. -/
def componentOperation (observations : SiteObservations interface) (tables : ComponentTables F G interface) :
    ComponentOperations (meaning observations tables.closed)
  | .exec primitive, args, .nil =>
      match RoleFamily.sequence args with
      | none => .halt .incomplete
      | some values => (primitiveOutcome (primitive.evaluate values)).bind fun result =>
          .done result.present
  | .map spec, args, .nil =>
      match RoleFamily.sequence (Value := assignment F G) (types := spec.arguments) args with
      | none => .halt .incomplete
      | some values => (denoteMap tables.closed spec values).bind fun result =>
          .done result.present
  | .invoke helper, args, .nil =>
      if helper.kind = .math then invoke tables.components helper args
      else strictComponent (meaning observations tables.closed) (.invoke helper) args .nil
  | op, args, bodies => strictComponent (meaning observations tables.closed) op args bodies

theorem componentOperation_map_present (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (spec : MapSpec)
    (args : Values (assignment F G) spec.arguments) :
    componentOperation observations tables (.map spec) args.present .nil =
      (denoteMap tables.closed spec args).bind (fun result => .done result.present) := by
  simp only [componentOperation, RoleFamily.sequence_present]
  rfl

/-- Direct optional maps require every operand, including unused broadcasts. -/
theorem componentOperation_map_absent (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (spec : MapSpec)
    (args : Values (Component (assignment F G)) spec.arguments)
    (absent : RoleFamily.sequence args = none) :
    componentOperation observations tables (.map spec) args .nil = .halt .incomplete := by
  simp only [componentOperation, absent]

theorem componentOperation_math (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (helper : Helper) (kind : helper.kind = .math)
    (args : Values (Component (assignment F G)) helper.inputs) :
    componentOperation observations tables (.invoke helper) args .nil =
      invoke tables.components helper args := by
  simp only [componentOperation, kind, ↓reduceIte]
  rfl

theorem componentOperation_local (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (helper : Helper) (kind : helper.kind = .local)
    (args : Values (Component (assignment F G)) helper.inputs) :
    componentOperation observations tables (.invoke helper) args .nil =
      strictComponent (meaning observations tables.closed) (.invoke helper) args .nil := by
  simp [componentOperation, kind]

/-- Present Local arguments preserve a stop, including zero-result calls. -/
theorem componentOperation_local_stops (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (helper : Helper) (kind : helper.kind = .local)
    (args : Values (assignment F G) helper.inputs) (reason : PIR.Stop)
    (stops : invoke tables.closed helper args = .halt reason) :
    componentOperation observations tables (.invoke helper) args.present .nil = .halt reason := by
  rw [componentOperation_local observations tables helper kind]
  exact (strictComponent_adequate (meaning observations tables.closed) (.invoke helper) args .nil).trans
    (congrArg (fun process => process.bind (fun result => .done result.present)) stops)

/-- A nullary mark is reached even when its result tuple is empty. -/
theorem componentOperation_mark (observations : SiteObservations interface)
    (tables : ComponentTables F G interface) (site : String) :
    componentOperation observations tables (.mark site) .nil .nil =
      (observations.mark site).bind (fun _ => .done .nil) := by
  change strictComponent (meaning observations tables.closed) (.mark site)
    (Values.nil : Values (assignment F G) []).present .nil = _
  exact (strictComponent_adequate (meaning observations tables.closed) (.mark site) .nil .nil).trans
    (PIR.Proc.bind_assoc (observations.mark site)
      (fun _ => .done (Values.nil : Values (assignment F G) []))
      (fun result => .done result.present))

def ComponentTables.extend (observations : SiteObservations interface) (tables : ComponentTables F G interface)
    (definition : CheckedDefinition) :
    ComponentTables F G interface where
  closed := extendMeanings observations tables.closed definition
  components := ⟨definition.helper, fun args =>
    definition.body.component (meaning observations tables.closed) (componentOperation observations tables) args.get⟩ ::
      tables.components

def ComponentTables.Adequate (tables : ComponentTables F G interface) : Prop :=
  ∀ helper args, invoke tables.components helper args.present =
    (invoke tables.closed helper args).bind fun results => .done results.present

theorem componentOperation_adequate (observations : SiteObservations interface) (tables : ComponentTables F G interface)
    (adequate : tables.Adequate) :
    ComponentOperations.Adequate (meaning observations tables.closed) (componentOperation observations tables) := by
  intro op args bodies
  cases op <;> try exact strictComponent_adequate (meaning observations tables.closed) _ args bodies
  case exec primitive =>
    cases bodies
    simp only [componentOperation, RoleFamily.sequence_present]
    rfl
  case map spec =>
    cases bodies
    exact componentOperation_map_present observations tables spec args
  case invoke helper =>
    cases bodies
    cases helper with
    | mk name kind inputs outputs =>
      cases kind with
      | math => exact adequate _ args
      | «local» => exact strictComponent_adequate (meaning observations tables.closed) _ args .nil

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem ComponentTables.adequate_empty : (⟨[], []⟩ : ComponentTables F G interface).Adequate := by
  intro helper args
  rfl

theorem ComponentTables.adequate_extend (observations : SiteObservations interface) (tables : ComponentTables F G interface)
    (adequate : tables.Adequate) (definition : CheckedDefinition) :
    (tables.extend observations definition).Adequate := by
  intro helper args
  by_cases name : definition.helper.name = helper.name
  · by_cases signature : definition.helper = helper
    · subst helper
      simp only [extend, extendMeanings]
      simp [invoke]
      have presentEnv : @Eq (Environment (Component (assignment F G)) definition.inputs)
          args.present.get (fun ref => some (args.get ref)) := by
        funext ty ref
        exact Values.get_present args ref
      rw [presentEnv]
      exact definition.body.component_present (meaning observations tables.closed) (componentOperation observations tables)
        (componentOperation_adequate observations tables adequate) args.get
    · simp [extend, extendMeanings, invoke, name, signature, PIR.Proc.bind]
  · simp only [extend, extendMeanings]
    simp only [invoke, List.find?_cons, show (definition.helper.name == helper.name) = false from
      beq_eq_false_iff_ne.mpr name]
    exact adequate helper args

theorem ComponentTables.adequate_fold (observations : SiteObservations interface) (tables : ComponentTables F G interface)
    (adequate : tables.Adequate) (definitions : List CheckedDefinition) :
    (definitions.foldl (ComponentTables.extend observations) tables).Adequate := by
  induction definitions generalizing tables with
  | nil => exact adequate
  | cons definition rest ih => exact ih _ (tables.adequate_extend observations adequate definition)

theorem ComponentTables.closed_fold (observations : SiteObservations interface) (tables : ComponentTables F G interface)
    (definitions : List CheckedDefinition) :
    (definitions.foldl (ComponentTables.extend observations) tables).closed =
      definitions.foldl (extendMeanings observations) tables.closed := by
  induction definitions generalizing tables with
  | nil => rfl
  | cons definition rest ih => exact ih (tables.extend observations definition)

def payloadComponentTables (observations : SiteObservations interface) (payload : Payload) :
    ComponentTables F G interface :=
  payload.definitions.foldl (ComponentTables.extend observations) ⟨[], []⟩

def payloadComponent (observations : SiteObservations interface) (payload : Payload)
    (inputs : Values (Component (assignment F G)) payload.entry.inputs) :
    PIR.Proc interface (Values (Component (assignment F G)) payload.entry.outputs) :=
  payload.entry.body.component
    (meaning observations (payloadComponentTables observations payload).closed)
    (componentOperation observations (payloadComponentTables observations payload)) inputs.get

variable (observations : SiteObservations interface)

theorem payload_componentTables_closed (payload : Payload) :
    (payloadComponentTables (F := F) (G := G) observations payload).closed =
      payloadMeanings observations payload :=
  ComponentTables.closed_fold observations _ _

theorem payload_componentTables_adequate (payload : Payload) :
    (payloadComponentTables (F := F) (G := G) observations payload).Adequate :=
  ComponentTables.adequate_fold observations _ ComponentTables.adequate_empty _

/-- All-present component execution equals closed execution with present results.
This preserves stops even for bodies outside the total mathematical fragment. -/
theorem payload_component_present (payload : Payload)
    (inputs : Values (assignment F G) payload.entry.inputs) :
    payloadComponent observations payload inputs.present =
      (payloadDenote observations payload inputs).bind fun results => .done results.present := by
  have presentEnv : @Eq (Environment (Component (assignment F G)) payload.entry.inputs)
      inputs.present.get (fun ref => some (inputs.get ref)) := by
    funext ty ref
    exact Values.get_present inputs ref
  unfold payloadComponent
  rw [presentEnv]
  have adequate := payload.entry.body.component_present
    (meaning observations (payloadComponentTables observations payload).closed)
    (componentOperation observations (payloadComponentTables observations payload))
    (componentOperation_adequate observations _ (payload_componentTables_adequate observations payload)) inputs.get
  exact adequate.trans (congrArg
    (fun table => (payload.entry.body.denote (meaning observations table) inputs.get).bind
      (fun results : Values (assignment F G) payload.entry.outputs => .done results.present))
    (payload_componentTables_closed observations payload))

end Evaluation

/-- Closed views specialize only the effect interface, retaining both value types. -/
abbrev ComponentTables (F G : Type) := Evaluation.ComponentTables F G closedInterface

def Payload.componentTables (payload : Payload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] : ComponentTables F G :=
  Evaluation.payloadComponentTables SiteObservations.closed payload

def Payload.component (payload : Payload) (F G : Type)
    [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]
    (inputs : Values (Component (assignment F G)) payload.entry.inputs) :
    Closed (Values (Component (assignment F G)) payload.entry.outputs) :=
  Evaluation.payloadComponent SiteObservations.closed payload inputs

end Zkc.Source.Structured
