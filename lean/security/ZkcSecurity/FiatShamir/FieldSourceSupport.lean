module

public import ZkcSecurity.FiatShamir.DomainSourceReading
public import Zkc.Source.OperationSupport

@[expose] public section

/-! A finite source check identifies field-message source mathematics.
Helper computations use the existing closed interpretation and its naturality
laws. Protocol bodies use their existing denotation, including captured callees
and arbitrary repeat bounds. No source or artifact interpreter is duplicated.
-/
set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.FieldSourceSupport
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction

attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions

/-- Proof messages in this reusable fragment carry fields in their original nominal domain. -/
def operation : ProtocolOp → Bool
  | .exchange (.field _) .. => true
  | .exchange .. => false
  | _ => true

/-- The actual stored bodies and all nested callbacks are inspected once. -/
def check (program : Program) : Bool :=
  program.payload.protocols.all fun definition => SourceSupport.region operation definition.body

/-- Boundaries and service queries are supported; sends and receives must carry fields. -/
def sourceOperation {carriers : Carriers} : (Occurrence.signature carriers).Op → Prop
  | .action (.receive (.field _) ..) | .action (.send (ty := .field _) ..) => True
  | .action (.receive ..) | .action (.send ..) => False
  | _ => True

private def fromClosed {I : PIR.Signature} : PIR.OperationInterpretation closedInterface I :=
  fun operation => nomatch operation

private def helperTables (model : DomainModel) (interface : PIR.Signature) (definitions : List CheckedDefinition) :=
  definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent interface)) ⟨[], []⟩

private theorem helpers (model : DomainModel) (definitions : List CheckedDefinition) :
    Evaluation.ComponentTablesOn.Interprets (model := model)
      (fromClosed (I := Occurrence.signature model.toCarriers))
      (helperTables model closedInterface definitions)
      (helperTables model (Occurrence.signature model.toCarriers) definitions) :=
  Evaluation.ComponentTablesOn.fold_interpret fromClosed (SiteObservations.silent_interpret _)
    (.empty _) definitions

private theorem calculation (model : DomainModel) (definitions : List CheckedDefinition)
    (op : Op) (allowed : op.isCalculation = true) (args : Values (Component model.Value) op.arguments) :
    OperationSupport (sourceOperation (carriers := model.toCarriers))
      (Evaluation.componentOperationOn model (.silent _)
        (helperTables model (Occurrence.signature model.toCarriers) definitions)
        op args (op.calculationRegions allowed)) := by
  have transported := Evaluation.componentOperationOn_interpret fromClosed
    (SiteObservations.silent_interpret _) (helpers model definitions)
    op args (op.calculationRegions (I := closedInterface) allowed)
  rw [Op.calculationRegions_translate] at transported
  rw [← transported]
  exact OperationSupport.closed _ _ _ (fun operation => nomatch operation)

private theorem localHelper (model : DomainModel) (definitions : List CheckedDefinition)
    (helper : Helper) (args : Values model.Value helper.inputs) :
    OperationSupport (sourceOperation (carriers := model.toCarriers))
      (invoke (helperTables model (Occurrence.signature model.toCarriers) definitions).closed
        helper args) := by
  rw [← (helpers model definitions).closed helper args]
  exact OperationSupport.closed _ _ _ (fun operation => nomatch operation)

/-- Captured protocol tables carry the same all-input support law. -/
def Protocols (model : DomainModel) (table : ProtocolTable model.Value (Occurrence.signature model.toCarriers)) : Prop :=
  ∀ signature context self args, OperationSupport (sourceOperation (carriers := model.toCarriers)) (invokeProtocol table signature context self args)

private theorem supportsRepeat (model : DomainModel) (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (count : Option Nat) (state : Values (Component model.Value) spec.state)
    (captures : Values (Component model.Value) spec.captures)
    (body : RegionFunction (Component model.Value) (Occurrence.signature model.toCarriers)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (supported : ∀ args, OperationSupport (sourceOperation (carriers := model.toCarriers)) (body args)) (site : String) :
    OperationSupport (sourceOperation (carriers := model.toCarriers)) (denoteRepeatOn spec context self count state captures body Occurrence.iterations site) := by
  unfold denoteRepeatOn
  by_cases participating : (spec.roles.map context.roles).contains self = true
  · rw [ite_eq_left participating]
    cases count with
    | none => trivial
    | some count =>
      dsimp only
      by_cases bounded : count ≤ spec.maximum
      · rw [ite_eq_left bounded]
        apply OperationSupport.finite
        intro state index
        apply OperationSupport.bind (next := fun results => .done (maskValues self (context.mapScopes spec.stateScopes) results))
        · exact ⟨trivial, fun _ => (supported _).bind _ (fun _ => ⟨trivial, fun _ => trivial⟩)⟩
        · intro _; trivial
      · rw [ite_eq_right bounded]; trivial
  · rw [ite_eq_right participating]; trivial

private theorem operation_support (model : DomainModel) (definitions : List CheckedDefinition)
    (table : ProtocolTable model.Value (Occurrence.signature model.toCarriers)) (protocols : Protocols model table)
    (context : ProtocolContext) (self : Nat) (op : ProtocolOp)
    (args : Values (Component model.Value) op.arguments)
    (callbacks : Values (RegionFunction (Component model.Value) (Occurrence.signature model.toCarriers)) op.regions)
    (checked : operation op = true)
    (bodies : ∀ {signature} (ref : Var op.regions signature) arguments,
      OperationSupport (sourceOperation (carriers := model.toCarriers)) (callbacks.get ref arguments)) :
    OperationSupport (sourceOperation (carriers := model.toCarriers))
      (protocolOperationWithOn model (.silent _) Occurrence.actions
        (helperTables model (Occurrence.signature model.toCarriers) definitions)
        self op args callbacks table context Occurrence.iterations) := by
  cases op with
  | calculate op allowed =>
    exact calculation model definitions op allowed args
  | localCall helper kind owner site =>
    cases callbacks
    change OperationSupport sourceOperation
      (Participant.owned self (context.roles owner)
        (invoke (helperTables model (Occurrence.signature model.toCarriers) definitions).closed helper) args)
    unfold Participant.owned
    split
    · cases RoleFamily.sequence args with
      | none => trivial
      | some values => exact (localHelper model definitions helper values).bind _ (fun _ => trivial)
    · trivial
  | guard owner site =>
    cases callbacks
    cases args with
    | cons condition rest =>
      cases rest
      simp only [protocolOperationWithOn, Participant.guard]
      split
      · cases condition with
        | none => trivial
        | some value => cases value <;> trivial
      · trivial
  | exchange ty sender receiver site =>
    cases callbacks
    cases args with
    | cons value rest =>
      cases rest
      cases ty <;> simp only [operation, Bool.false_eq_true] at checked
      rename_i field
      simp only [protocolOperationWithOn, Participant.exchange]
      split
      · cases value with
        | none => trivial
        | some value => exact ⟨trivial, fun _ => trivial⟩
      · split
        · exact ⟨trivial, fun _ => trivial⟩
        · trivial
  | restrict => cases args with
    | cons value rest => cases rest; trivial
  | draw owner field site =>
    set_option backward.isDefEq.respectTransparency false in
      cases callbacks
      simp only [protocolOperationWithOn, Participant.query]
      split
      · cases RoleFamily.sequence args with
        | none => trivial
        | some values => exact ⟨trivial, fun _ => trivial⟩
      · trivial
  | statement => trivial
  | mark => cases args; trivial
  | protocolApply signature roles site =>
    cases callbacks
    simp only [protocolOperationWithOn]
    by_cases inside : (context.enter site roles).contains signature self = true
    · rw [ite_eq_left inside]; exact protocols _ _ _ _
    · rw [ite_eq_right inside]; trivial
  | «repeat» spec site =>
    cases args with
    | cons count values =>
      exact supportsRepeat model spec context self count _ _ _ (bodies .here) site

private theorem body (model : DomainModel) (definitions : List CheckedDefinition)
    (table : ProtocolTable model.Value (Occurrence.signature model.toCarriers)) (protocols : Protocols model table)
    (context : ProtocolContext) (self : Nat) {Γ out} (region : Region protocolDialect Γ out)
    (checked : SourceSupport.region operation region = true) (args : Environment (Component model.Value) Γ) :
    OperationSupport (sourceOperation (carriers := model.toCarriers))
      (region.denote (participantMeaningWithOn model (.silent _) Occurrence.actions
        (helperTables model (Occurrence.signature model.toCarriers) definitions)
        self table context Occurrence.iterations) args) :=
  SourceSupport.denote operation sourceOperation
    (participantMeaningWithOn model (.silent _) Occurrence.actions
      (helperTables model (Occurrence.signature model.toCarriers) definitions) self table context Occurrence.iterations)
    (operation_support model definitions table protocols context self) region checked args

private theorem extend (model : DomainModel) (definitions : List CheckedDefinition)
    (table : ProtocolTable model.Value (Occurrence.signature model.toCarriers)) (protocols : Protocols model table)
    (definition : CheckedProtocol) (checked : SourceSupport.region operation definition.body = true) :
    Protocols model (extendProtocolTableOn model (.silent _) Occurrence.actions
      (helperTables model (Occurrence.signature model.toCarriers) definitions)
      table definition Occurrence.iterations) := by
  intro signature context self args
  by_cases names : definition.signature.name = signature.name
  · by_cases same : definition.signature = signature
    · subst signature
      rw [extendProtocolTableOn, invokeProtocol_cons_same]
      exact (body model definitions table protocols context self definition.body checked _).bind _ (fun _ => trivial)
    · rw [extendProtocolTableOn, invokeProtocol_cons_mismatch _ _ _ names same]
      trivial
  · rw [extendProtocolTableOn, invokeProtocol_cons_other _ _ _ names]
    exact protocols _ _ _ _

/-- The finite stored-body check proves support for the actual source process,
for every model, role, input tuple, private handle and provider reply. -/
theorem participant (program : Program) (checked : check program = true) (model : DomainModel)
    (role : Nat) (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    OperationSupport (sourceOperation (carriers := model.toCarriers)) (Occurrence.participant model program role inputs) := by
  have fold : ∀ definitions : List CheckedProtocol,
      definitions.all (fun definition => SourceSupport.region operation definition.body) = true →
      ∀ table, Protocols model table →
      Protocols model (definitions.foldl (fun table definition => extendProtocolTableOn model (.silent _)
        Occurrence.actions (program.payload.definitions.foldl
          (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩) table definition Occurrence.iterations) table) := by
    intro definitions
    induction definitions with
    | nil => intro _ table supported; exact supported
    | cons definition rest ih =>
      intro checked table supported
      simp only [List.all_cons, Bool.and_eq_true] at checked
      exact ih checked.2 _ (extend model program.payload.definitions table supported definition checked.1)
  exact fold program.payload.protocols checked [] (fun _ _ _ _ => trivial) _ _ _ _

end ZkcSecurity.FiatShamir.FieldSourceSupport
