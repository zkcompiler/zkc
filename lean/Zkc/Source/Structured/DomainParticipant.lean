module

public import Zkc.Source.Structured.DomainComponent
public import Zkc.Source.Structured.OpenMeaning

@[expose] public section

/-! Participant meanings over domain models.

These are the participant interface, the site-observation interface, protocol
operations, retained repeats, protocol tables and the participant views of
`Participant`, `Repeat` and `OpenMeaning` with the uniform values replaced by a
domain model's. Service queries keep the shared signature `services`.

The uniform participant semantics is the instance at `ringModel F G`, by the
equations at the end of this module, for every effect interface and in the
plain participant view. The uniform site-observation interface is its own
inductive type, so the observed views are related through the plain view. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

/-- The participant interface over carriers: the actual service handle and the
values of the carriers. -/
abbrev participantInterfaceOn (carriers : Carriers) : PIR.Signature :=
  Participant.interface Nat Ty services carriers.Value

inductive ObservedActionOn (carriers : Carriers) where
  | mark (site : String)
  | action (value : (participantInterfaceOn carriers).Op)

abbrev observedInterfaceOn (carriers : Carriers) : PIR.Signature where
  Op := ObservedActionOn carriers
  Reply
    | .mark _ => Unit
    | .action action => (participantInterfaceOn carriers).Reply action

section Carriers
variable {carriers : Carriers}

/-- Site observations are internal and do not acquire provider replies. -/
def observeActionOn : PIR.OperationInterpretation
    (participantInterfaceOn carriers) (observedInterfaceOn carriers) :=
  fun action => .call (.action action) .done

/-- The logical participant process explicitly forgets only site observations. -/
def forgetSitesOn : PIR.OperationInterpretation
    (observedInterfaceOn carriers) (participantInterfaceOn carriers)
  | .mark _ => .done ()
  | .action action => .call action .done

variable (carriers) in
def observedSitesOn : SiteObservations (observedInterfaceOn carriers) where
  mark site := .call (.mark site) .done

variable (carriers) in
/-- Protocol actions retain their actual provider replies in the plain view. -/
def participantActionsOn : PIR.OperationInterpretation
    (participantInterfaceOn carriers) (participantInterfaceOn carriers) := fun action => .call action .done

theorem observedSitesOn_forgetSitesOn :
    SiteObservations.Interprets forgetSitesOn (observedSitesOn carriers)
      (.silent (participantInterfaceOn carriers)) := by
  intro site
  rfl

theorem observeActionOn_forgetSitesOn (action : (participantInterfaceOn carriers).Op) :
    (observeActionOn action).interpret forgetSitesOn = participantActionsOn carriers action := by
  simp only [observeActionOn, forgetSitesOn, participantActionsOn, PIR.Proc.interpret,
    PIR.Proc.bind_done]

end Carriers

abbrev OpenTablesOn (carriers : Carriers) :=
  Evaluation.ComponentTablesOn carriers (observedInterfaceOn carriers)

namespace Repeat

variable {carriers : Carriers} {I : PIR.Signature}

/-- The concrete callback transition used by `denoteRepeatOn`. -/
abbrev stepOn (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) I
      (.index :: (spec.state ++ spec.captures), spec.state))
    (state : Values (Component carriers.Value) spec.state) (index : Nat) :=
  (body (.cons (some index)
    ((maskValues self (context.mapScopes spec.stateScopes) state).append captures))).bind
      (fun results => .done (maskValues self (context.mapScopes spec.stateScopes) results))

end Repeat

/-- Retained repeat over carriers; the bound is tested before constructing its
range, and the context and root participant never change. -/
def denoteRepeatOn {carriers : Carriers} {I : PIR.Signature}
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat)
    (count : Option Nat)
    (state : Values (Component carriers.Value) spec.state)
    (captures : Values (Component carriers.Value) spec.captures)
    (body : RegionFunction (Component carriers.Value) I
      (.index :: (spec.state ++ spec.captures), spec.state)) :
    PIR.Proc I (Values (Component carriers.Value) spec.state) :=
  if (spec.roles.map context.roles).contains self then
    match count with
    | none => .halt .incomplete
    | some count =>
      if count ≤ spec.maximum then
        let mask := maskValues self (context.mapScopes spec.stateScopes)
        Finite.execute (.elements (List.range count))
          (Repeat.stepOn spec context self captures body) (mask state)
      else .halt .refused
  else .done (Values.absent carriers.Value spec.state)

section Model
variable (model : DomainModel)

def protocolOperationWithOn {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) (self : Nat)
    (op : ProtocolOp) (args : Values (Component model.Value) op.arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I) op.regions)
    (protocols : ProtocolTable model.Value I := [])
    (context : ProtocolContext := {}) :
    PIR.Proc I (Values (Component model.Value) op.results) :=
  match op, args with
  | .repeat spec _, .cons count values =>
    let parts := Values.split spec.state values
    denoteRepeatOn spec context self count parts.1 parts.2 (callbacks.get .here)
  | .calculate op allowed, args =>
    Evaluation.componentOperationOn model observations tables op args (op.calculationRegions allowed)
  | .localCall helper _ owner _, args =>
    Participant.owned self (context.roles owner) (invoke tables.closed helper) args
  | .guard owner _, .cons condition .nil =>
    ((Participant.guard (services := services) (Value := model.Value) self (context.roles owner)
      condition).interpret actions).bind fun _ => .done .nil
  | .exchange _ sender receiver site, .cons value .nil =>
    ((Participant.exchange (services := services) self (context.roles sender) (context.roles receiver)
      (qualifyProtocolSite context.applicationPrefix site) value).interpret
      actions).bind fun result => .done (.cons result .nil)
  | .restrict _ roles, .cons value .nil =>
    .done (.cons (Participant.restrict ((roles.map context.roles).contains self) value) .nil)
  | .draw owner field site, args =>
    ((Participant.query (services := services) self (context.roles owner)
      (qualifyProtocolSite context.applicationPrefix site) field args).interpret
      actions).bind fun result => .done (.cons result .nil)
  | .statement .., _ => .done .nil
  | .mark site, .nil =>
    (observations.mark (qualifyProtocolSite context.applicationPrefix site)).bind fun _ => .done .nil
  | .protocolApply signature roles site, args =>
    let child := context.enter site roles
    if child.contains signature self then invokeProtocol protocols signature child self args
    else .done (Values.absent model.Value signature.outputs)

abbrev participantMeaningWithOn {I : PIR.Signature} (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I) (self : Nat)
    (protocols : ProtocolTable model.Value I := [])
    (context : ProtocolContext := {}) : RegionMeaning protocolDialect I where
  Value := Component model.Value
  operation := fun op args callbacks =>
    protocolOperationWithOn model observations actions tables self op args callbacks protocols context

/-- One body denotation, with optional input and output masks at this context. -/
def CheckedProtocol.denoteWithOn {I : PIR.Signature}
    (definition : CheckedProtocol) (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
    (protocols : ProtocolTable model.Value I) :
    ProtocolFunction model.Value I definition.signature :=
  fun context self inputs =>
    (definition.body.denote
      (participantMeaningWithOn model observations actions helpers self protocols context)
      (maskValues self (context.mapScopes definition.inputScopes) inputs).get).bind fun results =>
        .done (maskValues self (context.mapScopes definition.outputScopes) results)

/-- The new closure captures only the immutable earlier protocol table. -/
def extendProtocolTableOn {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (helpers : Evaluation.ComponentTablesOn model.toCarriers I)
    (captured : ProtocolTable model.Value I)
    (definition : CheckedProtocol) : ProtocolTable model.Value I :=
  ⟨definition.signature, definition.denoteWithOn model observations actions helpers captured⟩ :: captured

/-- Each named helper captures its checked prefix. -/
def UnitPayload.tablesOn (payload : UnitPayload) : OpenTablesOn model.toCarriers :=
  payload.definitions.foldl
    (Evaluation.ComponentTablesOn.extend model (observedSitesOn model.toCarriers)) ⟨[], []⟩

/-- Every protocol closure captures its dependency prefix and the unqualified helpers. -/
def UnitPayload.protocolTableOn (payload : UnitPayload) :
    ProtocolTable model.Value (observedInterfaceOn model.toCarriers) :=
  payload.protocols.foldl
    (extendProtocolTableOn model (observedSitesOn model.toCarriers) observeActionOn
      (payload.tablesOn model)) []

/-- Plain closures over the same helper bodies, with silent sites. -/
def UnitPayload.plainProtocolTableOn (payload : UnitPayload) :
    ProtocolTable model.Value (participantInterfaceOn model.toCarriers) :=
  payload.protocols.foldl
    (extendProtocolTableOn model (.silent (participantInterfaceOn model.toCarriers))
      (participantActionsOn model.toCarriers)
      (payload.definitions.foldl
        (Evaluation.ComponentTablesOn.extend model (.silent (participantInterfaceOn model.toCarriers)))
          ⟨[], []⟩)) []

def Program.observedOn (program : Program)
    (self : Nat) (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    PIR.Proc (observedInterfaceOn model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs) :=
  invokeProtocol (program.payload.protocolTableOn model) program.payload.entry.signature {} self inputs

/-- A participant is selected by its index in this root's roster. -/
def Program.participantOn (program : Program)
    (self : Nat) (inputs : Values (Component model.Value) program.payload.entry.inputs) :
    PIR.Proc (participantInterfaceOn model.toCarriers)
      (Values (Component model.Value) program.payload.entry.outputs) :=
  (program.observedOn model self inputs).interpret forgetSitesOn

end Model

/-! The uniform participant semantics is the instance at the uniform model. -/

section Uniform
variable {F G : Type}

theorem participantInterface_eq_participantInterfaceOn :
    participantInterface F G = participantInterfaceOn (uniformCarriers F G) := by
  with_reducible rfl

theorem denoteRepeat_eq_denoteRepeatOn {I : PIR.Signature}
    (spec : RepeatSpec) (context : ProtocolContext) (self : Nat) (count : Option Nat)
    (state : Values (Component (assignment F G)) spec.state)
    (captures : Values (Component (assignment F G)) spec.captures)
    (body : RegionFunction (Component (assignment F G)) I
      (.index :: (spec.state ++ spec.captures), spec.state)) :
    denoteRepeat spec context self count state captures body =
      denoteRepeatOn (carriers := uniformCarriers F G) spec context self count state captures body := by
  unfold denoteRepeat denoteRepeatOn
  split
  · rcases count with _ | count <;> rfl
  · rfl

/-- The uniform site-observation interface read as the one over the uniform
carriers: the same marks and the same actions. -/
def observedToOn : PIR.OperationInterpretation (observedInterface F G)
    (observedInterfaceOn (uniformCarriers F G))
  | .mark site => .call (.mark site) .done
  | .action action => .call (.action action) .done

theorem observedSites_toOn :
    SiteObservations.Interprets observedToOn (observedSites F G) (observedSitesOn (uniformCarriers F G)) := by
  intro site
  rfl

theorem observeAction_toOn (action : (participantInterface F G).Op) :
    (observeAction action).interpret observedToOn = observeActionOn (carriers := uniformCarriers F G) action :=
  rfl

theorem observedToOn_forgetSitesOn (operation : (observedInterface F G).Op) :
    (observedToOn operation).interpret forgetSitesOn = forgetSites operation := by
  cases operation <;> rfl

variable [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem protocolOperationWith_eq_protocolOperationWithOn {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (self : Nat)
    (op : ProtocolOp) (args : Values (Component (assignment F G)) op.arguments)
    (callbacks : Values (RegionFunction (Component (assignment F G)) I) op.regions)
    (protocols : ProtocolTable (assignment F G) I) (context : ProtocolContext) :
    protocolOperationWith observations actions tables self op args callbacks protocols context =
      protocolOperationWithOn (ringModel F G) observations actions tables.toOn self op args callbacks
        protocols context := by
  cases op with
  | «repeat» spec site =>
    rcases args with _ | ⟨count, values⟩
    exact denoteRepeat_eq_denoteRepeatOn spec context self count _ _ _
  | calculate op allowed =>
    exact congrFun (congrFun (congrFun (Evaluation.componentOperation_eq_componentOperationOn
      observations tables) op) args) (op.calculationRegions allowed)
  | guard owner site =>
    rcases args with _ | ⟨condition, _ | _⟩
    rfl
  | exchange ty sender receiver site =>
    rcases args with _ | ⟨value, _ | _⟩
    rfl
  | restrict ty roles =>
    rcases args with _ | ⟨value, _ | _⟩
    rfl
  | mark site =>
    rcases args with _ | _
    rfl
  | _ => rfl

theorem denote_participantMeaningWith_eq {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (tables : Evaluation.ComponentTables F G I) (self : Nat)
    (protocols : ProtocolTable (assignment F G) I) (context : ProtocolContext)
    {Γ out : List Ty} (region : Region protocolDialect Γ out)
    (env : Environment (Component (assignment F G)) Γ) :
    region.denote (participantMeaningWith observations actions tables self protocols context) env =
      region.denote (participantMeaningWithOn (ringModel F G) observations actions tables.toOn self
        protocols context) env := by
  have same : (fun op args callbacks =>
      protocolOperationWith observations actions tables self op args callbacks protocols context) =
      (fun op args callbacks => protocolOperationWithOn (ringModel F G) observations actions tables.toOn
        self op args callbacks protocols context) := by
    funext op args callbacks
    exact protocolOperationWith_eq_protocolOperationWithOn observations actions tables self op args
      callbacks protocols context
  calc region.denote (participantMeaningWith observations actions tables self protocols context) env
      = region.denote ⟨Component (assignment F G), fun op args callbacks =>
          protocolOperationWith observations actions tables self op args callbacks protocols context⟩
          env := rfl
    _ = region.denote ⟨Component (assignment F G), fun op args callbacks =>
          protocolOperationWithOn (ringModel F G) observations actions tables.toOn self op args callbacks
            protocols context⟩ env := by rw [same]
    _ = _ := rfl

theorem CheckedProtocol.denoteWith_eq_denoteWithOn {I : PIR.Signature}
    (definition : CheckedProtocol) (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) (protocols : ProtocolTable (assignment F G) I) :
    definition.denoteWith observations actions helpers protocols =
      definition.denoteWithOn (ringModel F G) observations actions helpers.toOn protocols := by
  funext context self inputs
  unfold CheckedProtocol.denoteWith CheckedProtocol.denoteWithOn
  congr 1
  exact denote_participantMeaningWith_eq observations actions helpers self protocols context
    definition.body _

theorem extendProtocolTable_fold_eq {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterface F G) I)
    (helpers : Evaluation.ComponentTables F G I) :
    ∀ (definitions : List CheckedProtocol) (captured : ProtocolTable (assignment F G) I),
      definitions.foldl (extendProtocolTable observations actions helpers) captured =
        definitions.foldl (extendProtocolTableOn (ringModel F G) observations actions helpers.toOn)
          captured
  | [], _ => rfl
  | definition :: rest, captured => by
    simp only [List.foldl_cons]
    have step : extendProtocolTable observations actions helpers captured definition =
        extendProtocolTableOn (ringModel F G) observations actions helpers.toOn captured definition := by
      unfold extendProtocolTable extendProtocolTableOn
      rw [CheckedProtocol.denoteWith_eq_denoteWithOn]
    rw [step]
    exact extendProtocolTable_fold_eq observations actions helpers rest _

theorem UnitPayload.plainProtocolTable_eq_plainProtocolTableOn (payload : UnitPayload) :
    payload.plainProtocolTable F G = payload.plainProtocolTableOn (ringModel F G) := by
  unfold UnitPayload.plainProtocolTable UnitPayload.plainProtocolTableOn
  rw [extendProtocolTable_fold_eq, Evaluation.ComponentTables.fold_toOn]
  rfl

theorem UnitPayload.protocolTable_toOn (payload : UnitPayload) :
    ProtocolTable.Interprets observedToOn (payload.protocolTable F G)
      (payload.protocolTableOn (ringModel F G)) := by
  have interprets := ProtocolTable.fold_interpret (F := F) (G := G) observedToOn observedSites_toOn
    observeAction_toOn
    (Evaluation.ComponentTables.fold_interpret observedToOn observedSites_toOn (.empty _)
      payload.definitions) (ProtocolTable.Interprets.empty _) payload.protocols
  have right : payload.protocols.foldl
      (extendProtocolTable (F := F) (G := G) (observedSitesOn (uniformCarriers F G))
        (observeActionOn (carriers := uniformCarriers F G))
        (payload.definitions.foldl
          (Evaluation.ComponentTables.extend (observedSitesOn (uniformCarriers F G))) ⟨[], []⟩)) [] =
      payload.protocolTableOn (ringModel F G) := by
    rw [extendProtocolTable_fold_eq, Evaluation.ComponentTables.fold_toOn]
    rfl
  rw [right] at interprets
  exact interprets

theorem Program.observed_toOn (program : Program) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    (program.observed F G self inputs).interpret observedToOn =
      program.observedOn (ringModel F G) self inputs :=
  program.payload.protocolTable_toOn program.payload.entry.signature {} self inputs

/-- The uniform participant process is the generic one at the uniform model. -/
theorem Program.participant_eq_participantOn (program : Program) (self : Nat)
    (inputs : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G self inputs = program.participantOn (ringModel F G) self inputs := by
  unfold Program.participant Program.participantOn
  rw [← Program.observed_toOn, PIR.Proc.interpret_interchange observedToOn forgetSitesOn forgetSites
    observedToOn_forgetSitesOn]

end Uniform

end Zkc.Source.Structured
