module

public import Zkc.Source.Structured.ProtocolEmbeddingMath
public import Zkc.Source.Structured.OracleProtocol
public import Zkc.Source.Structured.DomainParticipantInterpretation

@[expose] public section

/-! Ordinary-source specialization of the actual Oracle protocol algebra. Only internal
invocation/iteration/mark bookkeeping is erased. Logical requests and data demands are
retained by erasure, so this theorem cannot hide an Oracle action behind ordinary refusal. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Zkc.Source.Structured.ProtocolEmbedding
open Zkc.Source

/-- Retain every public and logical request, with its original reply type and value. -/
def eraseInternal (carriers : Carriers) :
    PIR.OperationInterpretation (oracleProtocolInterface carriers)
      (oracleProtocolInterface carriers)
  | .ordinary action => .call (.ordinary action) .done
  | .oracle request => .call (.oracle request) .done
  | .demand request => .call (.demand request) .done
  | .application .. | .iteration .. | .leave | .mark .. => .done ()

@[simp] theorem erase_actions (model : DomainModel)
    (action : (participantInterfaceOn model.toCarriers).Op) :
    (OracleProtocol.actions model action).interpret (eraseInternal model.toCarriers) =
      OracleProtocol.actions model action := rfl

theorem erase_enter_application (model : DomainModel) {A : Type}
    (signature : ProtocolSignature) (site : String)
    (process : PIR.Process (OracleProtocol.Interface model) A) :
    (OracleProtocol.enter model (.application signature site) process).interpret
      (eraseInternal model.toCarriers) = process.interpret (eraseInternal model.toCarriers) := by
  simp only [OracleProtocol.enter, PIR.Process.interpret_bind, PIR.Process.interpret,
    eraseInternal, PIR.Process.bind, PIR.Process.bind_done]

theorem erase_enter_iteration (model : DomainModel) {A : Type} (site : String) (index : Nat)
    (process : PIR.Process (OracleProtocol.Interface model) A) :
    (OracleProtocol.enter model (.iteration site index) process).interpret
      (eraseInternal model.toCarriers) = process.interpret (eraseInternal model.toCarriers) := by
  simp only [OracleProtocol.enter, PIR.Process.interpret_bind, PIR.Process.interpret,
    eraseInternal, PIR.Process.bind, PIR.Process.bind_done]

/-- A syntactic ordinary fragment of the exact retained body. -/
def OrdinaryOperation : ProtocolOp → Prop
  | .oracle .. => False
  | _ => True

@[simp] theorem mask_embed {carriers : Carriers} {ts : List Ty} (self : Nat)
    (scopes : List (List Nat)) (values : Values (Component carriers.Value) ts) :
    maskValues self scopes (ProtocolValue.embedComponents values) =
      ProtocolValue.embedComponents (maskValues self scopes values) := by
  induction values generalizing scopes with
  | nil => rfl
  | cons value rest ih =>
    simp only [maskValues, ProtocolValue.embedComponents, ih]
    unfold Participant.restrict
    split <;> rfl

@[simp] theorem assemble_embed {carriers : Carriers} {t : Ty}
    (selected : Nat → Bool) (roles : List Nat)
    (values : Values (Component carriers.Value) (roles.map (fun _ ↦ t))) :
    assembleComponent selected none roles (ProtocolValue.embedComponents values) =
      component t (assembleComponent selected none roles values) := by
  induction roles with
  | nil => cases values; rfl
  | cons role roles ih => cases values with
    | cons value rest =>
      simp only [assembleComponent, ProtocolValue.embedComponents]
      split <;> first | rfl | exact ih rest

/-- The full ordinary table is fixed by its actual source fold and silent observations. -/
def ordinaryTables (payload : UnitPayload) (model : DomainModel) :
    Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model) :=
  payload.definitions.foldl (Evaluation.ComponentTablesOn.extend model (.silent _)) ⟨[], []⟩

theorem ordinary_tables_erase (payload : UnitPayload) (model : DomainModel) :
    Evaluation.ComponentTablesOn.Interprets (eraseInternal model.toCarriers)
      (ordinaryTables payload model) (ordinaryTables payload model) :=
  Evaluation.ComponentTablesOn.fold_interpret _ (SiteObservations.silent_interpret _)
    (.empty _) payload.definitions

/-- Every Math condition is checked against the payload's actual stored body. -/
def MathFragment (definitions : List CheckedDefinition) : Prop :=
  ∀ definition ∈ definitions, definition.kind = .math → Fragment MathOperation definition.body

theorem payload_math_related (payload : UnitPayload) (model : DomainModel) (self : Nat)
    (fragment : MathFragment payload.definitions) :
    MathTablesRelated model (ordinaryTables payload model)
      (payload.oracleCalculations model self) :=
  math_tables_fold model (OracleProtocol.demand model) self (ordinaryTables payload model)
    ⟨[], []⟩ [] (fun _ _ _ ↦ rfl) Evaluation.ComponentTablesOn.adequate_empty
    payload.definitions fragment

/-- Protocol lookup relation includes all contexts, optional inputs and failed lookups. -/
def ProtocolTablesRelated (model : DomainModel) (self : Nat)
    (ordinary : ProtocolTable model.Value (OracleProtocol.Interface model))
    (lazy : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model)) :
    Prop :=
  ∀ signature context args,
    (invokeProtocol lazy signature context self (ProtocolValue.embedComponents args)).interpret
      (eraseInternal model.toCarriers) =
      (invokeProtocol ordinary signature context self args).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result))

/-- Erasure preserves arbitrary typed replies of the original participant interface. -/
theorem erase_ordinary (model : DomainModel) {A : Type}
    (process : PIR.Process (participantInterfaceOn model.toCarriers) A) :
    (process.interpret (OracleProtocol.actions model)).interpret (eraseInternal model.toCarriers) =
      process.interpret (OracleProtocol.actions model) :=
  PIR.Process.interpret_interchange _ _ _ (erase_actions model) process

theorem owned_embed (model : DomainModel) (self owner : Nat)
    (tables : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (stable : Evaluation.ComponentTablesOn.Interprets
      (eraseInternal model.toCarriers) tables tables)
    (helper : Helper) (args : Values (Component model.Value) helper.inputs) :
    (OracleProtocol.owned model self owner tables helper
      (ProtocolValue.embedComponents args)).interpret
      (eraseInternal model.toCarriers) =
      (Participant.owned self owner (invoke tables.closed helper) args).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  unfold OracleProtocol.owned
  simp only [sequence_embed]
  split
  · cases sequenced : RoleFamily.sequence args with
    | none => simp only [Option.map_none, Participant.owned, *, ↓reduceIte,
        PIR.Process.interpret, PIR.Process.bind]
    | some values =>
      simp only [Option.map_some, ProtocolValue.materializeComponents_embedComponents,
        PIR.Process.bind, PIR.Process.interpret_bind, PIR.Process.interpret]
      rw [Participant.owned_interpret _ self owner _ _ (stable.closed helper)]
  · simp only [PIR.Process.interpret, Participant.owned, * , ↓reduceIte,
      PIR.Process.bind, embed_absent]

theorem exchange_embed (model : DomainModel) (context : ProtocolContext)
    (self sender receiver : Nat) (site : String) {t : Ty} (value : Component model.Value t) :
    (OracleProtocol.exchange model context self sender receiver site
      (component t value)).interpret (eraseInternal model.toCarriers) =
      ((Participant.exchange (services := services) self (context.roles sender)
        (context.roles receiver) (qualifyProtocolSite context.applicationPrefix site)
        value).interpret
          (OracleProtocol.actions model)).bind (fun result ↦ .done (component t result)) := by
  unfold OracleProtocol.exchange
  split
  · cases value with
    | none => simp only [component, Option.map_none, Participant.exchange, *, ↓reduceIte,
        PIR.Process.interpret, PIR.Process.bind]
    | some value =>
      simp only [component, Option.map_some, ProtocolValue.materializeWith_ofConcrete,
        PIR.Process.bind, PIR.Process.interpret_bind, erase_ordinary, PIR.Process.interpret]
  · simp only [PIR.Process.interpret_bind, erase_ordinary, PIR.Process.interpret, component]
    congr 1
    unfold Participant.exchange
    simp only [*, ↓reduceIte]

theorem repeat_embed (model : DomainModel) (self : Nat)
    (ordinary : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))
    (spec : RepeatSpec) (context : ProtocolContext) (site : String)
    (count : Option Nat) (state : Values (Component model.Value) spec.state)
    (captures : Values (Component model.Value) spec.captures)
    (left : RegionFunction (Component model.Value) (OracleProtocol.Interface model)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (right : RegionFunction (Component (ProtocolValue model.toCarriers))
      (OracleProtocol.Interface model)
      (.index :: (spec.state ++ spec.captures), spec.state))
    (callback : ∀ args, (right (ProtocolValue.embedComponents args)).interpret
      (eraseInternal model.toCarriers) =
        (left args).bind (fun result ↦ .done (ProtocolValue.embedComponents result))) :
    ((OracleProtocol.algebra model self ordinary helpers).repeatProcess spec context self site
      (component .index count) (ProtocolValue.embedComponents state)
      (ProtocolValue.embedComponents captures) right).interpret (eraseInternal model.toCarriers) =
      (denoteRepeatOn spec context self count state captures left .silent site).bind
        (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  unfold ProtocolAlgebra.repeatProcess denoteRepeatOn
  dsimp only [OracleProtocol.algebra]
  rw [component_toConcrete]
  split
  · cases count with
    | none => rfl
    | some count =>
      dsimp only
      split
      · simp only [Finite.interpret_execute, PIR.Process.interpret_bind,
          erase_enter_iteration, PIR.Process.interpret, mask_embed]
        change Finite.fold _ (List.range count) (ProtocolValue.embedComponents
          (maskValues self (context.mapScopes spec.stateScopes) state)) = _
        apply fold_naturality ProtocolValue.embedComponents
        intro state index
        simp only [Repeat.stepOn, IterationObservations.silent_within,
          ← embed_append, ← mask_embed]
        have equation := callback (.cons (some index)
          ((maskValues self (context.mapScopes spec.stateScopes) state).append captures))
        simp only [ProtocolValue.embedComponents, Option.map_some,
          embed_append, ← mask_embed] at equation
        rw [equation]
        simp only [PIR.Process.bind_assoc, PIR.Process.bind, mask_embed]
      · rfl
  · simp only [PIR.Process.interpret, PIR.Process.bind, embed_absent]

/-- All action cases are supplied for the actual lazy instance. Callback equality is
all-input and includes stops, not a completeness or honesty postcondition. -/
theorem operation_embed (model : DomainModel) (self : Nat)
    (tables : Evaluation.ComponentTablesOn model.toCarriers (OracleProtocol.Interface model))
    (adequate : tables.Adequate)
    (stable : Evaluation.ComponentTablesOn.Interprets
      (eraseInternal model.toCarriers) tables tables)
    (helpers : ProtocolCalculation.Tables model.toCarriers (OracleProtocol.Interface model))
    (math : MathTablesRelated model tables helpers)
    (ordinary : ProtocolTable model.Value (OracleProtocol.Interface model))
    (lazy : ProtocolTable (ProtocolValue model.toCarriers) (OracleProtocol.Interface model))
    (related : ProtocolTablesRelated model self ordinary lazy) (context : ProtocolContext)
    (op : ProtocolOp) (allowed : OrdinaryOperation op)
    (args : Values (Component model.Value) op.arguments)
    (left : Values (RegionFunction (Component model.Value) (OracleProtocol.Interface model))
      op.regions)
    (right : Values (RegionFunction (Component (ProtocolValue model.toCarriers))
      (OracleProtocol.Interface model)) op.regions)
    (callbacks : CallbacksCommute (d := protocolDialect) component
      (eraseInternal model.toCarriers) left right) :
    ((OracleProtocol.algebra model self tables helpers).operation lazy context self op
      (ProtocolValue.embedComponents args) right).interpret (eraseInternal model.toCarriers) =
      (protocolOperationWithOn model (.silent _) (OracleProtocol.actions model) tables self
        op args left ordinary context .silent).bind
          (fun result ↦ .done (ProtocolValue.embedComponents result)) := by
  cases op with
  | oracle => cases allowed
  | «repeat» spec site =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases args with | cons count rest =>
      cases left with | cons body tail =>
        cases tail
        cases right with | cons lazyBody tail =>
          cases tail
          change ((OracleProtocol.algebra model self tables helpers).repeatProcess spec context self
            site (component .index count) ((ProtocolValue.embedComponents rest).split spec.state).1
              ((ProtocolValue.embedComponents rest).split spec.state).2 lazyBody).interpret _ = _
          rw [embed_split]
          exact repeat_embed model self tables helpers spec context site count _ _ body lazyBody
            (fun args ↦ by simpa only [map_components, Values.get] using callbacks .here args)
  | protocolApply signature roles site =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    change (if (context.enter site roles).contains signature self then
      OracleProtocol.enter model (.application signature site)
        (invokeProtocol lazy signature (context.enter site roles) self
          (ProtocolValue.embedComponents args))
      else .done (Values.absent (ProtocolValue model.toCarriers) signature.outputs)).interpret _ = _
    split
    · rw [erase_enter_application]
      simpa only [protocolOperationWithOn, *, ↓reduceIte] using
        related signature (context.enter site roles) args
    · simp only [PIR.Process.interpret, protocolOperationWithOn, *, ↓reduceIte,
        Bool.false_eq_true, PIR.Process.bind, embed_absent]
  | calculate op calculation =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    change (ProtocolCalculation.operation model (OracleProtocol.demand model) self tables helpers op
      (ProtocolValue.embedComponents args)).interpret _ = _
    rw [calculation_embed model (OracleProtocol.demand model) self tables tables helpers
      math adequate
      op calculation args (op.calculationRegions calculation)]
    simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
    have equation := Evaluation.componentOperationOn_interpret (eraseInternal model.toCarriers)
      (SiteObservations.silent_interpret _) stable op args (op.calculationRegions calculation)
    rw [Op.calculationRegions_translate] at equation
    rw [equation]
    rfl
  | localCall helper kind owner site =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    exact owned_embed model self (context.roles owner) tables stable helper args
  | guard owner site =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    cases args with | cons condition rest =>
      cases rest
      change (((Participant.guard (services := services) (Value := model.Value) self
        (context.roles owner) ((condition.map (ProtocolValue.ofConcrete .boolean)).bind
          ProtocolValue.toConcrete)).interpret (OracleProtocol.actions model)).bind
            (fun _ ↦ .done Values.nil)).interpret _ =
        (((Participant.guard (services := services) (Value := model.Value) self
          (context.roles owner) condition).interpret (OracleProtocol.actions model)).bind
          (fun _ ↦ .done (Values.nil : Values (Component model.Value) []))).bind
            (fun result ↦ .done (ProtocolValue.embedComponents result))
      rw [component_toConcrete]
      simp only [PIR.Process.interpret_bind, erase_ordinary, PIR.Process.interpret,
        protocolOperationWithOn, PIR.Process.bind_assoc, PIR.Process.bind,
        ProtocolValue.embedComponents]
  | exchange t sender receiver site =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    cases args with | cons value rest =>
      cases rest
      change ((OracleProtocol.exchange model context self sender receiver site
        (component t value)).bind
        (fun result ↦ .done (Values.cons result Values.nil))).interpret _ =
        (((Participant.exchange (services := services) self (context.roles sender)
          (context.roles receiver) (qualifyProtocolSite context.applicationPrefix site)
          value).interpret (OracleProtocol.actions model)).bind
          (fun result ↦ .done (Values.cons result Values.nil :
            Values (Component model.Value) [t]))).bind
              (fun result ↦ .done (ProtocolValue.embedComponents result))
      simp only [PIR.Process.interpret_bind, exchange_embed, PIR.Process.interpret,
        protocolOperationWithOn, PIR.Process.bind_assoc, PIR.Process.bind,
        ProtocolValue.embedComponents, component]
  | restrict t roles =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    cases args with | cons value rest =>
      cases rest
      change PIR.Process.done (Values.cons
        (Value := Component (ProtocolValue model.toCarriers))
        (Participant.restrict ((roles.map context.roles).contains self) (component t value)) .nil) =
          PIR.Process.done (ProtocolValue.embedComponents (Values.cons
            (Participant.restrict ((roles.map context.roles).contains self) value) .nil))
      unfold Participant.restrict
      split <;> rfl
  | assemble t roles =>
    dsimp only [ProtocolOp.arguments, ProtocolOp.results,
      ProtocolOp.regions] at args left right callbacks ⊢
    cases left
    cases right
    change PIR.Process.done (Values.cons
      (Value := Component (ProtocolValue model.toCarriers))
      (assembleComponent _ none roles (ProtocolValue.embedComponents args)) .nil) = _
    rw [assemble_embed]
    rfl
  | query owner service site =>
    cases left
    cases right
    change PIR.Process.interpret (eraseInternal model.toCarriers)
      ((((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) service
        (ProtocolValue.concreteComponents (ProtocolValue.embedComponents args))).interpret
          serviceAction).interpret (OracleProtocol.actions model)).bind
        (fun result ↦ .done (Values.cons
          (Value := Component (ProtocolValue model.toCarriers))
          (result.map (ProtocolValue.ofConcrete service.result)) .nil))) =
      ((((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) service args).interpret
          serviceAction).interpret (OracleProtocol.actions model)).bind
        (fun result ↦ .done (Values.cons result .nil :
          Values (Component model.Value) [service.result]))).bind
            (fun result ↦ .done (ProtocolValue.embedComponents result))
    erw [ProtocolValue.concreteComponents_embedComponents]
    simp only [PIR.Process.interpret_bind, erase_ordinary, PIR.Process.interpret,
      PIR.Process.bind_assoc, PIR.Process.bind, ProtocolValue.embedComponents]
  | draw owner field site =>
    cases left
    cases right
    change PIR.Process.interpret (eraseInternal model.toCarriers)
      (((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) (.draw field)
        (ProtocolValue.concreteComponents (ProtocolValue.embedComponents args))).interpret
          (OracleProtocol.actions model)).bind
        (fun result ↦ .done (Values.cons
          (Value := Component (ProtocolValue model.toCarriers))
          (result.map (ProtocolValue.ofConcrete (.field field))) .nil))) =
      (((Participant.query (services := services) self (context.roles owner)
        (qualifyProtocolSite context.applicationPrefix site) (.draw field) args).interpret
          (OracleProtocol.actions model)).bind
        (fun result ↦ .done (Values.cons result .nil :
          Values (Component model.Value) [.field field]))).bind
            (fun result ↦ .done (ProtocolValue.embedComponents result))
    erw [ProtocolValue.concreteComponents_embedComponents]
    simp only [PIR.Process.interpret_bind, erase_ordinary, PIR.Process.interpret,
      PIR.Process.bind_assoc, PIR.Process.bind, ProtocolValue.embedComponents]
  | statement => cases left; cases right; rfl
  | mark site => cases left; cases right; cases args; rfl

end Zkc.Source.Structured.ProtocolEmbedding
