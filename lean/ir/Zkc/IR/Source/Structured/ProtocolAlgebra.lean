module

public import Zkc.IR.Source.Structured.DomainParticipant

@[expose] public section

/-! A value/effect parameter for the existing protocol Region semantics. Structural transport,
role masks, applications and repeats are shared. The ordinary instance below is proved equal
to the existing domain participant meaning, including optional operands and stopped processes. -/

set_option autoImplicit false
namespace Zkc.Source.Structured

structure ProtocolAlgebra (V : Ty → Type) (I : PIR.Signature) where
  index : Nat → V .index
  count : V .index → Option Nat
  action : (context : ProtocolContext) → (self : Nat) → (op : ProtocolOp) →
    Values (Component V) op.arguments → PIR.Process I (Values (Component V) op.results)
  application : {A : Type} → ProtocolContext → ProtocolSignature → String →
    PIR.Process I A → PIR.Process I A := fun _ _ _ p ↦ p
  iteration : {A : Type} → ProtocolContext → String → Nat →
    PIR.Process I A → PIR.Process I A := fun _ _ _ p ↦ p

namespace ProtocolAlgebra
variable {V : Ty → Type} {I : PIR.Signature}

def repeatProcess (algebra : ProtocolAlgebra V I) (spec : RepeatSpec)
    (context : ProtocolContext) (self : Nat) (site : String)
    (count : Component V .index) (state : Values (Component V) spec.state)
    (captures : Values (Component V) spec.captures)
    (body : RegionFunction (Component V) I (.index :: (spec.state ++ spec.captures), spec.state)) :
    PIR.Process I (Values (Component V) spec.state) :=
  if (spec.roles.map context.roles).contains self then
    match count.bind algebra.count with
    | none => .halt .incomplete
    | some count =>
      if count ≤ spec.maximum then
        let mask := maskValues self (context.mapScopes spec.stateScopes)
        Finite.execute (.elements (List.range count)) (fun state index ↦
          (algebra.iteration context site index
            (body (.cons (some (algebra.index index)) ((mask state).append captures)))).bind
              (fun results ↦ .done (mask results))) (mask state)
      else .halt .refused
  else .done (Values.absent V spec.state)

def operation (algebra : ProtocolAlgebra V I)
    (protocols : ProtocolTable V I) (context : ProtocolContext) (self : Nat)
    (op : ProtocolOp) (args : Values (Component V) op.arguments)
    (callbacks : Values (RegionFunction (Component V) I) op.regions) :
    PIR.Process I (Values (Component V) op.results) :=
  match op, args with
  | .repeat spec site, .cons count values =>
    let parts := Values.split spec.state values
    algebra.repeatProcess spec context self site count parts.1 parts.2 (callbacks.get .here)
  | .protocolApply signature roles site, args =>
    let child := context.enter site roles
    if child.contains signature self then
      algebra.application context signature site
        (invokeProtocol protocols signature child self args)
    else .done (Values.absent V signature.outputs)
  | .restrict _ roles, .cons value .nil =>
    .done (.cons (Participant.restrict ((roles.map context.roles).contains self) value) .nil)
  | .assemble _ roles, values =>
    .done (.cons (assembleComponent (fun role ↦ context.roles role == self) none roles values) .nil)
  | op, args => algebra.action context self op args

abbrev meaning (algebra : ProtocolAlgebra V I) (protocols : ProtocolTable V I)
    (context : ProtocolContext) (self : Nat) : RegionMeaning protocolDialect I where
  Value := Component V
  operation := algebra.operation protocols context self

def denote (algebra : ProtocolAlgebra V I) (definition : CheckedProtocol)
    (protocols : ProtocolTable V I) : ProtocolFunction V I definition.signature :=
  fun context self inputs ↦
    (definition.body.denote (algebra.meaning protocols context self)
      (maskValues self (context.mapScopes definition.inputScopes) inputs).get).bind fun results ↦
        .done (maskValues self (context.mapScopes definition.outputScopes) results)

def extend (algebra : ProtocolAlgebra V I) (captured : ProtocolTable V I)
    (definition : CheckedProtocol) : ProtocolTable V I :=
  ⟨definition.signature, algebra.denote definition captured⟩ :: captured

end ProtocolAlgebra

/-- The ordinary instance retains the exact existing closed/component evaluator and services.
The impossible callback tuple is empty at every atomic action of this algebra. -/
def ordinaryProtocolAlgebra (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I := .silent) : ProtocolAlgebra model.Value I where
  index := id
  count := some
  iteration := fun context site index p ↦
    iterations.within (qualifyProtocolSite context.applicationPrefix site) index p
  action context self op args :=
    if noRegions : op.regions = [] then
      protocolOperationWithOn model observations actions tables self op args
        (by rw [noRegions]; exact .nil) [] context iterations
    else .halt .refused

theorem ordinaryProtocolAlgebra_repeat (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I) (spec : RepeatSpec) (context : ProtocolContext)
    (self : Nat) (site : String) (count : Option Nat)
    (state : Values (Component model.Value) spec.state)
    (captures : Values (Component model.Value) spec.captures)
    (body : RegionFunction (Component model.Value) I
      (.index :: (spec.state ++ spec.captures), spec.state)) :
    (ordinaryProtocolAlgebra model observations actions tables iterations).repeatProcess
      spec context self site count state captures body =
        denoteRepeatOn spec context self count state captures body iterations site := by
  unfold ProtocolAlgebra.repeatProcess denoteRepeatOn
  split
  · cases count <;> rfl
  · rfl

/-- Exact ordinary specialization for every operation and arbitrary callbacks. In particular
this equation does not sequence all Math operands or assume nonempty result tuples. -/
theorem ordinaryProtocolAlgebra_operation (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I) (protocols : ProtocolTable model.Value I)
    (context : ProtocolContext) (self : Nat) (op : ProtocolOp)
    (args : Values (Component model.Value) op.arguments)
    (callbacks : Values (RegionFunction (Component model.Value) I) op.regions) :
    (ordinaryProtocolAlgebra model observations actions tables iterations).operation
      protocols context self op args callbacks =
        protocolOperationWithOn model observations actions tables self op args callbacks
          protocols context iterations := by
  cases op with
  | «repeat» spec site =>
    cases args with | cons count rest =>
      cases callbacks with | cons body tail =>
        cases tail
        exact ordinaryProtocolAlgebra_repeat model observations actions tables iterations
          spec context self site count (rest.split spec.state).1 (rest.split spec.state).2 body
  | _ =>
    cases callbacks
    first | rfl | (cases args; rfl) | (cases args; rename_i head tail; cases tail; rfl)

theorem ordinaryProtocolAlgebra_meaning (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I) (protocols : ProtocolTable model.Value I)
    (context : ProtocolContext) (self : Nat) :
    (ordinaryProtocolAlgebra model observations actions tables iterations).meaning
      protocols context self =
        participantMeaningWithOn model observations actions tables self protocols context iterations := by
  apply congrArg (fun operation ↦ (⟨Component model.Value, operation⟩ : RegionMeaning protocolDialect I))
  funext op args callbacks
  exact ordinaryProtocolAlgebra_operation model observations actions tables iterations
    protocols context self op args callbacks

theorem ordinaryProtocolAlgebra_denote (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I) (definition : CheckedProtocol)
    (protocols : ProtocolTable model.Value I) :
    (ordinaryProtocolAlgebra model observations actions tables iterations).denote definition protocols =
      definition.denoteWithOn model observations actions tables protocols iterations := by
  unfold ProtocolAlgebra.denote CheckedProtocol.denoteWithOn
  funext context self inputs
  dsimp only [CheckedProtocol.signature] at inputs ⊢
  have operations := funext fun op ↦ funext fun args ↦ funext fun callbacks ↦
    ordinaryProtocolAlgebra_operation model observations actions tables iterations
      protocols context self op args callbacks
  exact congrArg (fun operation ↦
    (definition.body.denote
      (⟨Component model.Value, operation⟩ : RegionMeaning protocolDialect I)
      (maskValues self (context.mapScopes definition.inputScopes) inputs).get).bind
        (fun results ↦ .done (maskValues self (context.mapScopes definition.outputScopes) results))) operations

/-- The complete immutable closure table specializes, not just individual atomic actions. -/
theorem ordinaryProtocolAlgebra_table (model : DomainModel) {I : PIR.Signature}
    (observations : SiteObservations I)
    (actions : PIR.OperationInterpretation (participantInterfaceOn model.toCarriers) I)
    (tables : Evaluation.ComponentTablesOn model.toCarriers I)
    (iterations : IterationObservations I) (definitions : List CheckedProtocol)
    (initial : ProtocolTable model.Value I) :
    definitions.foldl
      (ProtocolAlgebra.extend (ordinaryProtocolAlgebra model observations actions tables iterations)) initial =
    definitions.foldl
      (fun captured definition ↦ extendProtocolTableOn model observations actions tables captured definition iterations)
      initial := by
  have step : ProtocolAlgebra.extend (ordinaryProtocolAlgebra model observations actions tables iterations) =
      (fun captured definition ↦ extendProtocolTableOn model observations actions tables captured definition iterations) := by
    funext captured definition
    simp only [ProtocolAlgebra.extend, extendProtocolTableOn, ordinaryProtocolAlgebra_denote]
  rw [step]

end Zkc.Source.Structured
