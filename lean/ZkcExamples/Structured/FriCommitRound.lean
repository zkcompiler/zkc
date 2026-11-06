module

public import ZkcExamples.Structured.FriBinding
public import Zkc.Source.RegionSelection
public import Zkc.Source.Structured.MarkedPrefix
public meta import ZkcTools.StructuredSource.Bindings.CheckedCallback
public meta import ZkcExamples.Structured.FriSourceBodies

@[expose] public section

/-! In each installed Commit iteration the verifier must publish a layer
and append that very handle before requesting the field challenge. -/
set_option autoImplicit false
namespace ZkcExamples.Structured.FriCommitRound
open Zkc.Source Zkc.Source.Structured
open FriSource FriSourceBodies FriSourceViews FriBinding
open Zkc.Source.Structured.Bindings
open OracleProtocol (AtMarkedCall concrete)
attribute [local implicit_reducible] ProtocolOp.arguments ProtocolOp.results ProtocolOp.regions ServiceOp.contract

checked_callback round := protocol0Body at 0

abbrev kind := OracleKind.table (.field extension) none

structure State (model : DomainModel) where
  layers : List OracleAnchor
  folds : List OracleAnchor
  rows : Nat
  offset : model.Field extension
  generator : model.Field extension
  inverseTwo : model.Field extension
  service : Nat

def arguments (model : DomainModel) (step : Nat) (st : State model) :
    Values (Value model) (.index :: (roundSite.spec.state ++ roundSite.spec.captures)) :=
  .cons (concrete model .index step) (.cons none (.cons none
    (.cons (concrete model layersSort.type st.layers) (.cons (concrete model layersSort.type st.folds)
      (.cons (concrete model .index st.rows) (.cons (concrete model (.field extension) st.offset)
        (.cons (concrete model (.field extension) st.generator) (.cons (concrete model (.field extension) st.inverseTwo)
          (.cons (concrete model (.service FriScalarLoop.contract) st.service) .nil)))))))))

def iteration (model : DomainModel) (context : ProtocolContext) (step : Nat) (st : State model) :=
  roundBody.denote ((verifierAlgebra model).meaning (verifierTable model) context 1) (arguments model step st).get

def fieldDelivery : Region.OperationCut roundBody :=
  (Region.cutFirst (d := protocolDialect) (fun op ↦ match op with | .exchange .. => true | _ => false) roundBody).get (by kernel_rfl)

def virtualConstruction : Region.OperationCut fieldDelivery.next :=
  (Region.cutFirst (d := protocolDialect) (fun op ↦ match op with | .oracle (.virtual ..) _ => true | _ => false) fieldDelivery.next).get (by kernel_rfl)

set_option maxRecDepth 6000 in
checked_cut_prefix prepareView := virtualConstruction

/-- Factor the actual installed iteration before challenge delivery and
again before virtual construction. Each continuation takes exactly the SSA
values returned by the preceding source region, for every handler and stop. -/
theorem constructionPath (model : DomainModel) (context : ProtocolContext) (step : Nat) (st : State model) :
    let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
    iteration model context step st =
      (fieldDelivery.before.denote meaning (arguments model step st).get).bind fun atDelivery ↦
      (meaning.operation fieldDelivery.op (fieldDelivery.arguments.eval atDelivery.get)
        (fieldDelivery.callbacks.denote meaning)).bind fun reply ↦
      (virtualConstruction.before.denote meaning (Environment.prepend atDelivery.get reply)).bind fun atView ↦
      (Region.letOp virtualConstruction.op virtualConstruction.arguments virtualConstruction.callbacks
        virtualConstruction.next).denote meaning atView.get := by
  intro meaning
  refine (fieldDelivery.exactRun meaning _).trans ?_
  apply congrArg (PIR.Process.bind _)
  funext atDelivery
  rw [Region.denote]
  apply congrArg (PIR.Process.bind _)
  funext reply
  exact virtualConstruction.exactRun meaning _

def registrySites := roundBody.erase.operations.filterMap fun op ↦ match op with
  | .oracle (.send ..) site | .oracle (.sequenceAppend ..) site => some site
  | _ => none

def registrySite (index : Fin 3) := registrySites[index.val]'(by
  have count : registrySites.length = 3 := by kernel_rfl
  simpa only [count] using index.isLt)

def serviceSites := roundBody.erase.operations.filterMap fun op ↦ match op with
  | .draw _ _ site | .exchange _ _ _ site => some site
  | _ => none

def serviceSite (context : ProtocolContext) (index : Fin 2) :=
  qualifyProtocolSite context.applicationPrefix (serviceSites[index.val]'(by
    have count : serviceSites.length = 2 := by kernel_rfl
    simpa only [count] using index.isLt))

variable {model : DomainModel}

def sendRequest (context : ProtocolContext) (rows : Nat) : (OracleProtocol.Interface model).Op :=
  .oracle ⟨.send kind 0 [1] [("rows", 32)], registrySite 0, 1, context.roles,
    .cons none (.cons (concrete model .index rows) .nil)⟩

def appendRequest (context : ProtocolContext) (layers : List OracleAnchor) (anchor : OracleAnchor) :
    (OracleProtocol.Interface model).Op :=
  .oracle ⟨.sequenceAppend kind 3 [0, 1], registrySite 1, 1, context.roles,
    .cons (concrete model layersSort.type layers) (.cons (concrete model initialSort.type anchor) .nil)⟩

def drawRequest (context : ProtocolContext) (service : Nat) : (OracleProtocol.Interface model).Op :=
  .ordinary (.query (serviceSite context 0) (.draw extension) (.cons service .nil))

def delivery (context : ProtocolContext) (beta : model.Field extension) : (OracleProtocol.Interface model).Op :=
  .ordinary (.send (ty := .field extension) (serviceSite context 1) (context.roles 0) beta)

/-- Retain the publication and the draw in the live row at delivery. The
exchange returns the transmitted field to its sender; the receiver-only
projection belongs to the following source restriction. -/
def deliveredValues (step : Nat) (st : State model) (anchor : OracleAnchor) (beta : model.Field extension) :
    Values (Value model) (protocolDialect.results fieldDelivery.op ++ fieldDelivery.context) :=
  let scalar := concrete model (.field extension) beta
  let results : Values (Value model) [.field extension, .field extension, layersSort.type, initialSort.type, .vector extension] :=
    .cons scalar (.cons scalar (.cons (concrete model layersSort.type (st.layers ++ [anchor]))
      (.cons (concrete model initialSort.type anchor) (.cons none .nil))))
  results.append (arguments model step st)

def deliveredSuffix (context : ProtocolContext) (step : Nat) (st : State model)
    (anchor : OracleAnchor) (beta : model.Field extension) :=
  fieldDelivery.next.denote ((verifierAlgebra model).meaning (verifierTable model) context 1)
    (deliveredValues step st anchor beta).get

def beforeDraw (context : ProtocolContext) (step : Nat) (st : State model)
    (sent : (OracleProtocol.Interface model).Reply (sendRequest context st.rows) →
      PIR.Process (OracleProtocol.Interface model) (Values (Value model) roundSite.spec.state)) : Prop :=
  ∀ anchor, AtMarkedCall (appendRequest context st.layers anchor) (fun appended ↦
    AtMarkedCall (drawRequest context st.service) (fun sampled ↦ ∀ beta,
      AtMarkedCall (delivery context beta) (fun next ↦ next () = deliveredSuffix context step st anchor beta) (sampled beta))
      (appended (.cons (concrete model layersSort.type (st.layers ++ [anchor])) .nil)))
    (sent (.cons (concrete model initialSort.type anchor) .nil))

/-- After each possible successful publication, the actual receiver appends
its returned anchor. Only the appended sequence can lead to the draw. The
network receives exactly that draw's answer as the delivery payload. -/
theorem beforeChallenge (context : ProtocolContext) (receiver : context.roles 1 = 1)
    (step : Nat) (st : State model) :
    AtMarkedCall (sendRequest context st.rows) (beforeDraw context step st) (iteration model context step st) := by
  unfold iteration
  repeat' with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  intro anchor
  repeat' with_unfolding_all apply AtMarkedCall.mark
  with_unfolding_all apply AtMarkedCall.found
  repeat' with_unfolding_all apply AtMarkedCall.mark
  simp only [PIR.Process.bind]
  conv =>
    enter [3]
    rw [Region.denote.eq_def]
    dsimp only
    enter [1]
    change (((Participant.query (services := services) (Value := model.Value) 1 (context.roles 1)
      (serviceSite context 0) (.draw extension) (ProtocolValue.concreteComponents
        (.cons (concrete model (.service FriScalarLoop.contract) st.service) .nil))).interpret
        (OracleProtocol.actions model)).bind _)
    rw [show Values.cons (concrete model (.service FriScalarLoop.contract) st.service) .nil =
      ProtocolValue.embedComponents ((Values.cons (Value := model.Value) (ty := .service FriScalarLoop.contract)
        st.service .nil).present) from rfl, ProtocolValue.concreteComponents_embedComponents]
    simp [Participant.query, receiver, RoleFamily.sequence_present,
      PIR.Process.interpret, OracleProtocol.actions, PIR.Process.bind]
  with_unfolding_all apply AtMarkedCall.found
  intro beta
  repeat' with_unfolding_all apply AtMarkedCall.mark
  simp only [PIR.Process.bind]
  conv =>
    enter [3]
    rw [Region.denote.eq_def]
    dsimp only
    enter [1]
    change (OracleProtocol.exchange model context 1 1 0 (serviceSites[1]'(by decide +kernel))
      (concrete model (.field extension) beta)).bind _
    simp [OracleProtocol.exchange, receiver, OracleProtocol.concrete, ProtocolValue.materializeWith_ofConcrete,
      Participant.exchange, OracleProtocol.actions, PIR.Process.interpret, PIR.Process.bind]
  with_unfolding_all apply AtMarkedCall.found
  let meaning := (verifierAlgebra model).meaning (verifierTable model) context 1
  change fieldDelivery.next.denote meaning _ =
    fieldDelivery.next.denote meaning (deliveredValues step st anchor beta).get
  apply congrArg (fieldDelivery.next.denote meaning)
  funext ty ref
  change Var ([.field extension, .field extension, layersSort.type, initialSort.type, .vector extension] ++
    (.index :: (roundSite.spec.state ++ roundSite.spec.captures))) ty at ref
  cases ref with
  | here => rfl
  | there ref =>
    cases ref with
    | here => rfl
    | there ref =>
      cases ref with
      | here => rfl
      | there ref =>
        cases ref with
        | here => rfl
        | there ref =>
          cases ref <;> rfl

end ZkcExamples.Structured.FriCommitRound
