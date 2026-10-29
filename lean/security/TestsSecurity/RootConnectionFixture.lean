module

public import TestsSecurity.SourceReading
public import ZkcSecurity.FiatShamir.RootConnectionEndpoint
public import ZkcTools.ConstructionBindings.Alignment
public import ZkcTools.ConstructionBindings.Inputs

@[expose] public section

/-! A complete consumer installation on the previously admitted Aggregate
source. The small constructed participant is a disclosed certified fixture,
not a native compiler export or a receipt of checkCompiled/route coverage.
The root is built from finite input, body and output certificates, rather than
assuming its semantic simulation. Every nominal model and received aggregate
is covered, with an arbitrary initial history and unread proof suffix.
-/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000
noncomputable section
namespace TestsSecurity.RootConnectionFixture
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Construction
open ConnectionFrame ConnectionInputs ConnectionRoot
open ZkcSecurity.FiatShamir
open TestsSecurity.SourceReading
attribute [local implicit_reducible] CheckedProtocol.signature

def artifact : Participant where
  source := Aggregate.snapshot.source
  candidate := "certified-aggregate-fixture"
  symbol := "validator"
  policy := ⟨"Aggregate", "P", "V", 0, "", [], [], [], "suite", "fixture"⟩
  inputs := [.transcript "suite"]
  outputs := [.data Aggregate.packet, .transcript "suite"]
  instructions := [
    ⟨.indicesEmpty, [], [.indices], []⟩,
    ⟨.receive "packet" "packet" "P" Aggregate.packet, [], [.data Aggregate.packet], []⟩,
    ⟨.observe "suite" Aggregate.message, [0, 2, 1], [.transcript "suite"], []⟩]
  returned := [2, 3]

def pattern : InputPattern Aggregate.definition.inputs := .cons .absent .nil
def layout : Layout pattern.scope := [.history "suite"]

def inputLayout : InputLayout Aggregate.definition.signature Aggregate.context 1 artifact.inputs where
  locations := [.absent]
  pattern := pattern
  shape := by derive_connection_inputs
  sorted := rfl
  visible := rfl
  layout := layout
  cells := by derive_connection_inputs
  length := rfl
  history := rfl

def outputLayout : ConnectionInstallation.ReturnLayout
    Aggregate.definition.signature Aggregate.context 1 artifact :=
  (ConnectionInstallation.ReturnLayout.build Aggregate.definition.signature Aggregate.context 1 artifact).toOption.get
    (by decide +kernel)

def target : ConnectionCertificate.Block := fun _ =>
  Domain.View.sequence (Domain.View.indicesEmpty [.indices]) <|
  Domain.View.sequence (Domain.View.receive "packet" "packet" "P" Aggregate.packet [.data Aggregate.packet]) <|
  Domain.View.sequence (Domain.View.observe Aggregate.context "suite" Aggregate.message 0 2 1
    [.transcript "suite"]) Domain.View.empty

def root : RootCertificate Aggregate.program (Aggregate.routing .validator) 1 artifact where
  snapshot := rfl
  roleValid := by decide
  distinct := RosterDistinct.root _ _
  inputs := inputLayout
  output := outputLayout
  target := target
  correspondence := fun _ => Domain.Correspondence.sequence
    (Domain.Correspondence.indicesEmpty [.indices])
    (Domain.Correspondence.sequence
      (Domain.Correspondence.receive "packet" "packet" "P" Aggregate.packet [.data Aggregate.packet])
      (Domain.Correspondence.sequence
        (Domain.Correspondence.observe "suite" Aggregate.message 0 2 1 [.transcript "suite"])
        Domain.Correspondence.empty))
  alignment := {
    self := rfl
    historyProfile := rfl
    form := (normalize {} Aggregate.definition.body 1 2 pattern).toOption.getD (.halt .refused)
    normalized := rfl
    alignment := by derive_connection_alignment }

/-- This fixture has an independently admitted actual source. -/
theorem source_admitted : check Aggregate.snapshot = .ok Aggregate.program := Aggregate.admitted

/-- Complete connection, automatic source reading and actual artifact coherence
are assembled from finite data. No semantic conclusion under test is assumed. -/
def installed (model : DomainModel) (physical : Domain.Environment model.toCarriers) :=
  RootConnection.publicBridge root _ rfl rfl model physical

theorem values (model : DomainModel) (physical : Domain.Environment model.toCarriers)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      m (Domain.Raw event)) (proof : Domain.Proof model.toCarriers) :
    (fun result => (Zkc.Transcript.mapOutcome (fun target => some target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution oracle
        (Domain.participant model Aggregate.program Aggregate.context artifact physical) proof =
    (fun result => (Zkc.Transcript.mapOutcome
      (ConnectionOutputSelection.encodedValues Aggregate.definition.signature Aggregate.context 1) result.1,
      result.2)) <$>
      Zkc.Transcript.transform NominalDomain.interface oracle
        (RootConnection.publicPresentation root model physical)
        (inputLayout.initial physical).history proof :=
  RootConnection.publicReadValues root _ rfl rfl model physical oracle proof

/-- The actual artifact receives arbitrary aggregates and appends exactly one
observation to the supplied history, retaining the entire unread suffix. -/
theorem artifact_readback (model : DomainModel) (value : model.Value Aggregate.packet)
    (history : Domain.History model.toCarriers) (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    (fun result => (Zkc.Transcript.mapOutcome (fun target => target.values) result.1, result.2)) <$>
      ZkcSecurity.Endpoint.Domain.readExecution oracle
        (Domain.participant model Aggregate.program Aggregate.context artifact [.transcript "suite" history])
        ((⟨Aggregate.packet, rfl, value⟩ : Domain.Payload model.toCarriers) :: suffix) =
      (.returned [.data ⟨Aggregate.packet, rfl, value⟩,
        .transcript "suite" (history ++ [.message Aggregate.origin ⟨Aggregate.packet, rfl, value⟩])],
        suffix) := by
  kernel_rfl

theorem actual_initial_history (model : DomainModel) (history : Domain.History model.toCarriers) :
    (root.inputs.initial [.transcript "suite" history]).history = history := rfl

/-- Malformed physical rows refuse before reading a proof or recording an event. -/
theorem malformed_input (model : DomainModel) (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model Aggregate.program Aggregate.context artifact []) suffix =
      (.stopped .refused, suffix) := by
  kernel_rfl

theorem wrong_history_suite (model : DomainModel) (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model Aggregate.program Aggregate.context artifact [.transcript "other" history])
      suffix = (.stopped .refused, suffix) := by
  kernel_rfl

theorem wrong_message_type (model : DomainModel) (history : Domain.History model.toCarriers)
    (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model Aggregate.program Aggregate.context artifact [.transcript "suite" history])
      (.boolean true :: suffix) = (.stopped .refused, .boolean true :: suffix) := by
  kernel_rfl

/-- Nominal aggregate constructors remain distinct even when their host
representations agree. A failed decode leaves the whole proof head unread. -/
def otherPacket : Ty := .sequence (.product "source-reading-record" "other"
  (.cons .boolean (.cons (.field "bls12-381.fr") .nil)))
theorem wrong_nominal_message (model : DomainModel) (value : model.Value otherPacket)
    (history : Domain.History model.toCarriers) (suffix : Domain.Proof model.toCarriers)
    (oracle : Domain.History model.toCarriers → (event : Domain.Event model.toCarriers) →
      Id (Domain.Raw event)) :
    ZkcSecurity.Endpoint.Domain.readExecution oracle
      (Domain.participant model Aggregate.program Aggregate.context artifact [.transcript "suite" history])
      ((⟨otherPacket, rfl, value⟩ : Domain.Payload model.toCarriers) :: suffix) =
      (.stopped .refused, (⟨otherPacket, rfl, value⟩ : Domain.Payload model.toCarriers) :: suffix) := by
  kernel_rfl

theorem malformed_source (model : DomainModel) : root.source model [] = .halt .refused := by
  kernel_rfl

#print axioms root
#print axioms installed
#print axioms values
#print axioms artifact_readback

end TestsSecurity.RootConnectionFixture
