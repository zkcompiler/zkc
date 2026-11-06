module

public import TestsSecurity.TypedSourceReading

@[expose] public section

/-! Run the actual nominal transcript transform on retained source Processes.
The deterministic provider records full query keys; it is only a control, not
an honest sampler. Both source roles use the existing Original fold/read law. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace TestsSecurity.TypedSourceExecution
open PIR Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Transcript
open ZkcSecurity.FiatShamir Tests.IndexServices

/-- An inhabitant of each exact reply sort; the field's own model zero is used. -/
def zeroReply (model : DomainModel) : (event : Domain.Event model.toCarriers) → Domain.Raw event
  | .challenge ⟨_, _, none⟩ => ()
  | .challenge ⟨_, _, some request⟩ => by
    rcases request with ⟨method, operands, sort⟩
    cases sort <;> try exact ()
    case field => exact 0
    case index => exact ⟨0, Request.replyBound_positive _⟩
    case indices => exact fun _ => ⟨0, Request.replyBound_positive _⟩
  | .message .. | .publicBinding .. => ()

def loggedQuery (model : DomainModel) (history : Domain.History model.toCarriers)
    (event : Domain.Event model.toCarriers) :
    StateM (List (Domain.History model.toCarriers)) (Domain.Raw event) :=
  fun log => (zeroReply model event, log ++ [history ++ [event]])

def role : Domain.Mode → Nat | .producer => 0 | .validator => 1
def handle : Domain.Mode → Option Nat | .producer => none | .validator => some 17

def scalar (model : DomainModel) (mode : Domain.Mode) :=
  (transform NominalDomain.interface (loggedQuery model)
    (DomainSourceReading.presentation (Scalar.routing mode)
      (Occurrence.participant model Scalar.program (role mode) (Execution.scalarInputs model (handle mode))) {})
    [] []).run []

def block (model : DomainModel) (mode : Domain.Mode) :=
  (transform NominalDomain.interface (loggedQuery model)
    (DomainSourceReading.presentation (Block.routing mode)
      (Occurrence.participant model Block.program (role mode) (Execution.blockInputs model (handle mode))) {})
    [] []).run []

def finalHistory {A : Type} {carriers : Carriers}
    (outcome : PIR.Outcome (A × Original.State carriers)) : Option (Domain.History carriers) :=
  match outcome with
  | .stopped _ => none
  | .returned (_, state) => some state.history

def finalFrames {A : Type} {carriers : Carriers}
    (outcome : PIR.Outcome (A × Original.State carriers)) : Option Original.Frames :=
  match outcome with
  | .stopped _ => none
  | .returned (_, state) => some state.frames

-- Scalar queries precede their original delivery, under either endpoint role.
example (model : DomainModel) : (scalar model .producer).2 =
    [[.challenge (Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8))]] := by kernel_rfl
example (model : DomainModel) : (scalar model .validator).2 = (scalar model .producer).2 := by kernel_rfl
example (model : DomainModel) : finalHistory (scalar model .producer).1.1 = some
    [.challenge (Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8)),
     .message (Scalar.context.message "label_64656c6976657279_0" 1 0) (.index 0)] := by kernel_rfl
example (model : DomainModel) : finalHistory (scalar model .validator).1.1 =
    finalHistory (scalar model .producer).1.1 := by kernel_rfl

-- A count-three block remains one query and one ordered-list delivery.
example (model : DomainModel) : (block model .producer).2 =
    [[.challenge (Block.context.query "label_706f736974696f6e73" (.sampleIndices 8 3))]] := by kernel_rfl
example (model : DomainModel) : (block model .validator).2 = (block model .producer).2 := by kernel_rfl
example (model : DomainModel) : finalHistory (block model .producer).1.1 = some
    [.challenge (Block.context.query "label_706f736974696f6e73" (.sampleIndices 8 3)),
     .message (Block.context.message "label_64656c6976657279_0" 1 0)
       ⟨.indices, rfl, [0, 0, 0]⟩] := by kernel_rfl
example (model : DomainModel) : finalHistory (block model .validator).1.1 =
    finalHistory (block model .producer).1.1 := by kernel_rfl
example (model : DomainModel) : finalFrames (block model .producer).1.1 = some [] := by kernel_rfl
example (model : DomainModel) : (block model .validator).1.2 = [] := by kernel_rfl

def repeatedInputs (model : DomainModel) :
    Values (Component model.Value) Repeated.program.payload.entry.inputs :=
  (show Repeated.program.payload.entry.inputs = [.service contract] by kernel_rfl).symm ▸
    (.cons (some 17) .nil : Values (Component model.Value) [.service contract])
def repeatedMessage : Template := ⟨Repeated.Source.snapshot.entry,
  [.repeat Repeated.Source.snapshot.entry "s4"],
  ["message", Repeated.Source.snapshot.entry, "label_64656c6976657279_0", "label_64656c6976657279_0",
    "role00000001", "role00000000"]⟩
def repeatedRouting : Original.Routing :=
  { Repeated.routing with messages := [repeatedMessage] }
def repeated (model : DomainModel) :=
  (transform NominalDomain.interface (loggedQuery model)
    (DomainSourceReading.presentation repeatedRouting
      (Occurrence.participant model Repeated.program 1 (repeatedInputs model)) {}) [] []).run []

-- Provider failure retains the attempted key and prevents message/suffix effects.
def stoppedQuery (model : DomainModel) (history : Domain.History model.toCarriers)
    (event : Domain.Event model.toCarriers) :
    ExceptT PIR.Stop (StateM (List (Domain.History model.toCarriers))) (Domain.Raw event) :=
  ExceptT.mk fun log => (.error .reject, log ++ [history ++ [event]])
def stoppedScalar (model : DomainModel) :=
  ((transform NominalDomain.interface (stoppedQuery model)
    (DomainSourceReading.presentation (Scalar.routing .producer)
      (Occurrence.participant model Scalar.program 0 (Execution.scalarInputs model none)) {}) [] []).run).run []

example (model : DomainModel) : (stoppedScalar model).1 = .error .reject := by kernel_rfl
example (model : DomainModel) : (stoppedScalar model).2 =
    [[.challenge (Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8))]] := by kernel_rfl

-- The actual source fold's handler independently retains the failure post-state.
example (model : DomainModel) :
    (Domain.run .producer (Execution.failedOracle model.toCarriers)
      (Original.participant model Scalar.program (Scalar.routing .producer) 0
        (Execution.scalarInputs model none)) ⟨[], [], 41⟩).events =
    [.challenge (Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8))] := by kernel_rfl
example (model : DomainModel) :
    (Domain.run .producer (Execution.failedOracle model.toCarriers)
      (Original.participant model Scalar.program (Scalar.routing .producer) 0
        (Execution.scalarInputs model none)) ⟨[], [], 41⟩).state.oracle = 42 := by kernel_rfl

/-- The existing constructed endpoints use the identical dependent replies. -/
def provider (model : DomainModel) : Domain.Oracle Id model.toCarriers Nat :=
  fun _ event state => (.returned (zeroReply model event), state + 1)
def scalarPair (model : DomainModel) :=
  Domain.executePair model Scalar.program Scalar.context
    Scalar.Producer.participant Scalar.Validator.participant
    [.transcript suite []] [.transcript suite []] (provider model) 0
def blockPair (model : DomainModel) :=
  Domain.executePair model Block.program Block.context
    Block.Producer.participant Block.Validator.participant
    [.transcript suite []] [.transcript suite []] (provider model) 0

example (model : DomainModel) :
    finalHistory (scalar model .producer).1.1 = some (scalarPair model).producer.events := by kernel_rfl
example (model : DomainModel) :
    finalHistory (block model .producer).1.1 = some (blockPair model).producer.events := by kernel_rfl
example (model : DomainModel) :
    ((scalarPair model).validator.map fun execution => Execution.returnedAcceptance execution.outcome) =
      some true := by kernel_rfl
example (model : DomainModel) :
    ((blockPair model).validator.map fun execution => Execution.returnedAcceptance execution.outcome) =
      some true := by kernel_rfl

end TestsSecurity.TypedSourceExecution
