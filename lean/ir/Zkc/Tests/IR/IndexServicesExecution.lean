module

public import Zkc.Tests.IR.IndexServices
public import Zkc.IR.Construction.DomainExecutionLaws

@[expose] public section

/-! Actual tiny constructed endpoints under an explicit deterministic service
control. This checks transport and failure behavior, not honest randomness or
cryptographic execution. Generic all-reply laws live in ServiceConnection. -/
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 4000000
namespace Tests.IndexServices.Execution
open Zkc.Source Zkc.Source.Structured Zkc.Construction

def fixedOracle (carriers : Carriers) : Domain.Oracle Id carriers Nat :=
  fun _ event state =>
    match event with
    | .challenge origin =>
      if scalar : origin.request = some (.sampleIndex 8) then
        (.returned (by simpa only [Domain.Raw, scalar] using
          (show Request.Raw carriers (.sampleIndex 8) from ⟨3, by decide⟩)), state + 1)
      else if block : origin.request = some (.sampleIndices 8 3) then
        (.returned (by simpa only [Domain.Raw, block] using
          (show Request.Raw carriers (.sampleIndices 8 3) from
            fun _ : Fin 3 => (⟨3, by decide⟩ : Fin 8))), state + 1)
      else (.stopped .refused, state + 1)
    | .message .. | .publicBinding .. => (.returned (), state)

def scalar (model : DomainModel) := Domain.produce model Scalar.program Scalar.context
  Scalar.Producer.participant [.transcript suite []] (fixedOracle model.toCarriers) 0

def block (model : DomainModel) := Domain.produce model Block.program Block.context
  Block.Producer.participant [.transcript suite []] (fixedOracle model.toCarriers) 0

example (model : DomainModel) : (scalar model).state.oracle = 1 := by kernel_rfl
example (model : DomainModel) : (block model).state.oracle = 1 := by kernel_rfl
example (model : DomainModel) : (scalar model).events.length = 2 := by kernel_rfl
example (model : DomainModel) : (block model).events.length = 2 := by kernel_rfl
example (model : DomainModel) : (scalar model).state.proof = [] := by kernel_rfl
example (model : DomainModel) : (block model).state.proof = [] := by kernel_rfl

def scalarPair (model : DomainModel) := Domain.executePair model Scalar.program Scalar.context
  Scalar.Producer.participant Scalar.Validator.participant [.transcript suite []] [.transcript suite []]
  (fixedOracle model.toCarriers) 0
def blockPair (model : DomainModel) := Domain.executePair model Block.program Block.context
  Block.Producer.participant Block.Validator.participant [.transcript suite []] [.transcript suite []]
  (fixedOracle model.toCarriers) 0

def returnedAcceptance {carriers : Carriers} (outcome : PIR.Outcome (Domain.Result carriers)) : Bool :=
  match outcome with
  | .returned result =>
      match (result.values[0]? : Option (Domain.Value carriers)) with
      | some (Domain.Value.data (Domain.Payload.boolean value)) => value
      | _ => false
  | .stopped _ => false

example (model : DomainModel) : (scalarPair model).validator.isSome = true := by kernel_rfl
example (model : DomainModel) : (blockPair model).validator.isSome = true := by kernel_rfl
example (model : DomainModel) :
    ((scalarPair model).validator.map fun execution => execution.state.oracle) = some 2 := by kernel_rfl
example (model : DomainModel) :
    ((blockPair model).validator.map fun execution => execution.state.oracle) = some 2 := by kernel_rfl
example (model : DomainModel) :
    ((scalarPair model).validator.map fun execution => returnedAcceptance execution.outcome) =
      some true := by kernel_rfl
example (model : DomainModel) :
    ((blockPair model).validator.map fun execution => returnedAcceptance execution.outcome) =
      some true := by kernel_rfl

/-- These are the existing admitted source participant and original effect
fold, with their real ABI. No source body is reimplemented in a test. -/
def scalarInputs (model : DomainModel) (handle : Option Nat) :
    Values (Component model.Value) Scalar.program.payload.entry.inputs :=
  Scalar.input_types.symm ▸ (.cons handle .nil : Values (Component model.Value) [.service contract])
def blockInputs (model : DomainModel) (handle : Option Nat) :
    Values (Component model.Value) Block.program.payload.entry.inputs :=
  Block.input_types.symm ▸ (.cons handle .nil : Values (Component model.Value) [.service contract])

def sourceScalarProducer (model : DomainModel) :=
  Domain.run .producer (fixedOracle model.toCarriers)
    (Original.participant model Scalar.program (Scalar.routing .producer) 0 (scalarInputs model none))
    ⟨[], [], 0⟩
def sourceScalarValidator (model : DomainModel) :=
  Domain.run .validator (fixedOracle model.toCarriers)
    (Original.participant model Scalar.program (Scalar.routing .validator) 1 (scalarInputs model (some 17)))
    ⟨[], [], 0⟩
def sourceBlockProducer (model : DomainModel) :=
  Domain.run .producer (fixedOracle model.toCarriers)
    (Original.participant model Block.program (Block.routing .producer) 0 (blockInputs model none))
    ⟨[], [], 0⟩

example (model : DomainModel) : (sourceScalarProducer model).events = (scalar model).events := by kernel_rfl
example (model : DomainModel) : (sourceScalarValidator model).events = (scalar model).events := by kernel_rfl
example (model : DomainModel) : (sourceBlockProducer model).events = (block model).events := by kernel_rfl
example (model : DomainModel) : (sourceScalarProducer model).state.oracle = 1 := by kernel_rfl
example (model : DomainModel) : (sourceBlockProducer model).state.oracle = 1 := by kernel_rfl

def receivedScalar (carriers : Carriers) := Domain.run .producer (fixedOracle carriers)
  (Original.receive (Scalar.routing .producer) {} .index "label_64656c6976657279_0" 1) ⟨[], [], 0⟩

example (carriers : Carriers) : (receivedScalar carriers).outcome =
    .returned (3, { frames := [], history :=
      [.challenge (Scalar.context.query "label_706f736974696f6e" (.sampleIndex 8)),
       .message (Scalar.context.message "label_64656c6976657279_0" 1 0) (.index 3)] }) := by kernel_rfl

-- The repeated scalar root makes three distinct query events; the three-entry
-- block root above still makes one. Occurrence coordinates stay in the events.
example (model : DomainModel) :
    (Domain.produce model Repeated.program Repeated.context Repeated.Producer.participant
      [.transcript suite []] (fixedOracle model.toCarriers) 0).state.oracle = 3 := by kernel_rfl
example (model : DomainModel) :
    (Domain.produce model Repeated.program Repeated.context Repeated.Producer.participant
      [.transcript suite []] (fixedOracle model.toCarriers) 0).events.length = 6 := by kernel_rfl

def failedOracle (carriers : Carriers) : Domain.Oracle Id carriers Nat :=
  fun _ _ state => (.stopped .reject, state + 1)

example (model : DomainModel) :
    (Domain.produce model Scalar.program Scalar.context Scalar.Producer.participant
      [.transcript suite []] (failedOracle model.toCarriers) 41).state.oracle = 42 := by kernel_rfl
example (model : DomainModel) :
    (Domain.produce model Scalar.program Scalar.context Scalar.Producer.participant
      [.transcript suite []] (failedOracle model.toCarriers) 41).events.length = 1 := by kernel_rfl
example (model : DomainModel) :
    (Domain.produce model Scalar.program Scalar.context Scalar.Producer.participant
      [.transcript suite []] (failedOracle model.toCarriers) 41).outcome = .stopped .reject := by kernel_rfl
example (model : DomainModel) :
    (Domain.executePair model Scalar.program Scalar.context Scalar.Producer.participant
      Scalar.Validator.participant [.transcript suite []] [.transcript suite []]
      (failedOracle model.toCarriers) 41).validator = none := by kernel_rfl

-- A wrong dynamic bound refuses before an oracle effect, even when its static
-- operation and source annotation claim the otherwise valid scalar request.
example (carriers : Carriers) :
    Domain.challengeRequest Scalar.context suite (.sampleIndex 8) Scalar.queryTemplate 0 2 [1]
      [.data .index, .transcript suite]
      ([.transcript suite [], .data (.index 7), .indices []] : Domain.Environment carriers) =
      .halt .refused := by kernel_rfl

end Tests.IndexServices.Execution
