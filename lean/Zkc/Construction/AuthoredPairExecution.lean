module

public import Zkc.Construction.AuthoredPair
public import Zkc.Construction.DomainProducer

@[expose] public section

/-! The actual compiled producer, followed by the actual compiled validator.
The same oracle is used with the producer's final oracle state. Both initial
transcripts are the request's public binding history; the producer's final
transcript, environment and observations remain in the result. This operational
experiment carries no probability, oracle coherence or completeness assumption.
-/
set_option autoImplicit false
namespace Zkc.Construction.AuthoredPair
open Zkc.Source Zkc.Source.Structured

abbrev Execution := Domain.PairExecution

/-- Both stages return, the selected Boolean is true, and no proof remains.
A producer stop is a failure even if its preceding proof would be accepted. -/
def succeeds {carriers : Carriers} {S : Type} (position : Nat)
    (execution : Execution carriers S) : Bool :=
  match execution.producer.outcome, execution.validator with
  | .returned _, some checked =>
      match checked.outcome with
      | .returned result =>
          (match result.values[position]? with
          | some (.data (.boolean true)) => true
          | _ => false) && checked.state.proof.isEmpty
      | .stopped _ => false
  | _, _ => false

/-- Retain the two stage traces separately; this concatenation exposes the
full execution order, including prefixes on a stop. -/
def observations {carriers : Carriers} {S : Type} (execution : Execution carriers S) :
    Domain.History carriers :=
  execution.producer.events ++ (execution.validator.map (·.events)).getD []

def executePrepared {m : Type → Type} [Monad m] {S : Type}
    (model : DomainModel) (program : Program) (context : Context) (actual : Artifacts)
    (producerInputs validatorInputs : Domain.Environment model.toCarriers)
    (oracle : Domain.Oracle m model.toCarriers S) (initial : S) :
    m (Execution model.toCarriers S) :=
  Domain.executePair model program context actual.producer actual.validator
    producerInputs validatorInputs oracle initial

/-- Original positions are preserved, including service positions. Service
handles cannot become private coins or public/proof payloads. -/
def inputValues (model : DomainModel) : {types : List Ty} → Values model.Value types →
    List (Option (Domain.Value model.toCarriers))
  | [], .nil => []
  | _ :: _, .cons value rest => Domain.Value.encode _ value :: inputValues model rest

def projectInputs {carriers : Carriers} (values : List (Option (Domain.Value carriers)))
    (positions : List Nat) : Option (Domain.Environment carriers) :=
  positions.mapM fun position => values[position]? >>= id

/-- The request cannot substitute validator inputs independently of the honest
invocation: both layouts are projected from the same typed original tuple.
The public-input order is the exact selected policy order. -/
def prepare {original : Snapshot} (imported : Imported original) (selected : Selection original)
    (model : DomainModel) (inputs : Values model.Value imported.program.payload.entry.inputs)
    (history : Domain.History model.toCarriers) :
    Option (Domain.Environment model.toCarriers × Domain.Environment model.toCarriers) := do
  let (types, interface) ← entryInterface original
  let values := inputValues model inputs
  let producer ← projectInputs values (dataInputs types interface.inputScopes selected.policy.producer)
  let validator ← projectInputs values selected.policy.publicInputs
  return (producer ++ [.transcript selected.policy.suite history],
    validator ++ [.transcript selected.policy.suite history])

/-- No separate producer implementation or input projection is chosen by
evidence. Failed preparation is a stopped experiment with no validator run. -/
def execute {original : Snapshot} (imported : Imported original) (selected : Selection original)
    (model : DomainModel)
    (inputs : Values model.Value imported.program.payload.entry.inputs)
    (history : Domain.History model.toCarriers)
    {m : Type → Type} [Monad m] {S : Type}
    (oracle : Domain.Oracle m model.toCarriers S) (initial : S) :
    m (Execution model.toCarriers S) :=
  match exportContext original selected.artifacts.validator,
      prepare imported selected model inputs history with
  | some context, some (producer, validator) =>
      executePrepared model imported.program context selected.artifacts producer validator oracle initial
  | _, _ => pure ⟨⟨.stopped .refused, ⟨[], [], initial⟩, []⟩, none⟩

/-- The acceptance position also comes from the selected source/policy map. -/
def selectedSucceeds {original : Snapshot} (selected : Selection original)
    {carriers : Carriers} {S : Type} (execution : Execution carriers S) : Bool :=
  match exportAcceptance original selected.artifacts.validator with
  | some position => succeeds position execution
  | none => false

theorem stopped_fails {carriers : Carriers} {S : Type} (position : Nat)
    (execution : Execution carriers S) (reason : PIR.Stop)
    (stopped : execution.producer.outcome = .stopped reason) :
    succeeds position execution = false := by simp [succeeds, stopped]

theorem leftover_fails {carriers : Carriers} {S : Type} (position : Nat)
    (execution : Execution carriers S)
    (checked : PIR.Execution (Domain.RuntimeState carriers S) (Domain.Event carriers)
      (Domain.Result carriers))
    (validator : execution.validator = some checked) (leftover : checked.state.proof ≠ []) :
    succeeds position execution = false := by
  have unread : checked.state.proof.isEmpty = false := by
    cases found : checked.state.proof <;> simp_all
  cases hp : execution.producer.outcome <;> cases hv : checked.outcome <;>
    simp [succeeds, validator, hp, hv, unread]

/-- Kernel-checked association transports the whole open producer process,
including all replies, final environments and stopped prefixes. This theorem
does not replace the missing original-to-constructed producer theorem. -/
theorem admitted_producer_process {original : Snapshot} {imported : Imported original}
    {selected : Selection original} {actual : Artifacts}
    (admitted : Admitted imported selected actual) (model : DomainModel) (context : Context)
    (inputs : Domain.Environment model.toCarriers) :
    Domain.participant model imported.program context actual.producer inputs =
      Domain.participant model imported.program context selected.artifacts.producer inputs := by
  rw [admitted_artifacts admitted]

end Zkc.Construction.AuthoredPair
