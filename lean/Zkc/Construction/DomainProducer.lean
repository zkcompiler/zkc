module

public import Zkc.Construction.DomainExecution

@[expose] public section

/-! Proof handlers for the single constructed evaluator.

The oracle state is explicit: a paired experiment passes the producer's final
oracle state to the validator. A security handler must implement shared keyed
queries coherently. A fresh independent sample on every call does not implement
that experiment. Local services have a separate interpreter; omitting it
refuses every local request rather than inventing private coins.
-/
set_option autoImplicit false
namespace Zkc.Construction.Domain
open Zkc.Source

variable {carriers : Structured.Carriers} {S A : Type} {m : Type → Type} [Monad m]

structure RuntimeState (carriers : Structured.Carriers) (S : Type) where
  environment : Environment carriers
  proof : Proof carriers
  oracle : S

/-- Both successful and failed queries retain the oracle post-state. The event
fixes the reply carrier. Probability and cache laws are security obligations. -/
abbrev Oracle (m : Type → Type) (carriers : Structured.Carriers) (S : Type) :=
  History carriers → (event : Event carriers) → S → m (PIR.Outcome (Raw event) × S)

inductive Mode where
  | producer
  | validator
  deriving DecidableEq

/-- Local capabilities are separate from the public keyed oracle. Both share
one explicit runtime state, including any service counters installed by a model. -/
abbrev LocalServices (m : Type → Type) (carriers : Structured.Carriers) (S : Type) :=
  Mode → ServicePort → (origin : Origin) → S →
    m (PIR.Outcome (Raw (.challenge origin : Event carriers)) × S)

/-- No local capability is granted implicitly to transcript-only experiments. -/
def refuseLocal : LocalServices m carriers S :=
  fun _ _ _ state => pure (.stopped .refused, state)

/-- Unsupported methods, operands and non-field requests cannot reach the oracle. -/
def drawRequest : Origin → Bool
  | ⟨_, _, some ⟨"draw", [], .field _⟩⟩ => true
  | _ => false

/-- Production appends exact sent payloads. Validation consumes only successfully
decoded messages. A failed decode leaves the entire unread suffix in place.
Receive is unsupported on the compiled producer path; it is never fabricated
from an interactive source role or a fresh random sample. -/
def handler (mode : Mode) (oracle : Oracle m carriers S)
    (services : LocalServices m carriers S := refuseLocal) :
    PIR.MonadHandler m (effects carriers) (RuntimeState carriers S) (Event carriers)
  | .checkpoint env, state => pure ⟨.returned (), { state with environment := env }, []⟩
  | .observe event, state => pure ⟨.returned (), state, [event]⟩
  | .receive ty _ _ _, state =>
      match mode, state.proof with
      | .validator, payload :: unread =>
          match payload.value ty with
          | some value => pure ⟨.returned value, { state with proof := unread }, []⟩
          | none => pure ⟨.stopped .refused, state, []⟩
      | _, _ => pure ⟨.stopped .refused, state, []⟩
  | .send _ _ _ payload, state =>
      match mode with
      | .producer => pure ⟨.returned (), { state with proof := state.proof ++ [payload] }, []⟩
      | .validator => pure ⟨.returned (), state, []⟩
  | .localService port origin, state => do
      let (outcome, final) ← services mode port origin state.oracle
      pure ⟨outcome, { state with oracle := final }, []⟩
  | .query history origin, state =>
      if drawRequest origin then do
        let (outcome, final) ← oracle history (.challenge origin) state.oracle
        pure ⟨outcome, { state with oracle := final }, [.challenge origin]⟩
      else pure ⟨.stopped .refused, state, []⟩

def run (mode : Mode) (oracle : Oracle m carriers S)
    (process : PIR.Process (effects carriers) A) (state : RuntimeState carriers S)
    (services : LocalServices m carriers S := refuseLocal) :
    m (PIR.Execution (RuntimeState carriers S) (Event carriers) A) :=
  process.runM (handler mode oracle services) state

/-- Run an actual constructed producer participant, starting with empty output.
The caller selects and admits this artifact; a source participant is not used. -/
def produce (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (constructed : Participant) (inputs : Environment model.toCarriers)
    (oracle : Oracle m model.toCarriers S) (initial : S)
    (services : LocalServices m model.toCarriers S := refuseLocal) :
    m (PIR.Execution (RuntimeState model.toCarriers S) (Event model.toCarriers)
      (Result model.toCarriers)) :=
  run .producer oracle (participant model program context constructed inputs) ⟨inputs, [], initial⟩ services

/-- The result exposes unread proof, every return value, observations and state.
The request's proof-consumption and acceptance policies are checked by its owner. -/
def validate (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (constructed : Participant) (inputs : Environment model.toCarriers)
    (proof : Proof model.toCarriers) (oracle : Oracle m model.toCarriers S) (initial : S)
    (services : LocalServices m model.toCarriers S := refuseLocal) :
    m (PIR.Execution (RuntimeState model.toCarriers S) (Event model.toCarriers)
      (Result model.toCarriers)) :=
  run .validator oracle (participant model program context constructed inputs) ⟨inputs, proof, initial⟩ services

/-- Both executions remain available to the consumer, including the producer's
returns, post-state and observations. A failed producer never runs validation. -/
structure PairExecution (carriers : Structured.Carriers) (S : Type) where
  producer : PIR.Execution (RuntimeState carriers S) (Event carriers) (Result carriers)
  validator : Option (PIR.Execution (RuntimeState carriers S) (Event carriers) (Result carriers))

/-- The same keyed oracle and its actual post-state serve both admitted artifacts.
This supplies sequencing only; pair admission, input alignment, acceptance and
probability laws remain with their respective owners. -/
def executePair (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (producer validator : Participant)
    (producerInputs validatorInputs : Environment model.toCarriers)
    (oracle : Oracle m model.toCarriers S) (initial : S)
    (services : LocalServices m model.toCarriers S := refuseLocal) :
    m (PairExecution model.toCarriers S) := do
  let produced ← produce model program context producer producerInputs oracle initial services
  match produced.outcome with
  | .stopped _ => pure ⟨produced, none⟩
  | .returned _ =>
      let validated ← validate model program context validator validatorInputs
        produced.state.proof oracle produced.state.oracle services
      pure ⟨produced, some validated⟩

end Zkc.Construction.Domain

-- Store interpreter equations here, including their private proof helpers.
-- Clients must not generate distinct providers for the same equation name.
run_cmd Lean.Elab.Command.liftTermElabM do
  for declaration in [``Zkc.Construction.Domain.drawRequest,
      ``Zkc.Construction.Domain.handler, ``Zkc.Construction.Domain.run,
      ``Zkc.Construction.Domain.produce, ``Zkc.Construction.Domain.validate,
      ``Zkc.Construction.Domain.executePair] do
    discard <| Lean.Meta.getEqnsFor? declaration
