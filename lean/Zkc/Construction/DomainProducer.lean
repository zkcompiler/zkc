module

public import Zkc.Construction.DomainExecution

@[expose] public section

/-! Proof handlers for the single constructed evaluator.

The oracle state is explicit: a paired experiment passes the producer's final
oracle state to the validator. A security handler must implement shared keyed
queries coherently. A fresh independent sample on every call does not implement
that experiment. Private fresh coins have no instruction in this vocabulary.
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

/-- Unsupported methods, operands and non-field requests cannot reach the oracle. -/
def drawRequest : Origin → Bool
  | ⟨_, _, some ⟨"draw", [], .field _⟩⟩ => true
  | _ => false

/-- Production appends exact sent payloads. Validation consumes only successfully
decoded messages. A failed decode leaves the entire unread suffix in place.
Receive is unsupported on the compiled producer path; it is never fabricated
from an interactive source role or a fresh random sample. -/
def handler (mode : Mode) (oracle : Oracle m carriers S) :
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
  | .query history origin, state =>
      if drawRequest origin then do
        let (outcome, final) ← oracle history (.challenge origin) state.oracle
        pure ⟨outcome, { state with oracle := final }, [.challenge origin]⟩
      else pure ⟨.stopped .refused, state, []⟩

def run (mode : Mode) (oracle : Oracle m carriers S)
    (process : PIR.Process (effects carriers) A) (state : RuntimeState carriers S) :
    m (PIR.Execution (RuntimeState carriers S) (Event carriers) A) :=
  process.runM (handler mode oracle) state

/-- Run an actual constructed producer participant, starting with empty output.
The caller selects and admits this artifact; a source participant is not used. -/
def produce (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (constructed : Participant) (inputs : Environment model.toCarriers)
    (oracle : Oracle m model.toCarriers S) (initial : S) :
    m (PIR.Execution (RuntimeState model.toCarriers S) (Event model.toCarriers)
      (Result model.toCarriers)) :=
  run .producer oracle (participant model program context constructed inputs) ⟨inputs, [], initial⟩

/-- The result exposes unread proof, every return value, observations and state.
The request's proof-consumption and acceptance policies are checked by its owner. -/
def validate (model : Structured.DomainModel) (program : Structured.Program)
    (context : Context) (constructed : Participant) (inputs : Environment model.toCarriers)
    (proof : Proof model.toCarriers) (oracle : Oracle m model.toCarriers S) (initial : S) :
    m (PIR.Execution (RuntimeState model.toCarriers S) (Event model.toCarriers)
      (Result model.toCarriers)) :=
  run .validator oracle (participant model program context constructed inputs) ⟨inputs, proof, initial⟩

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
    (oracle : Oracle m model.toCarriers S) (initial : S) :
    m (PairExecution model.toCarriers S) := do
  let produced ← produce model program context producer producerInputs oracle initial
  match produced.outcome with
  | .stopped _ => pure ⟨produced, none⟩
  | .returned _ =>
      let validated ← validate model program context validator validatorInputs
        produced.state.proof oracle produced.state.oracle
      pure ⟨produced, some validated⟩

end Zkc.Construction.Domain
