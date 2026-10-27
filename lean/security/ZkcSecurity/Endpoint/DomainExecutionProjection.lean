module

public import ZkcSecurity.Endpoint.DomainCompiled
public import Zkc.Construction.DomainExecutionLaws

@[expose] public section

/-! A proved reading of the core execution handler. The constructed evaluator
still owns instructions, values and oracle histories. This reading forgets
only side observations and checkpoints when an endpoint asks for outcome and
unread proof. It introduces no sampling or probabilistic experiment. -/
set_option autoImplicit false
namespace ZkcSecurity.Endpoint.Domain
open Zkc Zkc.Source Zkc.Construction
variable {carriers : Structured.Carriers} {m : Type → Type} [Monad m] {A : Type}

def readExecution (query : Construction.Domain.History carriers →
    (event : Construction.Domain.Event carriers) → m (Construction.Domain.Raw event)) :
    PIR.Process (Construction.Domain.effects carriers) A → Construction.Domain.Proof carriers →
      m (PIR.Outcome A × Construction.Domain.Proof carriers)
  | .done value, proof => pure (.returned value, proof)
  | .halt reason, proof => pure (.stopped reason, proof)
  | .call (.receive ty _ _ _) next, proof =>
      match proof with
      | [] => pure (.stopped .refused, [])
      | payload :: unread =>
          match payload.value ty with
          | none => pure (.stopped .refused, payload :: unread)
          | some value => readExecution query (next value) unread
  | .call (.localService ..) _, proof => pure (.stopped .refused, proof)
  | .call (.query history origin) next, proof =>
      if Construction.Domain.drawRequest origin then do
        let answer ← query history (.challenge origin)
        readExecution query (next answer) proof
      else pure (.stopped .refused, proof)
  | .call (.send ..) next, proof | .call (.observe ..) next, proof |
    .call (.checkpoint ..) next, proof => readExecution query (next ()) proof

variable [LawfulMonad m]

theorem readExecution_eq (query : Construction.Domain.History carriers →
    (event : Construction.Domain.Event carriers) → m (Construction.Domain.Raw event))
    (process : PIR.Process (Construction.Domain.effects carriers) A)
    (state : Construction.Domain.RuntimeState carriers Unit) :
    (fun result => (result.outcome, result.state.proof)) <$>
      Construction.Domain.run .validator (Compiled.oracle query) process state =
      readExecution query process state.proof := by
  rw [Construction.Domain.validator_eq_direct]
  induction process generalizing state with
  | done => simp [Construction.Domain.validateDirect, readExecution]
  | halt => simp [Construction.Domain.validateDirect, readExecution]
  | call operation next ih =>
    cases operation with
    | receive ty site schema peer =>
      cases hp : state.proof with
      | nil => simp [Construction.Domain.validateDirect, readExecution, hp]
      | cons payload unread =>
        cases decoded : payload.value ty <;>
          simp [Construction.Domain.validateDirect, readExecution, hp, decoded, ih]
    | send => simp [Construction.Domain.validateDirect, readExecution, ih]
    | checkpoint => simp [Construction.Domain.validateDirect, readExecution, ih]
    | observe => simp [Construction.Domain.validateDirect, readExecution, ← ih]
    | localService => simp [Construction.Domain.validateDirect, readExecution]
    | query history origin =>
      simp only [Construction.Domain.validateDirect, readExecution]
      split
      · simp [Compiled.oracle, PIR.Execution.followM, ← ih, Functor.map_map]
      · simp

theorem Compiled.verifier_readExecution {art : Artifacts} (compiled : Compiled art)
    (model : Structured.DomainModel) (query : Construction.Domain.History model.toCarriers →
      (event : Construction.Domain.Event model.toCarriers) → m (Construction.Domain.Raw event))
    (statement : art.Statement model) (initial : Construction.Domain.History model.toCarriers)
    (proof : Construction.Domain.Proof model.toCarriers) :
    compiled.verifier model query statement initial proof =
      match Construction.Domain.encodeValues statement with
      | none => pure (.stopped .refused, proof)
      | some inputs =>
        (fun result => (Zkc.Transcript.mapOutcome compiled.acceptance result.1, result.2)) <$>
          readExecution query
            (Construction.Domain.participant model compiled.imported.program compiled.selection.context
              art.participant (Construction.Domain.inputFrame compiled.selection.context inputs initial)) proof := by
  unfold verifier
  cases Construction.Domain.encodeValues statement with
  | none => rfl
  | some inputs =>
    simp only
    rw [← readExecution_eq query _
      ⟨Construction.Domain.inputFrame compiled.selection.context inputs initial, proof, ()⟩]
    simp [Construction.Domain.validate, Functor.map_map]

end ZkcSecurity.Endpoint.Domain
