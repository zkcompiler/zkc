module

public import ZkcSecurity.Bindings.Transcript.HonestSampledReadback
public import Mathlib.Tactic.Ring

@[expose] public section

/-! An honest composition client with fresh private coins between rounds.

These are actual Domain processes, with an additive commit/response equation
and heterogeneous boolean/index/field messages. The example proves perfect
completeness only. It supplies neither a source-export correspondence nor a
knowledge or zero-knowledge theorem for this algebraic protocol.
-/

set_option autoImplicit false
namespace ZkcSecurity.Examples.Components.SequentialSigma
open Zkc.Source Zkc.Construction ZkcSecurity.FiatShamir

variable {F : Type} [Field F] [DecidableEq F]

abbrev carriers (F : Type) := Structured.uniformCarriers F Unit

def port : ServicePort := ⟨"coins", "producer", 3, 3, "random.scalar/0"⟩
def privateOrigin : Origin := .query "sequential-sigma" "nonce" "input_3"
  "random.scalar/0" "producer" (.draw "scalar")
def publicOrigin (round : Nat) : Origin := .query "sequential-sigma"
  ("challenge-" ++ toString round) "input_4" "random.scalar/0" "validator" (.draw "scalar")

def Allowed (actualPort : ServicePort) (origin : Origin) : Prop :=
  actualPort = port ∧ origin = privateOrigin

def flag (round : Nat) : Bool := round % 2 == 0

def messageOrigin (site : String) : Origin :=
  .message "sequential-sigma" site "producer" "validator"

def commitmentHistory (prior : Domain.History (carriers F)) (round : Nat)
    (enabled : Bool) (commitment : F) : Domain.History (carriers F) :=
  prior ++ [.message (messageOrigin "flag") (.boolean enabled),
    .message (messageOrigin "round") (.index round),
    .message (messageOrigin "commitment") (.field "scalar" commitment)]

structure Frame (F : Type) where
  history : Domain.History (carriers F)
  enabled : Bool
  round : Nat
  commitment : F
  challenge : F
  response : F

def frame (prior : Domain.History (carriers F)) (round : Nat) (enabled : Bool)
    (commitment challenge response : F) : Frame F :=
  ⟨commitmentHistory prior round enabled commitment ++
    [.challenge (publicOrigin round), .message (messageOrigin "response") (.field "scalar" response)],
    enabled, round, commitment, challenge, response⟩

def environment (round : Nat) (enabled : Bool) (response : F) : Domain.Environment (carriers F) :=
  [.data (.boolean enabled), .data (.index round), .data (.field "scalar" response)]

def producerStage (round : Nat) (prior : Domain.History (carriers F)) (base witness : F) :
    PIR.Process (Domain.effects (carriers F)) (Frame F) :=
  .call (.localService port privateOrigin) fun nonce : F =>
  .call (.send "flag" "boolean" "validator" (.boolean (flag round))) fun _ =>
  .call (.send "round" "index" "validator" (.index round)) fun _ =>
  .call (.send "commitment" "scalar" "validator" (.field "scalar" (base * nonce))) fun _ =>
  .call (.query (commitmentHistory prior round (flag round) (base * nonce)) (publicOrigin round))
    fun challenge : F =>
  let response := nonce + challenge * witness
  .call (.send "response" "scalar" "validator" (.field "scalar" response)) fun _ =>
  .call (.checkpoint (environment round (flag round) response)) fun _ =>
  .call (.observe (.message (messageOrigin "response") (.field "scalar" response))) fun _ =>
  .done (frame prior round (flag round) (base * nonce) challenge response)

def validatorStage (round : Nat) (prior : Domain.History (carriers F)) (base statement : F) :
    PIR.Process (Domain.effects (carriers F)) (Frame F) :=
  .call (.receive .boolean "flag" "boolean" "producer") fun enabled =>
  .call (.receive .index "round" "index" "producer") fun receivedRound =>
  .call (.receive (.field "scalar") "commitment" "scalar" "producer") fun commitment =>
  .call (.query (commitmentHistory prior receivedRound enabled commitment) (publicOrigin round))
    fun challenge : F =>
  .call (.receive (.field "scalar") "response" "scalar" "producer") fun response =>
  if receivedRound = round ∧ enabled = flag round ∧
      base * response = commitment + challenge * statement then
    .call (.checkpoint (environment receivedRound enabled response)) fun _ =>
    .call (.observe (.message (messageOrigin "response") (.field "scalar" response))) fun _ =>
    .call (.send "acknowledgment" "boolean" "producer" (.boolean true)) fun _ =>
    .done (frame prior receivedRound enabled commitment challenge response)
  else .halt .reject

/-- One reusable component law. The public reply is universally quantified;
it is never identified with the fresh nonce. -/
theorem stage_readback (round : Nat) (prior : Domain.History (carriers F)) (base witness : F) :
    SampledReadback Allowed Eq (producerStage round prior base witness)
      (validatorStage round prior base (base * witness)) := by
  unfold producerStage validatorStage
  apply SampledReadback.localServiceLeft (carriers := carriers F) port privateOrigin ⟨rfl, rfl⟩
  intro nonce
  change F at nonce
  apply SampledReadback.sendReceive (carriers := carriers F) (ty := .boolean)
    "flag" "boolean" "validator" "flag" "boolean" "producer"
    (.boolean (flag round)) (flag round) rfl
  apply SampledReadback.sendReceive (carriers := carriers F) (ty := .index)
    "round" "index" "validator" "round" "index" "producer" (.index round) round rfl
  apply SampledReadback.sendReceive (carriers := carriers F) (ty := .field "scalar")
    "commitment" "scalar" "validator" "commitment" "scalar" "producer"
    (.field "scalar" (base * nonce)) (base * nonce) (by simp [Domain.Payload.value])
  apply SampledReadback.query (carriers := carriers F) _ (publicOrigin round) rfl
  intro challenge
  change F at challenge
  apply SampledReadback.sendReceive (carriers := carriers F) (ty := .field "scalar")
    "response" "scalar" "validator" "response" "scalar" "producer"
    (.field "scalar" (nonce + challenge * witness)) (nonce + challenge * witness)
    (by simp [Domain.Payload.value])
  have equation : base * (nonce + challenge * witness) =
      base * nonce + challenge * (base * witness) := by ring
  simp only [equation, and_self, ite_true]
  apply SampledReadback.checkpointLeft
  apply SampledReadback.checkpointRight
  apply SampledReadback.observeLeft
  apply SampledReadback.observeRight
  apply SampledReadback.sendRight
  exact .deterministic (.done rfl)

def producer (base firstWitness secondWitness : F) :
    PIR.Process (Domain.effects (carriers F)) (Frame F) :=
  (producerStage 0 [] base firstWitness).bind fun first =>
  producerStage 1 first.history base secondWitness

def validator (base firstStatement secondStatement : F) :
    PIR.Process (Domain.effects (carriers F)) (Frame F) :=
  (validatorStage 0 [] base firstStatement).bind fun first =>
  validatorStage 1 first.history base secondStatement

/-- Two independently sampled stages compose using the actual first return,
including its full history, as the second caller's input. -/
theorem readback (base firstWitness secondWitness : F) :
    SampledReadback Allowed Eq (producer base firstWitness secondWitness)
      (validator base (base * firstWitness) (base * secondWitness)) := by
  apply (stage_readback 0 [] base firstWitness).bind
  intro first second same
  subst second
  exact stage_readback 1 first.history base secondWitness

/-- The same component law installs at arbitrary finite adaptive depth. -/
theorem repeated_readback (count : Nat) (initial : Frame F) (base witness : F) :
    SampledReadback Allowed Eq
      (PIR.repeatN count (fun state : Frame F =>
        producerStage (state.round + 1) state.history base witness) initial)
      (PIR.repeatN count (fun state : Frame F =>
        validatorStage (state.round + 1) state.history base (base * witness)) initial) := by
  apply SampledReadback.repeatN (fun _ => Eq)
  · intro n first second same
    subst second
    exact stage_readback _ _ _ _
  · rfl

end ZkcSecurity.Examples.Components.SequentialSigma
