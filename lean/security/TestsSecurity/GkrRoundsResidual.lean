import ZkcSecurity.Examples.Components.GkrRoundsResidual
import Zkc.Source.Structured.ReplyScript
import TestsSecurity.GkrRoundsRealization

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace TestsSecurity.GkrRoundsResidual
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm
open ZkcSecurity.Examples.Components
open GkrRoundsBinding GkrRoundsResidual GkrRoundsRealization GkrRoundsGateRealization
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks

noncomputable section

def script (a b c challenge : ℚ) : ReplyScript ℚ ℚ where
  receive
    | .field _, site =>
      if site = "label_726f756e64_0" then some a
      else if site = "label_726f756e64_1" then some b
      else if site = "label_726f756e64_2" then some c
      else none
    | _, _ => none
  draw _ := some challenge

def round (point : Option (List ℚ)) (claim : Option ℚ) (service : Option Nat) :=
  protocol0Role1Callback0Process (F := ℚ) (G := ℚ) {} (some 91)
    (some [101]) (some [102]) (some [103]) (some [104]) (some [105]) point claim service

def runRound (a b c challenge : ℚ) (point : Option (List ℚ)) (claim : Option ℚ) (service : Option Nat) :=
  (script a b c challenge).run (round point claim service)

/-- All three received coefficients are attacker inputs. The entire return tuple
and actual query/send actions remain visible, including the private masks. -/
theorem arbitrary_reply :
    (runRound 1 2 3 2 (some [9]) (some 7) (some 83)).outcome =
      .returned (runtime (G := ℚ) [9, 2] 17) := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only [GkrRoundsBindingHelpers.owned_append (F := ℚ) (G := ℚ)]
  norm_num [ReplyScript.run, callback, receive, delivery, GkrRoundsBinding.query, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler,
    GkrRoundsBindingHelpers.owned_append, runtime, Values.get, Environment.push]

theorem boundary_rejects :
    (runRound 1 2 3 2 (some []) (some 8) (some 83)).outcome = .stopped .reject := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only [GkrRoundsBindingHelpers.owned_append (F := ℚ) (G := ℚ)]
  norm_num [ReplyScript.run, receive, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

theorem boundary_before_query :
    (runRound 1 2 3 2 (some []) (some 8) (some 83)).events.length = 3 := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only [GkrRoundsBindingHelpers.owned_append (F := ℚ) (G := ℚ)]
  norm_num [ReplyScript.run, receive, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

def missingThird : ReplyScript ℚ ℚ where
  receive ty site := if site = "label_726f756e64_2" then none else (script 1 2 3 2).receive ty site
  draw := (script 1 2 3 2).draw

theorem receive_stop_preserved :
    (missingThird.run (round (some []) (some 7) (some 83))).outcome = .stopped .refused ∧
      (missingThird.run (round (some []) (some 7) (some 83))).events.length = 3 := by
  unfold round
  rw [callback_source]
  norm_num [callback, ReplyScript.run, receive, missingThird, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

theorem missing_service :
    (runRound 1 2 3 2 (some []) (some 7) none).outcome = .stopped .incomplete := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only []
  norm_num [ReplyScript.run, receive, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

theorem missing_claim :
    (runRound 1 2 3 2 (some []) none (some 83)).outcome = .stopped .incomplete := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only []
  norm_num [ReplyScript.run, receive, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

theorem missing_point_after_delivery :
    (runRound 1 2 3 2 none (some 7) (some 83)).outcome = .stopped .incomplete ∧
      (runRound 1 2 3 2 none (some 7) (some 83)).events.length = 5 := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only [GkrRoundsBindingHelpers.owned_append (F := ℚ) (G := ℚ)]
  norm_num [ReplyScript.run, receive, delivery, GkrRoundsBinding.query,
    GkrRoundsBindingHelpers.owned_append, script, PIR.Process.run, PIR.Process.bind,
    PIR.Execution.follow, ReplyScript.handler]

def verifier (count : Nat) :=
  protocol0Role1Process (F := ℚ) (G := ℚ) {} (some [101]) (some [102]) (some [103]) (some [104])
    (some []) (some 2) (some count) (some 83)

/-- Two malicious non-honest triples both pass; exact source loop count,
point append and every private runtime output are checked. -/
theorem two_arbitrary_rounds :
    ((script 0 3 (-1) 2).run (verifier 2)).outcome =
      .returned (runtime (G := ℚ) [2, 2] 2) := by
  rw [show verifier 2 = _ from verifier_binding {} (RosterDistinct.root 1 2)
    _ _ _ _ (2 : ℚ) 83 2 (by decide) (n := 0)
    TestsSecurity.GkrRoundsRealization.raw
    (GkrRoundsLayout.state (x := 1) (y := 1) TestsSecurity.GkrRoundsRealization.wiringAdd
      TestsSecurity.GkrRoundsRealization.wiringMul
      TestsSecurity.GkrRoundsRealization.below TestsSecurity.GkrRoundsRealization.below)]
  dsimp only [GkrRoundsBinding.program, GkrRoundsBinding.query, participantInterface,
    Participant.interface, services, assignment]
  norm_num [ZkcSecurity.Families.Sumcheck.Program.remaining, GkrRoundsBinding.program, receive, delivery, GkrRoundsBinding.query,
    initial, advance, GkrRoundsBinding.carried, runtime, script, ReplyScript.run, ReplyScript.handler,
    PIR.Process.bind, PIR.Process.run, PIR.Execution.follow,
    ZkcSecurity.Families.Sumcheck.Message.coefficientTriples,
    ZkcSecurity.Families.Sumcheck.Message.ofTriple,
    Zkc.Protocols.AlgebraicRounds.Message.boundary,
    Zkc.Protocols.AlgebraicRounds.Message.evaluate]

theorem source_maximum (count : Nat) (large : 4 < count) :
    verifier count = .halt .refused :=
  above_maximum {} (RosterDistinct.root 1 2) _ _ _ _ _ _ _ count large

theorem zero_missing_optional :
    protocol0Role1Process (F := ℚ) (G := ℚ) {} (some [1]) none (some [3]) none (some []) none (some 0) none =
      .halt .incomplete :=
  zero {} (RosterDistinct.root 1 2) _ _ _ _ _ _ _

theorem zero_present_without_service (point : List ℚ) (claim : ℚ) :
    protocol0Role1Process (F := ℚ) (G := ℚ) {} none none none none (some point) (some claim) (some 0) none =
      .done (.cons none (.cons none (.cons none (.cons none (.cons none
        (.cons (some point) (.cons (some claim) .nil))))))) :=
  zero {} (RosterDistinct.root 1 2) _ _ _ _ _ _ _

/-- A perfectly decoded cubic input cannot instantiate the residual's layout
premise. This reuses the existing actual-helper independence refusal. -/
theorem cubic_independence_refused :
    ¬ Represents TestsSecurity.GkrRoundsRealization.cubicRaw TestsSecurity.GkrRoundsReference.cubicState :=
  TestsSecurity.GkrRoundsRealization.cubic_not_represented

/-- Changing the received quadratic coefficient invalidates the actual
boundary before the service query. -/
theorem changed_message_rejects :
    (runRound 1 2 4 2 (some [9]) (some 7) (some 83)).outcome = .stopped .reject ∧
      (runRound 1 2 4 2 (some [9]) (some 7) (some 83)).events.length = 3 := by
  unfold runRound round
  rw [callback_source]
  norm_num [callback, ReplyScript.run, receive, script, PIR.Process.run, PIR.Process.bind,
    PIR.Execution.follow, ReplyScript.handler]

/-- A deliberately changed arithmetic body keeps the boundary and all effects,
but drops the quadratic contribution from the returned scalar. -/
def linearizedBody : PIR.Process (participantInterface ℚ ℚ)
    (Values (Component (assignment ℚ ℚ)) spec.state) :=
  (receive {}).bind fun decoded =>
    match decoded with
    | none => .halt .refused
    | some (a, b, c) =>
        if (7 : ℚ) = a + a + b + c then
          .call (GkrRoundsBinding.query {} 83) fun (r : ℚ) =>
            (delivery {} r).bind fun _ => .done (runtime [9, r] (a + r * b))
        else .halt .reject

theorem changed_body_value :
    ((script 1 2 3 2).run linearizedBody).outcome =
      .returned (runtime (G := ℚ) [9, 2] 5) := by
  norm_num [linearizedBody, ReplyScript.run, receive, delivery, GkrRoundsBinding.query,
    script, PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

theorem changed_body_correspondence_refused :
    round (some [9]) (some 7) (some 83) ≠ linearizedBody := by
  intro same
  have observed := congrArg (fun body => ((script 1 2 3 2).run body).outcome) same
  change (runRound 1 2 3 2 (some [9]) (some 7) (some 83)).outcome =
    ((script 1 2 3 2).run linearizedBody).outcome at observed
  rw [arbitrary_reply, changed_body_value] at observed
  norm_num [runtime] at observed

def stopQuery : PIR.Handler (participantInterface ℚ ℚ) Unit (participantInterface ℚ ℚ).Op
  | action@(.query ..), state => ⟨.stopped .refused, state, [action]⟩
  | action, state => (script 1 2 3 2).handler action state

def stopDelivery : PIR.Handler (participantInterface ℚ ℚ) Unit (participantInterface ℚ ℚ).Op
  | action@(.send ..), state => ⟨.stopped .exhausted, state, [action]⟩
  | action, state => (script 1 2 3 2).handler action state

theorem query_stop_preserved :
    ((round (some [9]) (some 7) (some 83)).run stopQuery ()).outcome = .stopped .refused ∧
      ((round (some [9]) (some 7) (some 83)).run stopQuery ()).events.length = 4 := by
  unfold round
  rw [callback_source]
  norm_num [callback, receive, delivery, GkrRoundsBinding.query, script, stopQuery,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

theorem delivery_stop_preserved :
    ((round (some [9]) (some 7) (some 83)).run stopDelivery ()).outcome = .stopped .exhausted ∧
      ((round (some [9]) (some 7) (some 83)).run stopDelivery ()).events.length = 5 := by
  unfold round
  rw [callback_source]
  norm_num [callback, receive, delivery, GkrRoundsBinding.query, script, stopDelivery,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

/-- The exact requests include the selected service, method, sender, recipient
and delivery value; a trace-length observation alone would not check them. -/
theorem exact_actions :
    (runRound 1 2 3 2 (some [9]) (some 7) (some 83)).events =
      [.receive scalar "label_726f756e64_0" 0,
       .receive scalar "label_726f756e64_1" 0,
       .receive scalar "label_726f756e64_2" 0,
       GkrRoundsBinding.query {} 83,
       .send (ty := scalar) "label_64656c6976657279_0" 0 (2 : ℚ)] := by
  unfold runRound round
  rw [callback_source]
  unfold callback
  simp only [GkrRoundsBindingHelpers.owned_append (F := ℚ) (G := ℚ)]
  norm_num [ReplyScript.run, receive, delivery, GkrRoundsBinding.query, script,
    PIR.Process.run, PIR.Process.bind, PIR.Execution.follow, ReplyScript.handler]

/-- The nonconstant caller representation has a false scalar precondition;
the actual arbitrary-message run above is not vacuous. -/
theorem concrete_total :
    GkrRoundsReference.total (GkrRoundsLayout.state (x := 1) (y := 1)
      TestsSecurity.GkrRoundsRealization.wiringAdd TestsSecurity.GkrRoundsRealization.wiringMul
      TestsSecurity.GkrRoundsRealization.below TestsSecurity.GkrRoundsRealization.below) = 640 := by
  norm_num [GkrRoundsReference.total, GkrRoundsLayout.state, GkrRoundsLayout.replicate,
    GkrRoundsLayout.tile, GkrRoundsLayout.leading, GkrRoundsLayout.trailing,
    Zkc.Polynomial.Multilinear.booleanSum, Zkc.Polynomial.Multilinear.half,
    Zkc.Protocols.AlgebraicRounds.Gate.value,
    TestsSecurity.GkrRoundsRealization.wiringAdd, TestsSecurity.GkrRoundsRealization.wiringMul,
    TestsSecurity.GkrRoundsRealization.below]

theorem concrete_false_initial :
    (2 : ℚ) ≠ GkrRoundsReference.total (GkrRoundsLayout.state (x := 1) (y := 1)
      TestsSecurity.GkrRoundsRealization.wiringAdd TestsSecurity.GkrRoundsRealization.wiringMul
      TestsSecurity.GkrRoundsRealization.below TestsSecurity.GkrRoundsRealization.below) := by
  rw [concrete_total]
  norm_num

/-- The actual charged derivation can be instantiated on nonconstant factors
with all verifier-private inputs absent. Sampling remains the explicit local
conditional-query property, with no honest message or residual premise. -/
def concrete_residual {E P : Type} {Raw : E → Type}
    [∀ event, SampleableType (Raw event)]
    {absorb : Zkc.Transcript.Interface (participantInterface ℚ ℚ) E P Raw}
    {charge : List E → E → ENNReal}
    (queries : ZkcSecurity.Families.Sumcheck.QueryInterface (GkrRoundsBinding.program 83) absorb)
    (sampling : queries.ConditionalBound (representation 83) 2 2 charge) (history : List E) :=
  verifier_residual 83 2 (by decide) {} (RosterDistinct.root 1 2) none none none none
    (n := 0) TestsSecurity.GkrRoundsRealization.raw
    (GkrRoundsLayout.state (x := 1) (y := 1) TestsSecurity.GkrRoundsRealization.wiringAdd
      TestsSecurity.GkrRoundsRealization.wiringMul
      TestsSecurity.GkrRoundsRealization.below TestsSecurity.GkrRoundsRealization.below)
    2 TestsSecurity.GkrRoundsRealization.concrete_represents concrete_false_initial queries sampling history

#print axioms arbitrary_reply
#print axioms two_arbitrary_rounds
#print axioms changed_body_correspondence_refused
#print axioms exact_actions
#print axioms GkrRoundsBinding.verifier_binding
#print axioms GkrRoundsResidual.verifier_residual
#print axioms GkrRoundsResidual.verifier_doomed
#print axioms GkrRoundsResidual.conditional_uniform
#print axioms GkrRoundsResidual.verifier_uniform_residual
#print axioms GkrRoundsResidual.noReturn_exact_point
#print axioms concrete_residual

end
end TestsSecurity.GkrRoundsResidual
