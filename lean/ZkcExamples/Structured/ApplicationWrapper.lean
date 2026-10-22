module

public import ZkcExamples.Structured.ApplicationWrapperViews
public import ZkcExamples.Structured.ServiceOrder

public section

/-! Exact nested action sites of the complete wrapper source. The application
context changes protocol sites; it never changes the actual service handles. -/
namespace ZkcExamples.Structured.ApplicationWrapper

set_option smartUnfolding false
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies ApplicationWrapperViews

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The nested child uses the wrapper's complete linked protocol table. -/
theorem run_body_view (context : ProtocolContext) (self : Nat)
    (go : Option Bool) (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature context self
        (ServiceOrder.inputs go first second) =
      (runBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes runSignature.inputScopes)
          (ServiceOrder.inputs go first second)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes runSignature.outputScopes) results)) :=
  unit.protocol_body_view_as runDefinition run_member
    runSignature run_signature runBody run_raw
    context self (ServiceOrder.inputs go first second)

/-- The grandchild is transported through the same full table, without lookup reduction. -/
theorem draw_body_view (context : ProtocolContext) (self : Nat)
    (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) drawSignature context self
        (ServiceOrder.servicesInput first second) =
      (drawBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes drawSignature.inputScopes)
          (ServiceOrder.servicesInput first second)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes drawSignature.outputScopes) results)) :=
  unit.protocol_body_view_as drawDefinition draw_member
    drawSignature draw_signature drawBody draw_raw
    context self (ServiceOrder.servicesInput first second)

theorem outer_body_view (context : ProtocolContext) (self : Nat)
    (go : Option Bool) (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) outerSignature context self
        (ServiceOrder.inputs go first second) =
      (outerBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes outerSignature.inputScopes)
          (ServiceOrder.inputs go first second)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes outerSignature.outputScopes) results)) :=
  unit.protocol_body_view_as outerDefinition outer_member outerSignature outer_signature
    outerBody outer_raw context self (ServiceOrder.inputs go first second)

set_option smartUnfolding true in
theorem observed_verifier (go : Bool) (first second : Nat) :
    program.observed F G 1 (ServiceOrder.inputs (some go) (some first) (some second)) =
      .call (.mark "s0")
        (fun _ => ServiceOrder.verifierObserved (some "s0") go first second) := by
  change invokeProtocol (unit.protocolTable F G) outerSignature {} 1 _ = _
  have run_view := run_body_view (F := F) (G := G)
  simp only [ServiceOrder.inputs] at run_view
  have draw_view := draw_body_view (F := F) (G := G)
  simp only [ServiceOrder.servicesInput] at draw_view
  rw [outer_body_view]
  simp only [outerBody, runBody, Region.denote, participantMeaning, participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, observedSites, PIR.Process.bind,
    Environment.prepend, ServiceOrder.inputs, run_view, draw_view]
  set_option smartUnfolding false in
    cases go <;> rfl

set_option smartUnfolding true in
theorem observed_receiver (go : Option Bool) (first second : Option Nat) :
    program.observed F G 0 (ServiceOrder.inputs go first second) =
      .call (.mark "s0") (fun _ => ServiceOrder.receiverObserved (some "s0")) := by
  change invokeProtocol (unit.protocolTable F G) outerSignature {} 0 _ = _
  have run_view := run_body_view (F := F) (G := G)
  simp only [ServiceOrder.inputs] at run_view
  have draw_view := draw_body_view (F := F) (G := G)
  simp only [ServiceOrder.servicesInput] at draw_view
  rw [outer_body_view]
  simp only [outerBody, runBody, Region.denote, participantMeaning, participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, observedSites, PIR.Process.bind,
    Environment.prepend, ServiceOrder.inputs, run_view, draw_view]
  rfl

theorem verifier_participant (go : Bool) (first second : Nat) :
    program.participant F G 1 (ServiceOrder.inputs (some go) (some first) (some second)) =
      ServiceOrder.verifierProcess (some "s0") go first second := by
  unfold Program.participant
  rw [observed_verifier]
  change (ServiceOrder.verifierObserved (F := F) (G := G)
    (some "s0") go first second).interpret forgetSites = _
  exact ServiceOrder.verifier_forget_marks _ _ _ _

theorem receiver_participant (go : Option Bool) (first second : Option Nat) :
    program.participant F G 0 (ServiceOrder.inputs go first second) =
      .call (.receive fieldType "apply_13_apply_2_s0_s3_s5_0" 1)
        (fun received => .done (.cons (some received) (.cons none .nil))) := by
  unfold Program.participant
  rw [observed_receiver]
  change (ServiceOrder.receiverObserved (F := F) (G := G) (some "s0")).interpret forgetSites = _
  exact ServiceOrder.receiver_forget_marks _

/-- The leaf is qualified by the already qualified parent call site. -/
theorem nested_exchange_site :
    qualifyProtocolSite (some (qualifyProtocolSite (some "s0") "s3")) "s5_0" =
      "apply_13_apply_2_s0_s3_s5_0" := by
  decide +kernel

theorem nested_qualification_is_not_right_associated :
    qualifyProtocolSite (some (qualifyProtocolSite (some "s0") "s3")) "s5_0" ≠
      qualifyProtocolSite (some "s0") (qualifyProtocolSite (some "s3") "s5_0") := by
  decide +kernel

end ZkcExamples.Structured.ApplicationWrapper
