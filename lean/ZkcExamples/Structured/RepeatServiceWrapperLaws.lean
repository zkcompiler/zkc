module

public import ZkcExamples.Structured.RepeatServiceWrapperViews
public import ZkcExamples.Structured.RepeatServiceLaws

@[expose] public section

/-! The full three-role wrapper keeps the outsider's value and maps the nested
receiver/sender to root roles 2/0, retaining both actual service handles. -/
namespace ZkcExamples.Structured.RepeatServiceWrapperLaws
open Zkc.Source Zkc.Source.Structured RepeatServiceWrapperBodies RepeatServiceWrapperViews

set_option smartUnfolding false

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (count : Option Nat) (outside : Option F) (first second : Option Nat) :
    Values (Component (assignment F G)) outerSignature.inputs :=
  .cons count (.cons outside (.cons first (.cons second .nil)))

theorem outer_body_view (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) outerSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) outerSignature context self args =
      (outerBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes outerSignature.inputScopes) args).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes outerSignature.outputScopes) results)) :=
  unit.protocol_body_view_as outerDefinition outer_member outerSignature outer_signature
    outerBody outer_raw context self args

/-- The retained Run closure captures the same full Draw prefix in both units. -/
theorem run_agrees (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) runSignature.inputs) :
    invokeProtocol (unit.protocolTable F G) runSignature context self args =
      invokeProtocol (RepeatServiceViews.unit.protocolTable F G)
        RepeatServiceBodies.runSignature context self args := rfl

def senderObserved (count first second : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) outerSignature.outputs) :=
  .call (.mark "s0") <| fun _ =>
  (RepeatServiceLaws.verifierObserved (F := F) (G := G) (some "s0") 2 count first second).bind
    fun result => .done (.cons (result.get (.there .here)) (.cons none (.cons none .nil)))

def receiverObserved (count : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) outerSignature.outputs) :=
  .call (.mark "s0") <| fun _ =>
  (RepeatServiceLaws.receiverObserved (F := F) (G := G) (some "s0") 0 count).bind
    fun result => .done (.cons none (.cons none (.cons (result.get .here) .nil)))

set_option smartUnfolding true in
theorem observed_sender (count : Nat) (bound : count ≤ 3) (outside : Option F)
    (first second : Nat) :
    program.observed F G 0 (inputs (some count) outside (some first) (some second)) =
      senderObserved count first second := by
  change invokeProtocol (unit.protocolTable F G) outerSignature {} 0
    (inputs (some count) outside (some first) (some second)) = _
  rw [outer_body_view]
  simp only [outerBody, Region.denote, participantMeaning, participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, observedSites, PIR.Proc.bind,
    Environment.prepend, inputs]
  simp only [PIR.Proc.bind_assoc]
  change (PIR.Proc.call (I := observedInterface F G) (.mark "s0") _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) outerSignature.outputs)) =
    PIR.Proc.call (I := observedInterface F G) (.mark "s0") _
  congr 1
  funext ignored
  apply congrArg₂ (PIR.Proc.bind (I := observedInterface F G)
    (A := Values (Component (assignment F G)) runSignature.outputs)
    (B := Values (Component (assignment F G)) outerSignature.outputs))
  · exact (run_agrees ⟨some "s0", roleSubstitution [2, 0]⟩ 0
      (RepeatServiceLaws.inputs (some count) (some first) (some second))).trans
      (RepeatServiceLaws.permuted_verifier (some "s0") count bound first second)
  · funext values
    cases values with
    | cons a rest =>
      cases rest with
      | cons b rest => cases rest; rfl

set_option smartUnfolding true in
theorem observed_receiver (count : Nat) (bound : count ≤ 3) (outside : Option F)
    (first second : Option Nat) :
    program.observed F G 2 (inputs (some count) outside first second) = receiverObserved count := by
  change invokeProtocol (unit.protocolTable F G) outerSignature {} 2
    (inputs (some count) outside first second) = _
  rw [outer_body_view]
  simp only [outerBody, Region.denote, participantMeaning, participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, observedSites, PIR.Proc.bind,
    Environment.prepend, inputs]
  simp only [PIR.Proc.bind_assoc]
  change (PIR.Proc.call (I := observedInterface F G) (.mark "s0") _ :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) outerSignature.outputs)) =
    PIR.Proc.call (I := observedInterface F G) (.mark "s0") _
  congr 1
  funext ignored
  apply congrArg₂ (PIR.Proc.bind (I := observedInterface F G)
    (A := Values (Component (assignment F G)) runSignature.outputs)
    (B := Values (Component (assignment F G)) outerSignature.outputs))
  · exact (run_agrees ⟨some "s0", roleSubstitution [2, 0]⟩ 2
      (RepeatServiceLaws.inputs (some count) none none)).trans
      (RepeatServiceLaws.permuted_receiver (some "s0") count bound none none)
  · funext values
    cases values with
    | cons a rest =>
      cases rest with
      | cons b rest => cases rest; rfl

/-- The third role never enters the applied repeat and keeps its independent input. -/
theorem outside_participant (count : Option Nat) (outside : Option F)
    (first second : Option Nat) :
    program.participant F G 1 (inputs count outside first second) =
      .done (.cons none (.cons outside (.cons none .nil))) := by
  change (invokeProtocol (unit.protocolTable F G) outerSignature {} 1
    (inputs count outside first second)).interpret forgetSites = _
  rw [outer_body_view]
  rfl

end ZkcExamples.Structured.RepeatServiceWrapperLaws
