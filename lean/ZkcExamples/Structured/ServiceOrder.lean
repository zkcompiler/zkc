module

public import ZkcExamples.Structured.ServiceOrderViews
public import Zkc.Source.Structured.OpenLaws

@[expose] public section

/-! Exact observed and plain processes of the complete service-order source.
These equations quantify over actual service handles and independent replies;
they assert neither a provider distribution nor native correspondence. -/
namespace ZkcExamples.Structured.ServiceOrder

set_option smartUnfolding false
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies ServiceOrderViews

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def inputs (go : Option Bool) (first second : Option Nat) :
    Values (Component (assignment F G)) inputTypes :=
  .cons go (.cons first (.cons second .nil))

def servicesInput (first second : Option Nat) :
    Values (Component (assignment F G)) serviceTypes :=
  .cons first (.cons second .nil)

theorem draw_body_view (context : ProtocolContext) (self : Nat)
    (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) drawSignature context self
        (servicesInput first second) =
      (drawBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes drawSignature.inputScopes)
          (servicesInput first second)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes drawSignature.outputScopes) results)) :=
  unit.protocol_body_view_as drawDefinition draw_member drawSignature draw_signature
    drawBody draw_raw context self (servicesInput first second)

theorem run_body_view (context : ProtocolContext) (self : Nat)
    (go : Option Bool) (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature context self
        (inputs go first second) =
      (runBody.denote
        (participantMeaning (unit.tables F G) self (unit.protocolTable F G) context)
        (maskValues self (context.mapScopes runSignature.inputScopes)
          (inputs go first second)).get).bind
        (fun results => .done (maskValues self
          (context.mapScopes runSignature.outputScopes) results)) :=
  unit.protocol_body_view_as runDefinition run_member runSignature run_signature
    runBody run_raw context self (inputs go first second)

/-- A literal expected trace expression, retaining every lowered source mark. -/
def verifierObserved (parent : Option String) (go : Bool) (first second : Nat) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) resultTypes) :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s3"))
  .call (.mark (site "s0")) <| fun _ =>
  .call (.action (.query (site "s0") "bls12-381.fr" (.cons first .nil))) <| fun (before : F) =>
  .call (.mark (site "s2")) <| fun _ =>
  if go then
    .call (.mark (site "s3")) <| fun _ =>
    .call (.mark (child "s0")) <| fun _ =>
    .call (.action (.query (child "s0") "bls12-381.fr" (.cons first .nil))) <| fun (a : F) =>
    .call (.mark (child "s2")) <| fun _ =>
    .call (.action (.query (child "s2") "bls12-381.fr" (.cons second .nil))) <| fun (b : F) =>
    .call (.mark "") <| fun _ =>
    .call (.mark (child "s5_0")) <| fun _ =>
    .call (.action (.send (ty := fieldType) (child "s5_0") 0 (a + b))) <| fun _ =>
    .call (.mark "") <| fun _ =>
    .call (.mark "") <| fun _ =>
    .call (.mark (site "s6")) <| fun _ =>
    .call (.action (.query (site "s6") "bls12-381.fr" (.cons first .nil))) <| fun (after : F) =>
    .call (.mark "") <| fun _ =>
    .call (.mark "") <| fun _ =>
    .done (.cons none (.cons (some (before + (a + b) + after)) .nil))
  else .halt .reject

/-- The receiver's reply is independent of the sender's arithmetic and services. -/
def receiverObserved (parent : Option String) :
    PIR.Proc (observedInterface F G) (Values (Component (assignment F G)) resultTypes) :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s3"))
  .call (.mark (site "s0")) <| fun _ =>
  .call (.mark (site "s2")) <| fun _ =>
  .call (.mark (site "s3")) <| fun _ =>
  .call (.mark (child "s0")) <| fun _ =>
  .call (.mark (child "s2")) <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark (child "s5_0")) <| fun _ =>
  .call (.action (.receive fieldType (child "s5_0") 1)) <| fun received =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark (site "s6")) <| fun _ =>
  .call (.mark "") <| fun _ =>
  .call (.mark "") <| fun _ =>
  .done (.cons (some received) (.cons none .nil))

/-- Ordered actions after erasing internal marks; qualified action sites remain. -/
def verifierProcess (parent : Option String) (go : Bool) (first second : Nat) :
    PIR.Proc (participantInterface F G) (Values (Component (assignment F G)) resultTypes) :=
  let site := qualifyProtocolSite parent
  let child := qualifyProtocolSite (some (site "s3"))
  .call (.query (site "s0") "bls12-381.fr" (.cons first .nil)) <| fun (before : F) =>
  if go then
    .call (.query (child "s0") "bls12-381.fr" (.cons first .nil)) <| fun (a : F) =>
    .call (.query (child "s2") "bls12-381.fr" (.cons second .nil)) <| fun (b : F) =>
    .call (.send (ty := fieldType) (child "s5_0") 0 (a + b)) <| fun _ =>
    .call (.query (site "s6") "bls12-381.fr" (.cons first .nil)) <| fun (after : F) =>
    .done (.cons none (.cons (some (before + (a + b) + after)) .nil))
  else .halt .reject

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem verifier_forget_marks (parent : Option String) (go : Bool) (first second : Nat) :
    (verifierObserved (F := F) (G := G) parent go first second).interpret forgetSites =
      verifierProcess parent go first second := by
  cases go <;> rfl

omit [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem receiver_forget_marks (parent : Option String) :
    (receiverObserved (F := F) (G := G) parent).interpret forgetSites =
      .call (.receive fieldType (qualifyProtocolSite
        (some (qualifyProtocolSite parent "s3")) "s5_0") 1)
        (fun received => .done (.cons (some received) (.cons none .nil))) := rfl

set_option smartUnfolding true in
theorem contextual_verifier (parent : Option String) (go : Bool) (first second : Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, id⟩ 1
        (inputs (some go) (some first) (some second)) =
      verifierObserved parent go first second := by
  have draw_view := draw_body_view (F := F) (G := G)
  simp only [servicesInput] at draw_view
  rw [run_body_view]
  simp only [runBody, Region.denote, participantMeaning, participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, observedSites, PIR.Proc.bind,
    Environment.prepend, inputs, draw_view]
  cases parent <;> cases go <;> rfl

set_option smartUnfolding true in
theorem contextual_receiver (parent : Option String) (go : Option Bool)
    (first second : Option Nat) :
    invokeProtocol (unit.protocolTable F G) runSignature ⟨parent, id⟩ 0
        (inputs go first second) = receiverObserved parent := by
  have draw_view := draw_body_view (F := F) (G := G)
  simp only [servicesInput] at draw_view
  rw [run_body_view]
  simp only [runBody, Region.denote, participantMeaning, participantMeaningWith,
    protocolOperationWith, Operands.eval, Regions.denote, observedSites, PIR.Proc.bind,
    Environment.prepend, inputs, draw_view]
  cases parent <;> rfl

theorem observed_verifier (go : Bool) (first second : Nat) :
    program.observed F G 1 (inputs (some go) (some first) (some second)) =
      verifierObserved none go first second :=
  contextual_verifier none go first second

theorem observed_receiver (go : Option Bool) (first second : Option Nat) :
    program.observed F G 0 (inputs go first second) = receiverObserved none :=
  contextual_receiver none go first second

theorem verifier_participant (go : Bool) (first second : Nat) :
    program.participant F G 1 (inputs (some go) (some first) (some second)) =
      verifierProcess none go first second := by
  unfold Program.participant
  rw [observed_verifier]
  exact verifier_forget_marks none go first second

theorem receiver_participant (go : Option Bool) (first second : Option Nat) :
    program.participant F G 0 (inputs go first second) =
      .call (.receive fieldType "apply_2_s3_s5_0" 1)
        (fun received => .done (.cons (some received) (.cons none .nil))) := by
  unfold Program.participant
  rw [observed_receiver]
  exact receiver_forget_marks none

/-- The first draw is retained before the guard, with no child or suffix work. -/
theorem false_guard_observed (first second : Nat) :
    program.observed F G 1 (inputs (some false) (some first) (some second)) =
      .call (.mark "s0") (fun _ =>
        .call (.action (.query "s0" "bls12-381.fr" (.cons first .nil))) (fun _ =>
          .call (.mark "s2") (fun _ => .halt .reject))) := by
  rw [observed_verifier]
  rfl

end ZkcExamples.Structured.ServiceOrder
