module

public import ZkcSecurityExamples.Components.GkrRoundsBindingHelpers
public import ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation

@[expose] public section
noncomputable section

/-! The actual imported Rounds verifier as one shared Sumcheck component.
Ghost factors retain off-cube observations; runtime private slots retain their
actual absent masks. The equation is over the complete open Process. -/
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBinding
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
open ZkcExamples.Structured.Generated.Bindings.GkrRounds (payload)
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
open ZkcSecurity.Families.Sumcheck
open GkrRoundsRealization GkrRoundsGateRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- A small dependent-type presentation of the actual generated callback. -/
def callback (ctx : ProtocolContext) (point : Option (List F))
    (claim : Option F) (service : Option Nat) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) spec.state) :=
  (receive ctx).bind fun decoded =>
    match decoded with
    | none => .halt .refused
    | some (c0, c1, c2) =>
      match claim with
      | none => .halt .incomplete
      | some claim =>
        if claim = c0 + c0 + c1 + c2 then
          match service with
          | none => .halt .incomplete
          | some service =>
            .call (query ctx service) fun (r : F) =>
              (delivery ctx r).bind fun _ =>
                (Participant.owned (ctx.roles 1) (ctx.roles 1)
                  (invoke (helpers (F := F) (G := G) payload).toOn.closed
                    GkrRoundsHelpers.appendHelper)
                  (.cons point (.cons (some r) .nil))).bind fun appended =>
                  .done (.cons none (.cons none (.cons none (.cons none (.cons none
                    (.cons (appended.get .here) (.cons (some (c0 + r * (c1 + r * c2))) .nil)))))))
        else .halt .reject

theorem callback_source (ctx : ProtocolContext) (index : Option Nat)
    (a m l r pp point : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Callback0Process (F := F) (G := G) ctx index a m l r pp point claim service =
      callback ctx point claim service := by
  rfl

/-- The arbitrary coefficient replies precede the actual scalar boundary.
The append law is from the admitted full body, not an opaque helper assertion. -/
theorem callback_equation (ctx : ProtocolContext) (index : Option Nat)
    (a m l r pp : Option (List F)) (point : List F) (claim : F) (service : Nat) :
    protocol0Role1Callback0Process (F := F) (G := G) ctx index a m l r pp
      (some point) (some claim) (some service) =
    (receive (G := G) ctx).bind (fun decoded =>
      match decoded with
      | none => .halt .refused
      | some message =>
        if (Message.coefficientTriples F).boundary message = claim then
          .call (query (F := F) (G := G) ctx service) fun (challenge : F) =>
            (delivery (G := G) ctx challenge).bind fun _ =>
              .done (runtime (G := G) (point ++ [challenge])
                ((Message.coefficientTriples F).evaluate message challenge))
        else .halt .reject) := by
  exact ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation.callback_equation
    payload.linked GkrRoundsBindingHelpers.bodies ctx point claim service

/-- Residual source loop after its original maximum check. Its shifted index
and optional immutable service capture are the actual source arguments. -/
def actualRemaining (service : Nat) (ctx : ProtocolContext) {n : Nat}
    (count start : Nat) (s : State F (n + count)) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) spec.state) :=
  Repeat.loop spec ctx (ctx.roles 1) (.cons (some service) .nil)
    (fun args => protocol0Role1Callback0Process ctx
      (args.get .here) (args.get (.there .here)) (args.get (.there (.there .here)))
      (args.get (.there (.there (.there .here))))
      (args.get (.there (.there (.there (.there .here)))))
      (args.get (.there (.there (.there (.there (.there .here))))))
      (args.get (.there (.there (.there (.there (.there (.there .here)))))))
      (args.get (.there (.there (.there (.there (.there (.there (.there .here))))))))
      (args.get (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))
    start count (carried s)

/-- One whole binding for both consumers, over arbitrary replies and halts. -/
theorem remaining_binding (service : Nat) (ctx : ProtocolContext) (_distinct : RosterDistinct ctx 1 2)
    {n : Nat} (count start : Nat) (s : State F (n + count)) :
    actualRemaining (G := G) service ctx count start s =
      ((program service).remaining count ctx s).bind (fun final => .done (carried (G := G) final)) := by
  exact ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation.remaining_binding
    payload.linked GkrRoundsBindingHelpers.bodies service ctx count start s

end ZkcSecurity.Examples.Components.GkrRoundsBinding
