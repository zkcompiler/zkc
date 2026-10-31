module

public import ZkcSecurityExamples.Components.GkrRoundsBinding
public import ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate

@[expose] public section
noncomputable section

/-! Exact bounded invocation of the imported Rounds role 1. The source's maximum,
optional count, runtime scopes and output permutation remain operational. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.GkrRoundsBinding
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
open ZkcSecurity.Families.Sumcheck
open GkrRoundsRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Complete entry selection is checked independently of its operational law. -/
def source_entry : Template.Association payload
    (ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.signature definition0.name)
    (ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.body 4) := by
  refine ⟨definition0, definition0_member, ?_, ?_⟩ <;> kernel_rfl

/-- The actual entry cannot select a different operational maximum under
an unchanged source body, even when its complete ABI still matches. -/
theorem source_maximum_exact (maximum : Nat)
    (same : definition0.raw =
      (ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.body maximum).erase) : maximum = 4 := by
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.maximum_eq_of_body_eq
    (same.symm.trans source_entry.body_eq)

/-- The generic source installer is applied to the original admitted entry,
including absent private inputs and the complete declaration output mask. -/
theorem source_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx (ctx.roles 1) input =
      ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.view payload.definitions definition0.name 4 ctx input := by
  exact ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.invocation
    payload definition0.name 4 source_entry ctx distinct input

/-- The original generated process uses the installed callback template.
This bridge reuses the source normalizer rather than its generated readable view. -/
theorem source_process (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (count service : Option Nat) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r point claim count service =
      ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation.process payload.definitions 4
        ctx a m l r point claim count service := by
  have callback : (Runs.uniform (helpers payload) (payload.plainProtocolTable F G)
      ctx (ctx.roles 1)).callback spec
      Zkc.Protocols.Gkr.Source.HelperBodies.roundsCallbackBody =
        ZkcSecurity.Bindings.Gkr.RoundsVerifierInstallation.callbackBody (G := G)
          payload.definitions ctx := by
    funext input
    exact ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.callback_source
      payload.definitions (payload.plainProtocolTable F G) ctx distinct input
  dsimp only [Zkc.Protocols.Gkr.Source.HelperBodies.roundsCallbackBody, spec, repeatSpec] at callback
  unfold protocol0Role1Process
  rw [callback]
  rfl

/-- Direct imported whole-Process equation. Mathematical representation facts
are intentionally absent: this binding is shared by both property consumers. -/
theorem verifier_binding (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r : Option (List F)) (claim : F) (service count : Nat) (bounded : count ≤ 4)
    {n : Nat} (raw : RawState F) (reference : GkrRoundsReference.State F (n + count)) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r (some []) (some claim) (some count) (some service) =
      ((program service).remaining count ctx (initial raw reference claim)).bind
        (fun final => .done (carried (G := G) final)) := by
  rw [source_process ctx distinct]
  exact ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation.verifier_binding
    payload.linked GkrRoundsBindingHelpers.bodies 4 ctx distinct a m l r claim service count bounded raw reference

/-- Missing or excessive source counts stop before any receive or query. -/
theorem missing_count (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r point claim none service = .halt .incomplete := by
  rw [source_process ctx distinct]
  exact ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation.missing_count
    payload.linked GkrRoundsBindingHelpers.bodies 4 ctx distinct a m l r point claim service

theorem above_maximum (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (service : Option Nat)
    (count : Nat) (large : 4 < count) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r point claim (some count) service =
      match point, claim with
      | some _, some _ => .halt .refused
      | _, _ => .halt .incomplete := by
  rw [source_process ctx distinct]
  exact ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation.above_maximum
    payload.linked GkrRoundsBindingHelpers.bodies 4 ctx distinct a m l r point claim service count large

/-- Zero rounds retains the complete Pending input and does not demand a
service handle. Missing Pending components still stop at the linear boundary.
All private output slots are masked even for present local private inputs. -/
theorem zero (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a m l r point : Option (List F)) (claim : Option F) (service : Option Nat) :
    protocol0Role1Process (F := F) (G := G) ctx a m l r point claim (some 0) service =
      match point, claim with
      | some point, some claim =>
        .done (.cons none (.cons none (.cons none (.cons none (.cons none
          (.cons (some point) (.cons (some claim) .nil)))))))
      | _, _ => .halt .incomplete := by
  rw [source_process ctx distinct]
  exact ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation.zero
    payload.linked GkrRoundsBindingHelpers.bodies 4 ctx distinct a m l r point claim service

end ZkcSecurity.Examples.Components.GkrRoundsBinding
