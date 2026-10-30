module

public import ZkcSecurityExamples.Components.GkrCallerPrefix
public import ZkcSecurityExamples.Components.GkrRoundsResidual

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000

/-! Conditional composition at the first actual left invocation. The remaining
right invocation, line restriction, later layer and final source guard are the
unchanged generated continuation. No terminal GKR security theorem is supplied. -/
namespace ZkcSecurity.Examples.Components.GkrCallerResidual
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.Bindings Zkc.Source.Structured.NormalForm
open OracleComp OracleSpec Zkc.Transcript Zkc.Obligations ZkcSecurity.Obligations
open ZkcSecurity.Families.Sumcheck
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
open GkrCallerRealization GkrCallerBinding

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]
  {E P : Type} {Raw : E → Type} [∀ event, SampleableType (Raw event)]
  {absorb : Interface (participantInterface F G) E P Raw}
  {charge : List E → E → ENNReal}

/-- The only security obligation after the left call. It quantifies over every
reached history and complete returned ABI satisfying the anchored dimension-one
residual. It does not assume a whole source-process equation or honest messages. -/
def ContinuationContract (ctx : ProtocolContext) (service : Nat)
    (Final : List E → finalReturn (F := F) (G := G) → Prop) : Type 1 :=
  ∀ (rho : F) reached output,
    GkrRoundsResidual.NoReturn (n := 1) service
      (GkrRoundsBinding.initial (raw rho) (reference rho) (wrongClaim rho)) output →
    Derivation absorb (boundedEscape charge) Final reached
      (continuation ctx wrongOutputs rho (wrongClaim rho) service output)

/-- First call only: the existing Rounds theorem, specialized at count one,
retains a mathematical residual variable and the exact one-element point. -/
def left_residual (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (rho : F) (service : Nat)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (history : List E) :
    Derivation absorb (boundedEscape charge)
      (fun _ output => GkrRoundsResidual.NoReturn (n := 1) service
        (GkrRoundsBinding.initial (raw rho) (reference rho) (wrongClaim rho)) output)
      history (protocol0Role1Process (leftContext ctx) none none none none (some [])
        (some (wrongClaim rho)) (some 1) (some service)) :=
  GkrRoundsResidual.verifier_residual service 1 (by decide) (leftContext ctx)
    (left_distinct ctx distinct) none none none none (raw rho) (reference rho)
    (wrongClaim rho) (represented rho) (wrong_control rho) queries sampling history

/-- The discharged actual call equation binds precisely the original suffix. -/
def layer_conditional (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (rho : F) (service : Nat)
    (Final : List E → finalReturn (F := F) (G := G) → Prop)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (consumer : ContinuationContract (absorb := absorb) (charge := charge) ctx service Final)
    (history : List E) :
    Derivation absorb (boundedEscape charge) Final history
      ((protocol2Role1Loop ctx (frame wrongOutputs rho (wrongClaim rho) service)).bind
        (protocol2Role1After ctx (frame wrongOutputs rho (wrongClaim rho) service))) :=
  ((left_residual ctx distinct rho service queries sampling history).bind
    (continuation ctx wrongOutputs rho (wrongClaim rho) service)
    (consumer rho)).transport (first_left_call ctx distinct wrongOutputs rho (wrongClaim rho) service)

/-- Explicit absorption laws for the actual output-point query and its actual
source delivery. Decoding is unrestricted, including a failed raw decode. -/
structure OutputInterface (ctx : ProtocolContext) (service : Nat)
    (absorb : Interface (participantInterface F G) E P Raw) where
  event : E
  decode : Raw event → Option F
  queried : absorb (outputQuery ctx service) = .query event decode
  delivery : F → E
  delivered : ∀ rho, absorb (outputDelivery ctx rho) = .send (delivery rho) ()

/-- Conditional theorem about the entire admitted Gkr role-1 process on the
wrong-output fixture. The symbolic output point is sampled by the actual
prologue. The continuation and conditional query/interface laws are explicit.
The charge remains an event/history function; no aggregate scalar bound is
inferred from the local degree-two bound. -/
def first_left_conditional (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (service : Nat) (Final : List E → finalReturn (F := F) (G := G) → Prop)
    (output : OutputInterface ctx service absorb)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (consumer : ContinuationContract (absorb := absorb) (charge := charge) ctx service Final)
    (history : List E) :
    Derivation absorb (boundedEscape charge) Final history
      (protocol2Role1Process (F := F) (G := G) ctx (some inputs) (some wrongOutputs)
        (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service)) := by
  apply Derivation.transport (caller_equation ctx distinct 121 31 service)
  refine .query output.queried (fun _ => False) ?_ ?_
  · change Pr{let _ ← $ᵗ (Raw output.event)}[False] ≤ charge history output.event
    simp
  · intro rawAnswer rho decoded outside
    refine .send (output.delivered rho) ?_
    exact (left_residual (F := F) (G := G) ctx distinct (show F from rho) service queries sampling _).bind
      (continuation ctx wrongOutputs rho (wrongClaim rho) service) (consumer rho)

/-- The same conditional derivation at the declared invocation boundary,
including the exact outer return mask. -/
def first_left_invocation_conditional
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (service : Nat) (Final : List E → finalReturn (F := F) (G := G) → Prop)
    (output : OutputInterface ctx service absorb)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (consumer : ContinuationContract (absorb := absorb) (charge := charge) ctx service
      (fun reached result => Final reached (callerMask ctx result)))
    (history : List E) :
    Derivation absorb (boundedEscape charge) Final history
      (invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx (ctx.roles 1)
        (callerInput wrongOutputs service)) :=
  ((first_left_conditional ctx distinct service _ output queries sampling consumer history).bind
    (fun result => .done (callerMask ctx result))
    (fun _ _ holds => .done holds)).transport (fixture_invocation ctx distinct wrongOutputs service)

/-- Conditional charged partial safety for the actual invocation. This uses
the same explicit continuation and sampler premises as the derivation. -/
theorem first_left_invocation_doomed
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (service : Nat) (Final : List E → finalReturn (F := F) (G := G) → Prop)
    (output : OutputInterface ctx service absorb)
    (queries : QueryInterface (GkrRoundsBinding.program (F := F) (G := G) service) absorb)
    (sampling : queries.ConditionalBound (GkrRoundsBinding.representation service) 2 2 charge)
    (consumer : ContinuationContract (absorb := absorb) (charge := charge) ctx service
      (fun reached result => Final reached (callerMask ctx result)))
    (history : List E) :
    (reduction absorb Final charge).doomed history
      (invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx (ctx.roles 1)
        (callerInput wrongOutputs service)) :=
  derived_doomed
    (first_left_invocation_conditional ctx distinct service Final output queries sampling consumer history)

end ZkcSecurity.Examples.Components.GkrCallerResidual
