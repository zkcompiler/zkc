module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
public import Zkc.Source.TypedABI
public import Zkc.Source.Structured.ContractBoundary
public import ZkcSecurityExamples.Components.GkrRoundsBindingInvocation
public import ZkcSecurityExamples.Components.GkrCallerRealization

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Examples.Components.GkrCallerBinding
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Bindings.GkrRounds
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
open GkrCallerRealization

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem mask_cons {Value : Ty → Type} {ty : Ty} {types : List Ty}
    (self : Nat) (scopes : List (List Nat)) (head : Option (Value ty))
    (tail : Values (Component Value) types) :
    maskValues self scopes (.cons head tail) =
      .cons (Participant.restrict ((scopes.headD []).contains self) head)
        (maskValues self scopes.tail tail) := rfl

/-- The admitted input guards and every frame slot remain in the generated
constructor. The optional output-loop result and helper results are explicit. -/
def outputFrame (outputs : List F) (service : Nat)
    (point : Values (Component (assignment F G)) outputSpec.state)
    (claim : Values (Component (assignment F G)) [.field "bls12-381.fr"])
    (layerClaim : Values (Component (assignment F G))
      [.vector "bls12-381.fr", .field "bls12-381.fr"]) :
    protocol2Role1Frame (F := F) (G := G) :=
  protocol2Role1MakeFrame layerClaim claim point (.cons (some []) .nil)
    false (.cons (some false) .nil) (.cons (some 2) .nil)
    true (.cons (some true) .nil) (.cons (some 4) .nil)
    (.cons (some 3) .nil) (.cons (some 2) .nil)
    true (.cons (some true) .nil) (.cons (some 4) .nil)
    (.cons (some 3) .nil) (.cons (some 2) .nil)
    true (.cons (some true) .nil) true (.cons (some true) .nil)
    false (.cons (some false) .nil) false (.cons (some false) .nil)
    (some inputs) (some outputs) (some stackedAdd) (some stackedMul)
    (some 2) (some 1) (some 1) (some service)

/-- Semantic fixture values enter through the complete generated frame. -/
def frame (outputs : List F) (rho claim : F) (service : Nat) :
    protocol2Role1Frame (F := F) (G := G) :=
  outputFrame outputs service (.cons (some [rho]) (.cons none .nil))
    (.cons (some claim) .nil) (.cons (some [rho]) (.cons (some claim) .nil))

/-- The complete generated frame after opening the layer claim and constructing
its Pending input; both original inputs and produced components are retained. -/
def leftFrame (rho claim : F) (service : Nat) :
    protocol2Role1Callback1SetupFrame (F := F) (G := G) :=
  protocol2Role1Callback1MakeSetupFrame
    (.cons (some []) (.cons (some claim) .nil))
    (.cons (some [rho]) (.cons (some claim) .nil))
    (some 0) none (some [rho]) (some claim) (some inputs)
    (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service)

theorem left_setup (ctx : ProtocolContext) (rho claim : F) (service : Nat) :
    protocol2Role1Callback1Setup (F := F) (G := G) ctx (some 0) none (some [rho]) (some claim)
      (some inputs) (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service) =
      .done (leftFrame rho claim service) := by
  unfold protocol2Role1Callback1Setup
  rw [GkrRoundsBindingHelpers.owned_layer_open]
  simp only [PIR.Process.bind, Values.get]
  rw [GkrRoundsBindingHelpers.owned_pending]
  rfl

abbrev leftContext := firstLeftContext

theorem left_distinct (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) :
    RosterDistinct (leftContext ctx) 1 2 := by
  apply RosterDistinct.ofSeparate
  change ctx.roles 0 ≠ ctx.roles 1
  · exact distinct 0 (by decide) (by decide)
  · decide

abbrev leftReturn := Values (Component (assignment F G)) GkrRoundsBinding.spec.state
abbrev layerReturn := Values (Component (assignment F G)) layerSpec.state
abbrev finalReturn := Values (Component (assignment F G)) definition2.outputs

def leftMask (ctx : ProtocolContext) (result : leftReturn (F := F) (G := G)) :=
  maskValues ((leftContext ctx).roles 1)
    ((leftContext ctx).mapScopes definition0.outputScopes) result

/-- This is the generated continuation, followed by the unchanged remaining
layer and root suffix. It consumes the complete callee result and frame. -/
def continuation (ctx : ProtocolContext) (outputs : List F) (rho claim : F) (service : Nat)
    (result : leftReturn (F := F) (G := G)) :
    PIR.Process (participantInterface F G) (finalReturn (F := F) (G := G)) :=
  (firstLeftContinuation ctx (leftFrame rho claim service) (leftMask ctx result)).bind fun layer =>
      (protocol2Role1Resume ctx (frame outputs rho claim service) 1 layer).bind
        (protocol2Role1After ctx (frame outputs rho claim service))

theorem first_callback (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (outputs : List F) (rho claim : F) (service : Nat) :
    protocol2Role1First (F := F) (G := G) ctx (frame outputs rho claim service) =
      firstLeft ctx (some 0) none (some [rho]) (some claim) (some inputs)
        (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service) := by
  change ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx
    (ctx.roles 1)).callback layerSpec protocol2Role1Callback1Body)
    (protocol2Role1FirstInput ctx (frame outputs rho claim service)) = _
  rw [protocol2Role1Callback1_function ctx distinct]
  simp [protocol2Role1FirstInput, frame, outputFrame, protocol2Role1MakeFrame,
    maskValues, ProtocolContext.mapScopes, Participant.restrict, Values.append]

/-- Direct source call equation. No mathematical representation or assumed
source equation occurs among its hypotheses. The checked source association
supplies the callee body and both masks; the complete caller suffix is retained. -/
theorem first_left_call (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (outputs : List F) (rho claim : F) (service : Nat) :
    (protocol2Role1Loop (F := F) (G := G) ctx (frame outputs rho claim service)).bind
      (protocol2Role1After ctx (frame outputs rho claim service)) =
    (protocol0Role1Process (leftContext ctx) none none none none (some [])
      (some claim) (some 1) (some service)).bind (continuation ctx outputs rho claim service) := by
  rw [protocol2Role1_first ctx _ 1 rfl (by simp) (by decide), first_callback ctx distinct]
  unfold firstLeft
  rw [protocol2Role1Callback1_setup_split, left_setup]
  simp only [PIR.Process.bind, PIR.Process.bind_assoc]
  change (invokeProtocol _ definition0.signature (leftContext ctx)
    ((leftContext ctx).roles 1) _).bind _ = _
  rw [GkrRoundsBinding.source_invocation _ (left_distinct ctx distinct),
    GkrRoundsBinding.source_process _ (left_distinct ctx distinct)]
  unfold ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.view
  simp [contract_mask_get, ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate.signature,
    Zkc.Protocols.Gkr.Source.HelperBodies.roundsProtocolSignature,
    protocol2Role1Callback1SetupInput, leftFrame, protocol2Role1Callback1MakeSetupFrame,
    ProtocolContext.mapScopes, Participant.restrict, Var.index, PIR.Process.bind_assoc, PIR.Process.bind]
  rfl

end ZkcSecurity.Examples.Components.GkrCallerBinding
