module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCaller
public import Zkc.Source.TypedABI
public import ZkcSecurity.Examples.Components.GkrRoundsBindingInvocation
public import ZkcSecurity.Examples.Components.GkrCallerRealization

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

/-- Semantic fixture values enter through the generated frame constructor. -/
def frame (outputs : List F) (rho claim : F) (service : Nat) :
    protocol1Role1Frame (F := F) (G := G) :=
  protocol1Role1MakeFrame (.cons (some claim) .nil)
    (.cons (some [rho]) (.cons none .nil)) (.cons (some []) .nil)
    (some inputs) (some outputs) (some stackedAdd) (some stackedMul)
    (some 2) (some 1) (some 1) (some service)

abbrev leftContext := firstLeftContext

theorem left_distinct (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) :
    RosterDistinct (leftContext ctx) 1 2 := by
  apply RosterDistinct.ofSeparate
  change ctx.roles 0 ≠ ctx.roles 1
  · exact distinct 0 (by decide) (by decide)
  · decide

abbrev leftReturn := Values (Component (assignment F G)) GkrRoundsBinding.spec.state
abbrev layerReturn := Values (Component (assignment F G)) layerSpec.state
abbrev finalReturn := Values (Component (assignment F G)) definition1.outputs

def leftMask (ctx : ProtocolContext) (result : leftReturn (F := F) (G := G)) :=
  maskValues ((leftContext ctx).roles 1)
    ((leftContext ctx).mapScopes definition0.outputScopes) result

/-- This is the generated continuation, followed by the unchanged remaining
layer and root suffix. It consumes the complete callee result and frame. -/
def continuation (ctx : ProtocolContext) (outputs : List F) (rho claim : F) (service : Nat)
    (result : leftReturn (F := F) (G := G)) :
    PIR.Process (participantInterface F G) (finalReturn (F := F) (G := G)) :=
  (firstLeftContinuation ctx (some 0) (some [rho]) none (some claim)
    (some inputs) (some stackedAdd) (some stackedMul) (some 2) (some 1)
    (some 1) (some service) (leftMask ctx result)).bind fun layer =>
      (protocol1Role1Resume ctx (frame outputs rho claim service) 1 layer).bind
        (protocol1Role1After ctx (frame outputs rho claim service))

theorem first_callback (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (outputs : List F) (rho claim : F) (service : Nat) :
    protocol1Role1First (F := F) (G := G) ctx (frame outputs rho claim service) =
      firstLeft ctx (some 0) (some [rho]) none (some claim) (some inputs)
        (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service) := by
  let input : Values (Component (assignment F G))
      (.index :: (layerSpec.state ++ layerSpec.captures)) :=
    .cons (some 0) (.cons (some [rho]) (.cons none (.cons (some claim)
      (.cons (some inputs) (.cons (some stackedAdd) (.cons (some stackedMul)
        (.cons (some 2) (.cons (some 1) (.cons (some 1) (.cons (some service) .nil))))))))))
  have inputEq : protocol1Role1FirstInput ctx (frame (G := G) outputs rho claim service) = input := by
    simp [layerSpec, protocol1Role1FirstInput, frame, protocol1Role1MakeFrame, input,
      mask_cons, maskValues, ProtocolContext.mapScopes, Participant.restrict,
      TypedABI.get_cons_here, TypedABI.get_cons_there, Values.append]
  change ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx
    (ctx.roles 1)).callback layerSpec protocol1Role1Callback1Body)
    (protocol1Role1FirstInput ctx (frame outputs rho claim service)) = _
  rw [inputEq]
  exact congrFun (protocol1Role1Callback1_function ctx distinct) input

/-- Direct source call equation. No mathematical representation or assumed
source equation occurs among its hypotheses. -/
theorem first_left_call (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (outputs : List F) (rho claim : F) (service : Nat) :
    (protocol1Role1Loop (F := F) (G := G) ctx (frame outputs rho claim service)).bind
      (protocol1Role1After ctx (frame outputs rho claim service)) =
    (protocol0Role1Process (leftContext ctx) none none none none
      (some claim) (some 1) (some service)).bind (continuation ctx outputs rho claim service) := by
  rw [protocol1Role1_first ctx _ 1 rfl (by simp) (by decide), first_callback ctx distinct]
  unfold firstLeft
  rw [protocol1Role1Callback1_call]
  change (((invokeProtocol _ definition0.signature (leftContext ctx)
    ((leftContext ctx).roles 1) _).bind _).bind _).bind _ = _
  rw [protocol0Role1_invocation _ (left_distinct ctx distinct)]
  unfold protocol0Role1View
  have separate := (left_distinct ctx distinct) 0 (by decide) (by decide)
  have inputScopes : definition0.inputScopes = [[0], [0], [0], [0], [1], [0, 1], [1]] := by kernel_rfl
  simp only [inputScopes, protocol1Role1Callback1CallInput, mask_cons, maskValues, ProtocolContext.mapScopes,
    List.map_cons, List.map_nil, List.tail_cons, List.headD_cons, List.contains_cons, List.contains_nil, beq_self_eq_true,
    Bool.or_false, Bool.or_true, Participant.restrict, ite_true, TypedABI.get_cons_here, TypedABI.get_cons_there, PIR.Process.bind_assoc,
    PIR.Process.bind, ite_self]
  rfl

end ZkcSecurity.Examples.Components.GkrCallerBinding
