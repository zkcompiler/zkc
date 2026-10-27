module

public import ZkcSecurity.Examples.Components.GkrCallerBinding
public import ZkcSecurity.Examples.Components.GkrCallerSource
public import Zkc.Source.Structured.Labels

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

abbrev outputQuery (ctx : ProtocolContext) (service : Nat) : (participantInterface F G).Op :=
  .query (qualifyProtocolSite ctx.applicationPrefix (encodedLabel "output")) "bls12-381.fr" (.cons service .nil)
abbrev outputDelivery (ctx : ProtocolContext) (rho : F) : (participantInterface F G).Op :=
  .send (ty := .field "bls12-381.fr")
    (qualifyProtocolSite ctx.applicationPrefix (encodedLabel "output_delivery" ++ "_0")) (ctx.roles 0) rho

/-- Exact output query, delivery and source-computed frame. Stops in either
operation bypass the complete layer and final-check suffix. -/
def prologue (ctx : ProtocolContext) (a b : F) (service : Nat) :
    PIR.Process (participantInterface F G) (protocol2Role1Frame (F := F) (G := G)) :=
  .call (outputQuery ctx service) fun (rho : F) =>
  .call (outputDelivery ctx rho) fun _ =>
  .done (frame [a, b] rho ((1 - rho) * a + rho * b) service)

theorem prefix_equation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a b : F) (service : Nat) :
    protocol2Role1Prefix (F := F) (G := G) ctx (some inputs) (some [a, b])
      (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service) =
      prologue ctx a b service := by
  have admitted :
      protocol2Role1Prefix (F := F) (G := G) ctx (some inputs) (some [a, b])
        (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service) =
      (denoteRepeat outputSpec ctx (ctx.roles 1) (some 1)
        (.cons (some []) (.cons none .nil)) (.cons (some service) .nil)
        ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx
          (ctx.roles 1)).callback outputSpec outputBody)).bind (fun point =>
        (Participant.owned (ctx.roles 1) (ctx.roles 1)
          (invoke (helpers payload).toOn.closed evaluateHelper)
          (.cons (some [a, b]) (.cons (point.get .here) .nil))).bind fun claim =>
        (Participant.owned (ctx.roles 1) (ctx.roles 1)
          (invoke (helpers payload).toOn.closed GkrCallerSource.layerClaimHelper)
          (.cons (point.get .here) (.cons (claim.get .here) .nil))).bind fun layerClaim =>
        .done (outputFrame [a, b] service point claim layerClaim)) := by
    unfold protocol2Role1Prefix
    simp only [Participant.owned, ite_true]
    kernel_rfl
  rw [admitted]
  rw [repeat_admitted _ _ _ _ _ _ _ (by simp) (by decide)]
  rw [Repeat.loop_succ, Repeat.step_equation]
  rw [protocol2Role1Callback0_function ctx distinct]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, Repeat.loop_zero]
  simp only [maskValues, ProtocolContext.mapScopes, Participant.restrict,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.append,
    protocol2Role1Callback0Process]
  simp only [PIR.Process.bind, PIR.Process.bind_assoc]
  unfold prologue
  congr 1
  funext rho
  congr 1
  funext delivered
  rw [GkrRoundsBindingHelpers.owned_append]
  simp only [mask_cons, maskValues, List.map_cons, List.map_nil, List.headD_cons,
    List.tail_cons, List.contains_cons, List.contains_nil, beq_self_eq_true,
    Bool.or_false, Participant.restrict, ite_true, List.nil_append,
    PIR.Process.bind, TypedABI.get_cons_here]
  erw [GkrCallerSource.owned_evaluate_pair]
  simp only [PIR.Process.bind, Values.get, ite_self]
  rw [GkrCallerSource.owned_layer_claim]
  rfl


/-- The enclosing generated source role process, including its prologue and
complete continuation. The only fixed inputs are the finite fixture values. -/
theorem caller_equation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (a b : F) (service : Nat) :
    protocol2Role1Process (F := F) (G := G) ctx (some inputs) (some [a, b])
      (some stackedAdd) (some stackedMul) (some 2) (some 1) (some 1) (some service) =
    .call (outputQuery ctx service) (fun (rho : F) =>
      .call (outputDelivery ctx rho) (fun _ =>
        (protocol0Role1Process (leftContext ctx) none none none none (some [])
          (some ((1 - rho) * a + rho * b)) (some 1) (some service)).bind
          (continuation ctx [a, b] rho ((1 - rho) * a + rho * b) service))) := by
  rw [protocol2Role1_split, prefix_equation ctx distinct]
  unfold prologue
  simp only [PIR.Process.bind]
  congr 1
  funext rho
  congr 1
  funext ignored
  exact first_left_call ctx distinct [a, b] rho _ service

/-- Full declared input ABI for the fixture, without projection paths. -/
def callerInput (outputs : List F) (service : Nat) :
    Values (Component (assignment F G)) definition2.inputs :=
  .cons (some inputs) (.cons (some outputs) (.cons (some stackedAdd)
    (.cons (some stackedMul) (.cons (some 2) (.cons (some 1)
      (.cons (some 1) (.cons (some service) .nil)))))))

def callerMask (ctx : ProtocolContext) (result : finalReturn (F := F) (G := G)) :=
  maskValues (ctx.roles 1) (ctx.mapScopes definition2.outputScopes) result

/-- The outer invocation's input and output masks remain in the theorem.
This is the admitted Gkr protocol, with the actual enclosing context. -/
theorem fixture_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (outputs : List F) (service : Nat) :
    invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx (ctx.roles 1)
      (callerInput outputs service) =
    (protocol2Role1Process ctx (some inputs) (some outputs) (some stackedAdd) (some stackedMul)
      (some 2) (some 1) (some 1) (some service)).bind
        (fun result => .done (callerMask ctx result)) := by
  rw [protocol2Role1_invocation ctx distinct]
  unfold protocol2Role1View callerInput
  have scopes : definition2.inputScopes =
      [[0, 1], [1], [0, 1], [0, 1], [0, 1], [0, 1], [0, 1], [1]] := by kernel_rfl
  simp only [scopes, mask_cons, maskValues, ProtocolContext.mapScopes,
    List.map_cons, List.map_nil, List.tail_cons, List.headD_cons,
    List.contains_cons, List.contains_nil, beq_self_eq_true,
    Bool.or_true, Bool.or_false, Participant.restrict, ite_true,
    TypedABI.get_cons_here, TypedABI.get_cons_there]
  rfl

end ZkcSecurity.Examples.Components.GkrCallerBinding
