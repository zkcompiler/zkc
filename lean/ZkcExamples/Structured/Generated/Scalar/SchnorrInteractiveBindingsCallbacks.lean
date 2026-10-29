module

public import ZkcExamples.Structured.Generated.Scalar.SchnorrInteractiveBindings
public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! Generated complete callback views. -/
namespace ZkcExamples.Structured.Generated.Scalar.SchnorrInteractiveBindingsCallbacks
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Scalar.SchnorrInteractiveBindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

def callbackKeys : List LawKey := []

def callbackResults : LawResults (ringModel F G) callbackKeys where
  result := fun entry => entry.elim0

theorem callbackLaws_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
    LawsHold (helpers payload).toOn (callbackResults (F := F) (G := G)) input := by
  intro entry
  exact entry.elim0

noncomputable def protocol0Role0ReadableProcess (ctx : ProtocolContext) (b0 : (Option (G))) (_b1 : (Option (G))) (b2 : (Option (F))) (b3 : (Option (Nat))) (_b4 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  match b3 with
  | none =>
    .halt .incomplete
  | some b5 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "s0") "bls12-381.fr" (.cons (b5) .nil)) fun (b6 : F) =>
    match b0 with
    | none =>
      .halt .incomplete
    | some b7 =>
      .call (.send (ty := (.group "bls12-381.g1")) (qualifyProtocolSite (ctx).applicationPrefix "label_636f6d6d69746d656e74_0") ((ctx).roles 1) (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b6) (b7)))) fun _ =>
      .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 1)) fun (b8 : F) =>
      match b2 with
      | none =>
        .halt .incomplete
      | some b9 =>
        .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_726573706f6e7365_0") ((ctx).roles 1) (((b6) + (((b8) * (b9)))))) fun _ =>
        .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol0Role0_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 0 2) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (F))) (b3 : (Option (Nat))) (b4 : (Option (Nat))) :
    (protocol0Role0Process (F := F) (G := G) ctx b0 b1 b2 b3 b4) = (protocol0Role0ReadableProcess (F := F) (G := G) ctx b0 b1 b2 b3 b4) := by
  unfold protocol0Role0Process protocol0Role0ReadableProcess
  rfl

noncomputable def protocol0Role0ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role0ReadableProcess ctx ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here)))))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role0_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 0) input = protocol0Role0ReadableView ctx input := by
  refine (protocol0Role0_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role0_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))))

noncomputable def protocol0Role1ReadableProcess (ctx : ProtocolContext) (b0 : (Option (G))) (b1 : (Option (G))) (_b2 : (Option (F))) (_b3 : (Option (Nat))) (b4 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .call (.receive (.group "bls12-381.g1") (qualifyProtocolSite (ctx).applicationPrefix "label_636f6d6d69746d656e74_0") ((ctx).roles 0)) fun (b5 : G) =>
  match b4 with
  | none =>
    .halt .incomplete
  | some b6 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6368616c6c656e6765") "bls12-381.fr" (.cons (b6) .nil)) fun (b7 : F) =>
    .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 0) (b7)) fun _ =>
    .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_726573706f6e7365_0") ((ctx).roles 0)) fun (b8 : F) =>
    match b0 with
    | none =>
      match b1 with
      | none =>
        .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
      | some _b10 =>
        .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
    | some b9 =>
      match b1 with
      | none =>
        .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
      | some b11 =>
        .done ((.cons ((some (((Op.evalTotal (ringModel F G) (.groupEqual "bls12-381.g1") rfl (.cons (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b8) (b9))) (.cons (((b5) + (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b7) (b11))))) .nil))).get .here)))) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol0Role1_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 1 2) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (F))) (b3 : (Option (Nat))) (b4 : (Option (Nat))) :
    (protocol0Role1Process (F := F) (G := G) ctx b0 b1 b2 b3 b4) = (protocol0Role1ReadableProcess (F := F) (G := G) ctx b0 b1 b2 b3 b4) := by
  unfold protocol0Role1Process protocol0Role1ReadableProcess
  rfl

noncomputable def protocol0Role1ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role1ReadableProcess ctx ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here)))))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role1_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 1) input = protocol0Role1ReadableView ctx input := by
  refine (protocol0Role1_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role1_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))))

end
end ZkcExamples.Structured.Generated.Scalar.SchnorrInteractiveBindingsCallbacks
