module

public import ZkcExamples.Structured.Generated.Scalar.SchnorrAndBindings
public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! Generated complete callback views. -/
namespace ZkcExamples.Structured.Generated.Scalar.SchnorrAndBindingsCallbacks
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open ZkcExamples.Structured.Generated.Scalar.SchnorrAndBindings
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

noncomputable def protocol0Role0ReadableProcess (ctx : ProtocolContext) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (G))) (b3 : (Option (G))) (b4 : (Option (F))) (b5 : (Option (F))) (b6 : (Option (Nat))) (_b7 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  match b6 with
  | none =>
    .halt .incomplete
  | some b8 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "s0") (.draw "bls12-381.fr") (.cons (b8) .nil)) fun (b9 : F) =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "s2") (.draw "bls12-381.fr") (.cons (b8) .nil)) fun (b10 : F) =>
    match b0 with
    | none =>
      .halt .incomplete
    | some b11 =>
      .call (.send (ty := (.group "bls12-381.g1")) (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f636f6d6d69746d656e74_0") ((ctx).roles 1) (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b9) (b11)))) fun _ =>
      match b2 with
      | none =>
        .halt .incomplete
      | some b12 =>
        .call (.send (ty := (.group "bls12-381.g1")) (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f636f6d6d69746d656e74_0") ((ctx).roles 1) (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b10) (b12)))) fun _ =>
        .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 1)) fun (b13 : F) =>
        match b4 with
        | none =>
          .halt .incomplete
        | some b14 =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f726573706f6e7365_0") ((ctx).roles 1) (((b9) + (((b13) * (b14)))))) fun _ =>
          match b5 with
          | none =>
            .halt .incomplete
          | some b15 =>
            .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f726573706f6e7365_0") ((ctx).roles 1) (((b10) + (((b13) * (b15)))))) fun _ =>
            (invoke ((helpers (F := F) (G := G) payload).toOn).components (⟨"zkl_58c3e21ec903d97998e4e0fbc53e6da76c0f9a6d09bd13bcd30d778eb1f644b0", .math, [(.group "bls12-381.g1"), (.field "bls12-381.fr"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.group "bls12-381.g1"), (.group "bls12-381.g1")], [.boolean]⟩ : Helper) (.cons ((some (b11))) (.cons (none) (.cons (none) (.cons (b1) (.cons (none) (.cons ((some (b12))) (.cons (none) (.cons (none) (.cons (b3) .nil)))))))))).bind fun (b16 : (Values (Component (assignment F G)) [.boolean])) =>
            .done ((.cons ((b16).get .here) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol0Role0_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 0 2) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (G))) (b3 : (Option (G))) (b4 : (Option (F))) (b5 : (Option (F))) (b6 : (Option (Nat))) (b7 : (Option (Nat))) :
    (protocol0Role0Process (F := F) (G := G) ctx b0 b1 b2 b3 b4 b5 b6 b7) = (protocol0Role0ReadableProcess (F := F) (G := G) ctx b0 b1 b2 b3 b4 b5 b6 b7) := by
  unfold protocol0Role0Process protocol0Role0ReadableProcess
  rfl

noncomputable def protocol0Role0ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role0ReadableProcess ctx ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there .here)))))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there .here))))))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there (.there .here))))))))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role0_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 0) input = protocol0Role0ReadableView ctx input := by
  refine (protocol0Role0_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role0_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there .here)))))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there .here))))))) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there (.there .here)))))))))

noncomputable def protocol0Role1ReadableProcess (ctx : ProtocolContext) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (G))) (b3 : (Option (G))) (_b4 : (Option (F))) (_b5 : (Option (F))) (_b6 : (Option (Nat))) (b7 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .call (.receive (.group "bls12-381.g1") (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f636f6d6d69746d656e74_0") ((ctx).roles 0)) fun (b8 : G) =>
  .call (.receive (.group "bls12-381.g1") (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f636f6d6d69746d656e74_0") ((ctx).roles 0)) fun (b9 : G) =>
  match b7 with
  | none =>
    .halt .incomplete
  | some b10 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6368616c6c656e6765") (.draw "bls12-381.fr") (.cons (b10) .nil)) fun (b11 : F) =>
    .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 0) (b11)) fun _ =>
    .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f726573706f6e7365_0") ((ctx).roles 0)) fun (b12 : F) =>
    .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f726573706f6e7365_0") ((ctx).roles 0)) fun (b13 : F) =>
    (invoke ((helpers (F := F) (G := G) payload).toOn).components (⟨"zkl_58c3e21ec903d97998e4e0fbc53e6da76c0f9a6d09bd13bcd30d778eb1f644b0", .math, [(.group "bls12-381.g1"), (.field "bls12-381.fr"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.group "bls12-381.g1"), (.group "bls12-381.g1")], [.boolean]⟩ : Helper) (.cons (b0) (.cons ((some (b12))) (.cons ((some (b8))) (.cons (b1) (.cons ((some (b11))) (.cons (b2) (.cons ((some (b13))) (.cons ((some (b9))) (.cons (b3) .nil)))))))))).bind fun (b14 : (Values (Component (assignment F G)) [.boolean])) =>
    .done ((.cons ((b14).get .here) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol0Role1_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 1 2) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (G))) (b3 : (Option (G))) (b4 : (Option (F))) (b5 : (Option (F))) (b6 : (Option (Nat))) (b7 : (Option (Nat))) :
    (protocol0Role1Process (F := F) (G := G) ctx b0 b1 b2 b3 b4 b5 b6 b7) = (protocol0Role1ReadableProcess (F := F) (G := G) ctx b0 b1 b2 b3 b4 b5 b6 b7) := by
  unfold protocol0Role1Process protocol0Role1ReadableProcess
  rfl

noncomputable def protocol0Role1ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role1ReadableProcess ctx ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there .here)))))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there .here))))))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there (.there .here))))))))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role1_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 1) input = protocol0Role1ReadableView ctx input := by
  refine (protocol0Role1_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role1_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there .here)))))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there .here))))))) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there (.there (.there (.there .here)))))))))

end
end ZkcExamples.Structured.Generated.Scalar.SchnorrAndBindingsCallbacks
