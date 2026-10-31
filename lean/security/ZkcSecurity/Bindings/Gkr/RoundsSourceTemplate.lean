module

public import Zkc.Protocols.Gkr.Source.HelperBodies
public import Zkc.Protocols.Gkr.Source.RoundHelpers
public import ZkcSecurity.Bindings.Gkr.RoundsInvocationInstallation
public import Zkc.Source.Structured.Template
public import Zkc.Source.KernelRfl
public import Zkc.Source.Structured.Bindings.Assembly

@[expose] public section
noncomputable section

/-! Exact typed source selection and normalization for the round protocol.
No declaration index or generated client is part of this template. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate
open Zkc.Source Zkc.Source.Structured NormalForm
open Zkc.Protocols.Gkr.Source
open ZkcExamples.Structured.Generated.Bindings.GkrRoundsGate

abbrev signature (name : String) := HelperBodies.roundsProtocolSignature name
abbrev body (maximum : Nat) := HelperBodies.roundsProtocolBody maximum
abbrev pattern := Bindings.optionalPattern (signature "").inputs
abbrev normalization : Signature :=
  ⟨[], false, false, [roundsOpenHelper, roundsCloseHelper], []⟩

def form (maximum : Nat) : Form [] [] pattern.scope (signature "").outputs :=
  (.owned 1 (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.input (.there (.there (.there (.there .here))))) (.cons (.input (.there (.there (.there (.there (.there .here)))))) .nil)) (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], maximum⟩ : RepeatSpec) "s9" HelperBodies.roundsCallbackBody (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.input (.there .here)) (.cons (.input (.there (.there .here))) (.cons (.input (.there (.there (.there .here)))) (.cons (.input (.there (.there (.there (.there .here))))) (.cons .absent (.cons (.read .here .here) (.cons (.read .here (.there .here)) .nil))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) (.owned 1 (⟨"zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.read .here (.there (.there (.there (.there (.there .here)))))) (.cons (.read .here (.there (.there (.there (.there (.there (.there .here))))))) .nil)) (.done (.cons (.read (.there .here) (.there (.there (.there (.there .here))))) (.cons (.read (.there .here) .here) (.cons (.read (.there .here) (.there .here)) (.cons (.read (.there .here) (.there (.there .here))) (.cons (.read (.there .here) (.there (.there (.there .here)))) (.cons (.read .here .here) (.cons (.read .here (.there .here)) .nil)))))))))))

theorem normalized (maximum : Nat) :
    normalize normalization (body maximum) 1 2 pattern = .ok (form maximum) := by
  kernel_rfl

theorem calls (maximum : Nat) : (form maximum).CallsMatch := by
  kernel_rfl

abbrev callbackNormalization : Signature := ⟨[], false, false, [appendHelper], []⟩
abbrev callbackPattern := Bindings.optionalPattern (.index ::
  ((signature "").outputs ++ [.service "random.bls12-381.fr/0"]))

def callbackForm : Form [] [] callbackPattern.scope (signature "").outputs :=
  (.receive (.field "bls12-381.fr") "label_726f756e64_0" 0 (.receive (.field "bls12-381.fr") "label_726f756e64_1" 0 (.receive (.field "bls12-381.fr") "label_726f756e64_2" 0 (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.halt .incomplete) (.guard (.field "bls12-381.fr") (.var .here) (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there .here)))) (.cons (.var (.there (.there (.there .here)))) .nil)) .here) (.cons (.var (.there (.there .here))) .nil)) .here) (.cons (.var (.there .here)) .nil)) .here) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.halt .incomplete) (.query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657279_0" 0 (.var .here) (.owned 1 (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.present (.var .here)) .nil)) (.done (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.read .here .here) (.cons (.present (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.var (.there (.there (.there (.there .here))))) .nil)) .here) .nil)) .here) .nil)) .here) .nil)) .here)) .nil)))))))))))))))))

theorem callback_normalized : normalize callbackNormalization
    HelperBodies.roundsCallbackBody 1 2 callbackPattern = .ok callbackForm := by
  kernel_rfl

theorem callback_calls : callbackForm.CallsMatch := by
  kernel_rfl

/-- Exact body association retains the operational maximum. -/
theorem maximum_eq_of_body_eq {first second : Nat}
    (same : (body first).erase = (body second).erase) : first = second := by
  have selected := congrArg (fun raw : RawRegion Ty ProtocolOp =>
    raw.operations.filterMap (fun operation => match operation with
      | .repeat spec _ => some spec.maximum
      | _ => none)) same
  change [first] = [second] at selected
  exact List.singleton_inj.mp selected

variable {F G : Type} [Field F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- The callback normalization is independent of the selected declaration and
protocol table, including optional captures and arbitrary incoming coefficients. -/
theorem callback_source (definitions : List CheckedDefinition)
    (protocols : ProtocolTable (assignment F G) (participantInterface F G))
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G))
      (.index :: ((signature "").outputs ++ [.service "random.bls12-381.fr/0"]))) :
    HelperBodies.roundsCallbackBody.denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩)
        (ctx.roles 1) protocols ctx) input.get =
      RoundsVerifierInstallation.callbackBody definitions ctx input := by
  have equation := sound_uniform callbackNormalization HelperBodies.roundsCallbackBody 1 2
    callbackPattern callbackForm callback_normalized callback_calls ctx distinct
    (definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) protocols
    (Bindings.emptyResults (ringModel F G)) (fun entry => entry.elim0)
    (Bindings.optionalBinders (ringModel F G) input) input
    (Bindings.optional_environment _ _) (Bindings.emptyLaws _ _) (fun entry => entry.elim0)
  refine equation.trans ?_
  cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; kernel_rfl

/-- Source-body presentation obtained from the existing normalizer, with no
whole-process equality or helper mathematics supplied by the source client. -/
theorem body_source (definitions : List CheckedDefinition)
    (protocols : ProtocolTable (assignment F G) (participantInterface F G))
    (maximum : Nat) (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) (signature "").inputs) :
    (body maximum).denote
      (participantMeaningWith (.silent _) (participantActions F G)
        (definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩)
        (ctx.roles 1) protocols ctx) input.get =
      RoundsInvocationInstallation.process definitions maximum ctx
        (input.get .here) (input.get (.there .here)) (input.get (.there (.there .here)))
        (input.get (.there (.there (.there .here))))
        (input.get (.there (.there (.there (.there .here)))))
        (input.get (.there (.there (.there (.there (.there .here))))))
        (input.get (.there (.there (.there (.there (.there (.there .here)))))))
        (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) := by
  have equation := sound_uniform normalization (body maximum) 1 2 pattern (form maximum)
    (normalized maximum) (calls maximum) ctx distinct
    (definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩) protocols
    (Bindings.emptyResults (ringModel F G)) (fun entry => entry.elim0)
    (Bindings.optionalBinders (ringModel F G) input) input
    (Bindings.optional_environment _ _) (Bindings.emptyLaws _ _) (fun entry => entry.elim0)
  have callback : (Runs.uniform
      (definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩)
      protocols ctx (ctx.roles 1)).callback
      (ZkcSecurity.Examples.Components.GkrRoundsBinding.repeatSpec maximum)
      HelperBodies.roundsCallbackBody =
        RoundsVerifierInstallation.callbackBody (G := G) definitions ctx := by
    funext args
    exact callback_source definitions protocols ctx distinct args
  refine equation.trans ?_
  cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; simp only [form, Form.denote, Form.denoteOn, Form.denoteWithOn]; rw [callback]; rfl

/-- Complete entry view, retaining both selected declaration masks. -/
def view (definitions : List CheckedDefinition) (name : String) (maximum : Nat)
    (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) (signature name).inputs) :
    PIR.Process (participantInterface F G)
      (Values (Component (assignment F G)) (signature name).outputs) :=
  let visible := maskValues (ctx.roles 1) (ctx.mapScopes (signature name).inputScopes) input
  (RoundsInvocationInstallation.process definitions maximum ctx
    (visible.get .here) (visible.get (.there .here)) (visible.get (.there (.there .here)))
    (visible.get (.there (.there (.there .here))))
    (visible.get (.there (.there (.there (.there .here)))))
    (visible.get (.there (.there (.there (.there (.there .here))))))
    (visible.get (.there (.there (.there (.there (.there (.there .here)))))))
    (visible.get (.there (.there (.there (.there (.there (.there (.there .here))))))))).bind
      fun output => .done (maskValues (ctx.roles 1) (ctx.mapScopes (signature name).outputScopes) output)

private theorem invoke_body_as (payload : UnitPayload)
    (definition : CheckedProtocol) (member : definition ∈ payload.protocols)
    (sig : ProtocolSignature) (same : definition.signature = sig)
    (region : Region protocolDialect sig.inputs sig.outputs)
    (raw : definition.raw = region.erase) (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) sig.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) sig ctx (ctx.roles 1) input =
      (region.denote (participantMeaningWith (.silent _) (participantActions F G)
        (Bindings.helpers payload) (ctx.roles 1) (payload.plainProtocolTable F G) ctx)
        (maskValues (ctx.roles 1) (ctx.mapScopes sig.inputScopes) input).get).bind
          fun output => .done (maskValues (ctx.roles 1) (ctx.mapScopes sig.outputScopes) output) := by
  subst sig
  exact protocol_invoke_body_view (.silent _) (participantActions F G) (Bindings.helpers payload)
    payload.protocols payload.protocolsLinked definition member region raw ctx (ctx.roles 1) input

/-- Install at any actual linked entry with the exact full signature and raw
body. Neither a selected name nor equality of a proposed target process is a premise. -/
theorem invocation (payload : UnitPayload) (name : String) (maximum : Nat)
    (associated : Template.Association payload (signature name) (body maximum))
    (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) (signature name).inputs) :
    invokeProtocol (payload.plainProtocolTable F G) (signature name) ctx (ctx.roles 1) input =
      view payload.definitions name maximum ctx input := by
  rcases associated with ⟨definition, member, same, raw⟩
  refine (invoke_body_as payload definition member (signature name) same
    (body maximum) raw ctx input).trans ?_
  exact bind_congr_left
    (body_source payload.definitions (payload.plainProtocolTable F G) maximum ctx distinct _) _

end ZkcSecurity.Bindings.Gkr.RoundsSourceTemplate
