module

public import ZkcExamples.Structured.SchnorrInteractive
public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.NormalForm.Sites
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Generated from admitted source by ZkcTools.StructuredSource.Bindings.Generate.
Regenerate; every independent presentation is checked by the kernel. -/

namespace ZkcExamples.Structured.Generated.Scalar.SchnorrInteractiveBindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section

abbrev sourceImported := ZkcExamples.Structured.SchnorrInteractive.imported
abbrev program : Program := ZkcExamples.Structured.SchnorrInteractive.program
abbrev payload : UnitPayload := program.payload
def sourceContracts := program.snapshot.contracts

abbrev definition0 : CheckedProtocol :=
  payload.protocols.get ⟨0, by decide +kernel⟩
theorem definition0_member : definition0 ∈ payload.protocols := List.get_mem _ _

def calleeKeys : List CalleeKey := [(⟨(⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", ["role00000000", "role00000001"], [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")], [.boolean], [[0, 1], [0, 1], [0], [0], [1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil))))), []⟩ : CalleeKey), (⟨(⟨"zkl_0b89849acf95dbecb929c216aef6f53085c353bcfe48c36ad4489eda36af65ad", ["role00000000", "role00000001"], [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")], [.boolean], [[0, 1], [0, 1], [0], [0], [1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil))))), []⟩ : CalleeKey)]

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem callees_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) (actualCallees payload calleeKeys) input := by
  apply actualCallees_hold
  · intro entry
    fin_cases entry
    · exact ⟨definition0, definition0_member, rfl⟩
    · exact ⟨definition0, definition0_member, rfl⟩
  · intro entry binders others
    fin_cases entry <;> exact optional_fill _ _ binders others
  · intro entry
    fin_cases entry <;> simp [calleeKeys, calleeAt]

def projectionKeys : List LawKey := []

noncomputable def projectionResults : LawResults (ringModel F G) projectionKeys where
  result := (fun entry => entry.elim0)

theorem projectionLaws_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
    LawsHold (helpers payload).toOn (projectionResults (F := F) (G := G)) input := by
  intro entry
  fin_cases entry

noncomputable def protocol0Role0Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  actualCallees payload calleeKeys

theorem protocol0Role0Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role0Callees input :=
  callees_hold input

def protocol0Role0Signature : Signature := ⟨projectionKeys, false, false, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol0Role0Pattern : InputPattern definition0.inputs := (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))))

noncomputable def protocol0Role0Form : Form protocol0Role0Signature.laws calleeKeys protocol0Role0Pattern.scope [.boolean] :=
  (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.query "s0" "bls12-381.fr" (.cons (.var .here) .nil) (.split (.input (.there (.there .here))) (.halt .incomplete) (.send (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 1 (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there .here)) .nil)) .here) (.receive (.field "bls12-381.fr") "label_64656c6976657279_0" 1 (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.send (.field "bls12-381.fr") "label_726573706f6e7365_0" 1 (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there .here)))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.var .here) .nil)) .here) .nil)) .here) (.done (.cons .absent .nil)))))))))

noncomputable def protocol0Role0Process (ctx : ProtocolContext) (b0 : (Option (G))) (_b1 : (Option (G))) (b2 : (Option (F))) (b3 : (Option (Nat))) (_b4 : (Option (Nat))) :
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

theorem protocol0Role0_calls : protocol0Role0Form.CallsMatch := by
  kernel_rfl

theorem protocol0Role0_presentation (ctx : ProtocolContext) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (F))) (b3 : (Option (Nat))) (b4 : (Option (Nat))) :
    ((protocol0Role0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (protocol0Role0Callees) (.cons (b0) (.cons (b1) (.cons (b2) (.cons (b3) (.cons (b4) .nil)))))) =
      (protocol0Role0Process ctx (b0) (b1) (b2) (b3) (b4)) := by
  kernel_rfl

theorem protocol0Role0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol0Role0Form [] =
      [(⟨[1], "query", "s0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[1, 0, 1], "send", "label_636f6d6d69746d656e74_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[1, 0, 1, 0], "receive", "label_64656c6976657279_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[1, 0, 1, 0, 0, 1], "send", "label_726573706f6e7365_0"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol0Role0_normalized : normalize protocol0Role0Signature definition0.body 0 2 protocol0Role0Pattern = .ok protocol0Role0Form := by
  kernel_rfl

noncomputable def protocol0Role0View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role0Process ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there .here))) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there .here)))) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there (.there .here)))))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role0_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 0) input = protocol0Role0View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition0 definition0_member
    protocol0Role0Signature 0 2 protocol0Role0Pattern
    protocol0Role0Form protocol0Role0_normalized protocol0Role0_calls
    (projectionResults (F := F) (G := G)) protocol0Role0Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol0Role0Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input) = (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))) .nil))))) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role0_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there .here))) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there .here)))) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there (.there .here)))))))

theorem protocol0Role0_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition0.signature ctx (ctx.roles 0) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 0 2) (protocol0Role0View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol0Role0_invocation ctx distinct input⟩

theorem protocol0Role0_participant
    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G 0 input = protocol0Role0View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans (protocol0Role0_invocation {} (RosterDistinct.root _ _) input)

noncomputable def protocol0Role0BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ (fun ctx binders => protocol0Role0View (F := F) (G := G) ctx ((optionalPattern [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))

theorem protocol0Role0BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role0BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ _ input (callees_hold input) (callees_hold input)
  intro ctx binders distinct
  exact protocol0Role0_invocation ctx distinct _

noncomputable def protocol0Role1Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  actualCallees payload calleeKeys

theorem protocol0Role1Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role1Callees input :=
  callees_hold input

def protocol0Role1Signature : Signature := ⟨projectionKeys, false, false, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol0Role1Pattern : InputPattern definition0.inputs := (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))))

noncomputable def protocol0Role1Form : Form protocol0Role1Signature.laws calleeKeys protocol0Role1Pattern.scope [.boolean] :=
  (.receive (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 0 (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657279_0" 0 (.var .here) (.receive (.field "bls12-381.fr") "label_726573706f6e7365_0" 0 (.split (.input (.there (.there (.there (.there .here))))) (.split (.input (.there (.there (.there (.there (.there .here)))))) (.done (.cons .absent .nil)) (.done (.cons .absent .nil))) (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.done (.cons .absent .nil)) (.done (.cons (.present (.calc (.groupEqual "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.var (.there (.there .here))) .nil)) .here) (.cons (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there (.there .here)))) .nil)) .here) .nil)) .here) .nil)) .here)) .nil)))))))))

noncomputable def protocol0Role1Process (ctx : ProtocolContext) (b0 : (Option (G))) (b1 : (Option (G))) (_b2 : (Option (F))) (_b3 : (Option (Nat))) (b4 : (Option (Nat))) :
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

theorem protocol0Role1_calls : protocol0Role1Form.CallsMatch := by
  kernel_rfl

theorem protocol0Role1_presentation (ctx : ProtocolContext) (b0 : (Option (G))) (b1 : (Option (G))) (b2 : (Option (F))) (b3 : (Option (Nat))) (b4 : (Option (Nat))) :
    ((protocol0Role1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (protocol0Role1Callees) (.cons (b0) (.cons (b1) (.cons (b2) (.cons (b3) (.cons (b4) .nil)))))) =
      (protocol0Role1Process ctx (b0) (b1) (b2) (b3) (b4)) := by
  kernel_rfl

theorem protocol0Role1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol0Role1Form [] =
      [(⟨[], "receive", "label_636f6d6d69746d656e74_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 1], "query", "label_6368616c6c656e6765"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 1, 0], "send", "label_64656c6976657279_0"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 1, 0, 0], "receive", "label_726573706f6e7365_0"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol0Role1_normalized : normalize protocol0Role1Signature definition0.body 1 2 protocol0Role1Pattern = .ok protocol0Role1Form := by
  kernel_rfl

noncomputable def protocol0Role1View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role1Process ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there .here))) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there .here)))) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there (.there .here)))))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role1_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 1) input = protocol0Role1View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition0 definition0_member
    protocol0Role1Signature 1 2 protocol0Role1Pattern
    protocol0Role1Form protocol0Role1_normalized protocol0Role1_calls
    (projectionResults (F := F) (G := G)) protocol0Role1Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol0Role1Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input) = (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there .here))) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there .here)))) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there (.there (.there (.there .here))))) .nil))))) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role1_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there .here))) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there .here)))) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there (.there (.there (.there .here)))))))

theorem protocol0Role1_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition0.signature ctx (ctx.roles 1) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 1 2) (protocol0Role1View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol0Role1_invocation ctx distinct input⟩

theorem protocol0Role1_participant
    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G 1 input = protocol0Role1View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans (protocol0Role1_invocation {} (RosterDistinct.root _ _) input)

noncomputable def protocol0Role1BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol0Role0BoundCallees) ⟨1, by decide +kernel⟩ (fun ctx binders => protocol0Role1View (F := F) (G := G) ctx ((optionalPattern [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))

theorem protocol0Role1BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role1BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol0Role0BoundCallees) ⟨1, by decide +kernel⟩ _ input (callees_hold input) (protocol0Role0BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol0Role1_invocation ctx distinct _

end
end ZkcExamples.Structured.Generated.Scalar.SchnorrInteractiveBindings
