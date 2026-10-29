module

public import Tests.Generated.NestedRoleBindings
public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! Generated complete callback views. -/
namespace Tests.Generated.NestedRoleBindingsCallbacks
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open Tests.Generated.NestedRoleBindings
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

def protocol0Role0Callback0Body : Region protocolDialect [.index, .index] [.index] :=
  (.ret (.cons (.there .here) .nil))

theorem protocol0Role0Callback0_selected : Zkc.Source.Structured.Bindings.findRepeat "round" definition0.body = some ⟨_, _, protocol0Role0Callback0Body⟩ := by
  kernel_rfl

def protocol0Role0Callback0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]⟩ : Signature)
def protocol0Role0Callback0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role0Callback0Form : (Form [] [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.done (.cons (.input (.there .here)) .nil))

noncomputable def protocol0Role0Callback0Process (_ctx : ProtocolContext) (_b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  .done ((.cons (b1) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role0Callback0_calls : protocol0Role0Callback0Form.CallsMatch := by
  kernel_rfl

theorem protocol0Role0Callback0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol0Role0Callback0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (callbackResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons (b0) (.cons (b1) .nil))) =
      (protocol0Role0Callback0Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol0Role0Callback0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol0Role0Callback0Form [] =
      [] := by
  decide +kernel

theorem protocol0Role0Callback0_normalized : normalize protocol0Role0Callback0Signature protocol0Role0Callback0Body 0 2 protocol0Role0Callback0Pattern = .ok protocol0Role0Callback0Form := by
  kernel_rfl

theorem protocol0Role0Callback0_source (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) [.index, .index]) :
    protocol0Role0Callback0Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 0) (payload.plainProtocolTable F G) ctx) input.get =
      (protocol0Role0Callback0Process ctx (input.get .here) (input.get (.there .here))) := by
  have equation := sound_uniform protocol0Role0Callback0Signature protocol0Role0Callback0Body 0 2 protocol0Role0Callback0Pattern protocol0Role0Callback0Form protocol0Role0Callback0_normalized protocol0Role0Callback0_calls ctx distinct
    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))
    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input
    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (input) = (.cons ((input).get .here) (.cons ((input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (protocol0Role0Callback0_presentation (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))

theorem protocol0Role0Callback0_function (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2) :
    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) protocol0Role0Callback0Body =
      (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol0Role0Callback0Process ctx (input.get .here) (input.get (.there .here)))) := by
  funext input
  exact protocol0Role0Callback0_source ctx distinct input

noncomputable def protocol0Role0ReadableProcess (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons (b1) .nil) .nil (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol0Role0Callback0Process ctx (input.get .here) (input.get (.there .here))))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role0_readable (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (protocol0Role0Process (F := F) (G := G) ctx b0 b1) = (protocol0Role0ReadableProcess (F := F) (G := G) ctx b0 b1) := by
  have equation := Eq.refl (protocol0Role0Process (F := F) (G := G) ctx b0 b1)
  have callback0 := protocol0Role0Callback0_function (F := F) (G := G) ctx distinct
  unfold protocol0Role0Callback0Body at callback0
  conv_rhs at equation => unfold protocol0Role0Process; simp only [callback0]
  exact equation

noncomputable def protocol0Role0ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role0ReadableProcess ctx ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role0_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 0) input = protocol0Role0ReadableView ctx input := by
  refine (protocol0Role0_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role0_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)))

def protocol0Role1Callback0Body : Region protocolDialect [.index, .index] [.index] :=
  (.ret (.cons (.there .here) .nil))

theorem protocol0Role1Callback0_selected : Zkc.Source.Structured.Bindings.findRepeat "round" definition0.body = some ⟨_, _, protocol0Role1Callback0Body⟩ := by
  kernel_rfl

def protocol0Role1Callback0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]⟩ : Signature)
def protocol0Role1Callback0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role1Callback0Form : (Form [] [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.done (.cons (.input (.there .here)) .nil))

noncomputable def protocol0Role1Callback0Process (_ctx : ProtocolContext) (_b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  .done ((.cons (b1) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role1Callback0_calls : protocol0Role1Callback0Form.CallsMatch := by
  kernel_rfl

theorem protocol0Role1Callback0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol0Role1Callback0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (callbackResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (actualCallees payload calleeKeys) (.cons (b0) (.cons (b1) .nil))) =
      (protocol0Role1Callback0Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol0Role1Callback0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol0Role1Callback0Form [] =
      [] := by
  decide +kernel

theorem protocol0Role1Callback0_normalized : normalize protocol0Role1Callback0Signature protocol0Role1Callback0Body 1 2 protocol0Role1Callback0Pattern = .ok protocol0Role1Callback0Form := by
  kernel_rfl

theorem protocol0Role1Callback0_source (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) [.index, .index]) :
    protocol0Role1Callback0Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 1) (payload.plainProtocolTable F G) ctx) input.get =
      (protocol0Role1Callback0Process ctx (input.get .here) (input.get (.there .here))) := by
  have equation := sound_uniform protocol0Role1Callback0Signature protocol0Role1Callback0Body 1 2 protocol0Role1Callback0Pattern protocol0Role1Callback0Form protocol0Role1Callback0_normalized protocol0Role1Callback0_calls ctx distinct
    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))
    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input
    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (input) = (.cons ((input).get .here) (.cons ((input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (protocol0Role1Callback0_presentation (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))

theorem protocol0Role1Callback0_function (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) :
    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) protocol0Role1Callback0Body =
      (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol0Role1Callback0Process ctx (input.get .here) (input.get (.there .here)))) := by
  funext input
  exact protocol0Role1Callback0_source ctx distinct input

noncomputable def protocol0Role1ReadableProcess (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons (b1) .nil) .nil (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol0Role1Callback0Process ctx (input.get .here) (input.get (.there .here))))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role1_readable (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (protocol0Role1Process (F := F) (G := G) ctx b0 b1) = (protocol0Role1ReadableProcess (F := F) (G := G) ctx b0 b1) := by
  have equation := Eq.refl (protocol0Role1Process (F := F) (G := G) ctx b0 b1)
  have callback0 := protocol0Role1Callback0_function (F := F) (G := G) ctx distinct
  unfold protocol0Role1Callback0Body at callback0
  conv_rhs at equation => unfold protocol0Role1Process; simp only [callback0]
  exact equation

noncomputable def protocol0Role1ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role1ReadableProcess ctx ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out)

theorem protocol0Role1_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition0.signature ctx
      (ctx.roles 1) input = protocol0Role1ReadableView ctx input := by
  refine (protocol0Role1_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role1_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)))

noncomputable def protocol1Role0ReadableProcess (_ctx : ProtocolContext) (b0 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .done ((.cons (b0) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol1Role0_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 0 2) (b0 : (Option (Bool))) :
    (protocol1Role0Process (F := F) (G := G) ctx b0) = (protocol1Role0ReadableProcess (F := F) (G := G) ctx b0) := by
  unfold protocol1Role0Process protocol1Role0ReadableProcess
  rfl

noncomputable def protocol1Role0ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition1.outputs) :=
  (protocol1Role0ReadableProcess ctx ((maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input).get .here)).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition1.outputScopes) out)

theorem protocol1Role0_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition1.signature ctx
      (ctx.roles 0) input = protocol1Role0ReadableView ctx input := by
  refine (protocol1Role0_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition1.outputScopes) out))
    (protocol1Role0_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input).get .here))

noncomputable def protocol1Role1ReadableProcess (_ctx : ProtocolContext) (b0 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .done ((.cons (b0) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol1Role1_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 1 2) (b0 : (Option (Bool))) :
    (protocol1Role1Process (F := F) (G := G) ctx b0) = (protocol1Role1ReadableProcess (F := F) (G := G) ctx b0) := by
  unfold protocol1Role1Process protocol1Role1ReadableProcess
  rfl

noncomputable def protocol1Role1ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition1.outputs) :=
  (protocol1Role1ReadableProcess ctx ((maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input).get .here)).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition1.outputScopes) out)

theorem protocol1Role1_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition1.signature ctx
      (ctx.roles 1) input = protocol1Role1ReadableView ctx input := by
  refine (protocol1Role1_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition1.outputScopes) out))
    (protocol1Role1_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input).get .here))

noncomputable def protocol2Role0ReadableProcess (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol2Role0Callees ⟨1, by decide⟩) ((ctx).enter "swapped" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol2Role0Callees ⟨0, by decide⟩) ((ctx).enter "again" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b2).get .here) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol2Role0_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 0 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (protocol2Role0Process (F := F) (G := G) ctx b0 b1) = (protocol2Role0ReadableProcess (F := F) (G := G) ctx b0 b1) := by
  unfold protocol2Role0Process protocol2Role0ReadableProcess
  rfl

noncomputable def protocol2Role0ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition2.outputs) :=
  (protocol2Role0ReadableProcess ctx ((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input).get (.there .here))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition2.outputScopes) out)

theorem protocol2Role0_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx
      (ctx.roles 0) input = protocol2Role0ReadableView ctx input := by
  refine (protocol2Role0_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition2.outputScopes) out))
    (protocol2Role0_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input).get (.there .here)))

noncomputable def protocol2Role1ReadableProcess (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol2Role1Callees ⟨0, by decide⟩) ((ctx).enter "swapped" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol2Role1Callees ⟨1, by decide⟩) ((ctx).enter "again" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b2).get .here) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol2Role1_readable (ctx : ProtocolContext)
    (_distinct : RosterDistinct ctx 1 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (protocol2Role1Process (F := F) (G := G) ctx b0 b1) = (protocol2Role1ReadableProcess (F := F) (G := G) ctx b0 b1) := by
  unfold protocol2Role1Process protocol2Role1ReadableProcess
  rfl

noncomputable def protocol2Role1ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition2.outputs) :=
  (protocol2Role1ReadableProcess ctx ((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input).get (.there .here))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition2.outputScopes) out)

theorem protocol2Role1_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx
      (ctx.roles 1) input = protocol2Role1ReadableView ctx input := by
  refine (protocol2Role1_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition2.outputScopes) out))
    (protocol2Role1_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input).get (.there .here)))

def protocol3Role0Callback0Body : Region protocolDialect [.index, .index] [.index] :=
  (.letOp (.mark "before") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "inner") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner") (.cons (.there .here) (.cons .here .nil)) (.cons (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) (.ret (.cons .here .nil))))))

theorem protocol3Role0Callback0_selected : Zkc.Source.Structured.Bindings.findRepeat "outer" definition3.body = some ⟨_, _, protocol3Role0Callback0Body⟩ := by
  kernel_rfl

def protocol3Role0Callback0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]⟩ : Signature)
def protocol3Role0Callback0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol3Role0Callback0Form : (Form [] [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.apply ⟨1, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before" (by change (Values (Argument [] [(.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner" (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) (.input (.there .here)) (.cons (.read .here .here) .nil) .nil (.done (.cons (.read .here .here) .nil))))

noncomputable def protocol3Role0Callback0Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((actualCallees payload calleeKeys ⟨1, by decide⟩) ((ctx).enter "before" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons ((b2).get .here) .nil) .nil ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role0Callback0_calls : protocol3Role0Callback0Form.CallsMatch := by
  kernel_rfl

theorem protocol3Role0Callback0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol3Role0Callback0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (callbackResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons (b0) (.cons (b1) .nil))) =
      (protocol3Role0Callback0Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol3Role0Callback0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol3Role0Callback0Form [] =
      [(⟨[], "apply", "before"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "repeat", "inner"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol3Role0Callback0_normalized : normalize protocol3Role0Callback0Signature protocol3Role0Callback0Body 0 2 protocol3Role0Callback0Pattern = .ok protocol3Role0Callback0Form := by
  kernel_rfl

theorem protocol3Role0Callback0_source (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) [.index, .index]) :
    protocol3Role0Callback0Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 0) (payload.plainProtocolTable F G) ctx) input.get =
      (protocol3Role0Callback0Process ctx (input.get .here) (input.get (.there .here))) := by
  have equation := sound_uniform protocol3Role0Callback0Signature protocol3Role0Callback0Body 0 2 protocol3Role0Callback0Pattern protocol3Role0Callback0Form protocol3Role0Callback0_normalized protocol3Role0Callback0_calls ctx distinct
    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))
    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input
    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (input) = (.cons ((input).get .here) (.cons ((input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (protocol3Role0Callback0_presentation (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))

theorem protocol3Role0Callback0_function (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2) :
    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) protocol3Role0Callback0Body =
      (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol3Role0Callback0Process ctx (input.get .here) (input.get (.there .here)))) := by
  funext input
  exact protocol3Role0Callback0_source ctx distinct input

def protocol3Role0Callback1Body : Region protocolDialect [.index, .index] [.index] :=
  (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))

theorem protocol3Role0Callback1_selected : Zkc.Source.Structured.Bindings.findRepeat "inner" definition3.body = some ⟨_, _, protocol3Role0Callback1Body⟩ := by
  kernel_rfl

def protocol3Role0Callback1Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]⟩ : Signature)
def protocol3Role0Callback1Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol3Role0Callback1Form : (Form [] [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.apply ⟨0, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside" (by change (Values (Argument [] [(.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.apply ⟨1, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again" (by change (Values (Argument [] [(.tuple [.index]), (.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input (.there .here)) (.cons (.read .here .here) .nil))) (.done (.cons (.read .here .here) .nil))))

noncomputable def protocol3Role0Callback1Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((actualCallees payload calleeKeys ⟨0, by decide⟩) ((ctx).enter "inside" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((actualCallees payload calleeKeys ⟨1, by decide⟩) ((ctx).enter "again" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons ((b2).get .here) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role0Callback1_calls : protocol3Role0Callback1Form.CallsMatch := by
  kernel_rfl

theorem protocol3Role0Callback1_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol3Role0Callback1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (callbackResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons (b0) (.cons (b1) .nil))) =
      (protocol3Role0Callback1Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol3Role0Callback1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol3Role0Callback1Form [] =
      [(⟨[], "apply", "inside"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "apply", "again"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol3Role0Callback1_normalized : normalize protocol3Role0Callback1Signature protocol3Role0Callback1Body 0 2 protocol3Role0Callback1Pattern = .ok protocol3Role0Callback1Form := by
  kernel_rfl

theorem protocol3Role0Callback1_source (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) [.index, .index]) :
    protocol3Role0Callback1Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 0) (payload.plainProtocolTable F G) ctx) input.get =
      (protocol3Role0Callback1Process ctx (input.get .here) (input.get (.there .here))) := by
  have equation := sound_uniform protocol3Role0Callback1Signature protocol3Role0Callback1Body 0 2 protocol3Role0Callback1Pattern protocol3Role0Callback1Form protocol3Role0Callback1_normalized protocol3Role0Callback1_calls ctx distinct
    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))
    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input
    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (input) = (.cons ((input).get .here) (.cons ((input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (protocol3Role0Callback1_presentation (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))

theorem protocol3Role0Callback1_function (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2) :
    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) protocol3Role0Callback1Body =
      (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol3Role0Callback1Process ctx (input.get .here) (input.get (.there .here)))) := by
  funext input
  exact protocol3Role0Callback1_source ctx distinct input

noncomputable def protocol3Role0ReadableProcess (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (_b2 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol3Role0Callees ⟨5, by decide⟩) ((ctx).enter "first" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol3Role0Callees ⟨4, by decide⟩) ((ctx).enter "second" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b3).get .here) (.cons (b1) .nil)))).bind fun (b4 : (Values (Component (assignment F G)) [.index])) =>
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons ((b4).get .here) .nil) .nil (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol3Role0Callback0Process ctx (input.get .here) (input.get (.there .here))))).bind fun (b5 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b5).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role0_readable (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (b2 : (Option (Bool))) :
    (protocol3Role0Process (F := F) (G := G) ctx b0 b1 b2) = (protocol3Role0ReadableProcess (F := F) (G := G) ctx b0 b1 b2) := by
  have equation := Eq.refl (protocol3Role0Process (F := F) (G := G) ctx b0 b1 b2)
  have callback0 := protocol3Role0Callback0_function (F := F) (G := G) ctx distinct
  unfold protocol3Role0Callback0Body at callback0
  conv_rhs at equation => unfold protocol3Role0Process; simp only [callback0]
  exact equation

noncomputable def protocol3Role0ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition3.outputs) :=
  (protocol3Role0ReadableProcess ctx ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get (.there (.there .here)))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition3.outputScopes) out)

theorem protocol3Role0_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition3.signature ctx
      (ctx.roles 0) input = protocol3Role0ReadableView ctx input := by
  refine (protocol3Role0_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition3.outputScopes) out))
    (protocol3Role0_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get .here) ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get (.there (.there .here))))

def protocol3Role1Callback0Body : Region protocolDialect [.index, .index] [.index] :=
  (.letOp (.mark "before") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "inner") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner") (.cons (.there .here) (.cons .here .nil)) (.cons (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) (.ret (.cons .here .nil))))))

theorem protocol3Role1Callback0_selected : Zkc.Source.Structured.Bindings.findRepeat "outer" definition3.body = some ⟨_, _, protocol3Role1Callback0Body⟩ := by
  kernel_rfl

def protocol3Role1Callback0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]⟩ : Signature)
def protocol3Role1Callback0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol3Role1Callback0Form : (Form [] [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.apply ⟨0, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before" (by change (Values (Argument [] [(.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner" (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) (.input (.there .here)) (.cons (.read .here .here) .nil) .nil (.done (.cons (.read .here .here) .nil))))

noncomputable def protocol3Role1Callback0Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((actualCallees payload calleeKeys ⟨0, by decide⟩) ((ctx).enter "before" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons ((b2).get .here) .nil) .nil ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role1Callback0_calls : protocol3Role1Callback0Form.CallsMatch := by
  kernel_rfl

theorem protocol3Role1Callback0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol3Role1Callback0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (callbackResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (actualCallees payload calleeKeys) (.cons (b0) (.cons (b1) .nil))) =
      (protocol3Role1Callback0Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol3Role1Callback0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol3Role1Callback0Form [] =
      [(⟨[], "apply", "before"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "repeat", "inner"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol3Role1Callback0_normalized : normalize protocol3Role1Callback0Signature protocol3Role1Callback0Body 1 2 protocol3Role1Callback0Pattern = .ok protocol3Role1Callback0Form := by
  kernel_rfl

theorem protocol3Role1Callback0_source (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) [.index, .index]) :
    protocol3Role1Callback0Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 1) (payload.plainProtocolTable F G) ctx) input.get =
      (protocol3Role1Callback0Process ctx (input.get .here) (input.get (.there .here))) := by
  have equation := sound_uniform protocol3Role1Callback0Signature protocol3Role1Callback0Body 1 2 protocol3Role1Callback0Pattern protocol3Role1Callback0Form protocol3Role1Callback0_normalized protocol3Role1Callback0_calls ctx distinct
    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))
    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input
    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (input) = (.cons ((input).get .here) (.cons ((input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (protocol3Role1Callback0_presentation (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))

theorem protocol3Role1Callback0_function (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) :
    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) protocol3Role1Callback0Body =
      (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol3Role1Callback0Process ctx (input.get .here) (input.get (.there .here)))) := by
  funext input
  exact protocol3Role1Callback0_source ctx distinct input

def protocol3Role1Callback1Body : Region protocolDialect [.index, .index] [.index] :=
  (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil))))))

theorem protocol3Role1Callback1_selected : Zkc.Source.Structured.Bindings.findRepeat "inner" definition3.body = some ⟨_, _, protocol3Role1Callback1Body⟩ := by
  kernel_rfl

def protocol3Role1Callback1Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]⟩ : Signature)
def protocol3Role1Callback1Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol3Role1Callback1Form : (Form [] [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.apply ⟨1, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside" (by change (Values (Argument [] [(.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.apply ⟨0, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again" (by change (Values (Argument [] [(.tuple [.index]), (.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input (.there .here)) (.cons (.read .here .here) .nil))) (.done (.cons (.read .here .here) .nil))))

noncomputable def protocol3Role1Callback1Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((actualCallees payload calleeKeys ⟨1, by decide⟩) ((ctx).enter "inside" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((actualCallees payload calleeKeys ⟨0, by decide⟩) ((ctx).enter "again" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons ((b2).get .here) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role1Callback1_calls : protocol3Role1Callback1Form.CallsMatch := by
  kernel_rfl

theorem protocol3Role1Callback1_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol3Role1Callback1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (callbackResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (actualCallees payload calleeKeys) (.cons (b0) (.cons (b1) .nil))) =
      (protocol3Role1Callback1Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol3Role1Callback1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol3Role1Callback1Form [] =
      [(⟨[], "apply", "inside"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "apply", "again"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol3Role1Callback1_normalized : normalize protocol3Role1Callback1Signature protocol3Role1Callback1Body 1 2 protocol3Role1Callback1Pattern = .ok protocol3Role1Callback1Form := by
  kernel_rfl

theorem protocol3Role1Callback1_source (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) [.index, .index]) :
    protocol3Role1Callback1Body.denote (participantMeaningWith (.silent _) (participantActions F G)
      (helpers payload) (ctx.roles 1) (payload.plainProtocolTable F G) ctx) input.get =
      (protocol3Role1Callback1Process ctx (input.get .here) (input.get (.there .here))) := by
  have equation := sound_uniform protocol3Role1Callback1Signature protocol3Role1Callback1Body 1 2 protocol3Role1Callback1Pattern protocol3Role1Callback1Form protocol3Role1Callback1_normalized protocol3Role1Callback1_calls ctx distinct
    (helpers payload) (payload.plainProtocolTable F G) (callbackResults (F := F) (G := G))
    (actualCallees payload calleeKeys) (optionalBinders (ringModel F G) input) input
    (optional_environment _ _) (callbackLaws_hold _) (callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (input) = (.cons ((input).get .here) (.cons ((input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (protocol3Role1Callback1_presentation (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))

theorem protocol3Role1Callback1_function (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) :
    (Runs.uniform (helpers (F := F) (G := G) payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) protocol3Role1Callback1Body =
      (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol3Role1Callback1Process ctx (input.get .here) (input.get (.there .here)))) := by
  funext input
  exact protocol3Role1Callback1_source ctx distinct input

noncomputable def protocol3Role1ReadableProcess (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (_b2 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol3Role1Callees ⟨4, by decide⟩) ((ctx).enter "first" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol3Role1Callees ⟨5, by decide⟩) ((ctx).enter "second" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b3).get .here) (.cons (b1) .nil)))).bind fun (b4 : (Values (Component (assignment F G)) [.index])) =>
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons ((b4).get .here) .nil) .nil (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol3Role1Callback0Process ctx (input.get .here) (input.get (.there .here))))).bind fun (b5 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b5).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role1_readable (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (b2 : (Option (Bool))) :
    (protocol3Role1Process (F := F) (G := G) ctx b0 b1 b2) = (protocol3Role1ReadableProcess (F := F) (G := G) ctx b0 b1 b2) := by
  have equation := Eq.refl (protocol3Role1Process (F := F) (G := G) ctx b0 b1 b2)
  have callback0 := protocol3Role1Callback0_function (F := F) (G := G) ctx distinct
  unfold protocol3Role1Callback0Body at callback0
  conv_rhs at equation => unfold protocol3Role1Process; simp only [callback0]
  exact equation

noncomputable def protocol3Role1ReadableView (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition3.outputs) :=
  (protocol3Role1ReadableProcess ctx ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get (.there (.there .here)))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition3.outputScopes) out)

theorem protocol3Role1_readable_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition3.signature ctx
      (ctx.roles 1) input = protocol3Role1ReadableView ctx input := by
  refine (protocol3Role1_invocation ctx distinct input).trans ?_
  exact congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition3.outputScopes) out))
    (protocol3Role1_readable (F := F) (G := G) ctx distinct ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get .here) ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get (.there .here)) ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get (.there (.there .here))))

end
end Tests.Generated.NestedRoleBindingsCallbacks
