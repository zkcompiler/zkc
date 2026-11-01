module

public import Tests.Generated.StructuredBindingsGeneric
public import Zkc.Source.Structured.Bindings.Selection

@[expose] public section

/-! Generated complete callback views. -/
namespace Tests.Generated.StructuredBindingsGenericCallbacks
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
open Tests.Generated.StructuredBindingsGeneric
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

def protocol0Callback0Selection : RepeatOccurrence definition0.body :=
  checkedRepeat 0 definition0.body (by kernel_rfl)

def protocol0Callback0Body : Region protocolDialect [.index, .index] [.index] :=
  (.ret (.cons (.there .here) .nil))

abbrev protocol0Callback0Site : RepeatSite :=
  ⟨[.index, .index], [.index], (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec), "round", (.cons .here (.cons (.there .here) .nil)), protocol0Callback0Body, (Eq.mp (show Region protocolDialect (protocol0Callback0Selection.repeatSite.spec.state ++ protocol0Callback0Selection.repeatSite.context) protocol0Callback0Selection.repeatSite.outputs = Region protocolDialect [.index, .index, .index] [.index] from by kernel_rfl) protocol0Callback0Selection.repeatSite.next)⟩

theorem protocol0Callback0_body : protocol0Callback0Site.body = protocol0Callback0Body := rfl

theorem protocol0Callback0_selected : (selectRepeat 0 definition0.body).map (·.repeatSite) = some protocol0Callback0Site := by
  kernel_rfl

def protocol0Callback0Occurrence : RepeatAt protocol0Callback0Site definition0.body :=
  selectedRepeat protocol0Callback0_selected

theorem protocol0Callback0_position : protocol0Callback0Occurrence.position = [1] := by
  kernel_rfl

abbrev protocol0Role0Callback0Body := protocol0Callback0Body
abbrev protocol0Role0Callback0Site := protocol0Callback0Site
abbrev protocol0Role0Callback0Occurrence := protocol0Callback0Occurrence
theorem protocol0Role0Callback0_body : protocol0Role0Callback0Site.body = protocol0Role0Callback0Body := protocol0Callback0_body
theorem protocol0Role0Callback0_selected : (selectRepeat 0 definition0.body).map (·.repeatSite) = some protocol0Role0Callback0Site :=
  protocol0Callback0_selected

theorem protocol0Role0Callback0_position : protocol0Role0Callback0Occurrence.position = [1] := protocol0Callback0_position

def protocol0Role0Callback0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)]⟩ : Signature)
def protocol0Role0Callback0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role0Callback0Form : (Form [] [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
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
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons (b1) .nil) .nil (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol0Role0Callback0Process ctx (input.get .here) (input.get (.there .here)))) "round").bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role0_readable (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (protocol0Role0Process (F := F) (G := G) ctx b0 b1) = (protocol0Role0ReadableProcess (F := F) (G := G) ctx b0 b1) := by
  have equation := Eq.refl (protocol0Role0Process (F := F) (G := G) ctx b0 b1)
  have callback0 := protocol0Role0Callback0_function (F := F) (G := G) ctx distinct
  unfold protocol0Role0Callback0Body protocol0Callback0Body at callback0
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

abbrev protocol0Role1Callback0Body := protocol0Callback0Body
abbrev protocol0Role1Callback0Site := protocol0Callback0Site
abbrev protocol0Role1Callback0Occurrence := protocol0Callback0Occurrence
theorem protocol0Role1Callback0_body : protocol0Role1Callback0Site.body = protocol0Role1Callback0Body := protocol0Callback0_body
theorem protocol0Role1Callback0_selected : (selectRepeat 0 definition0.body).map (·.repeatSite) = some protocol0Role1Callback0Site :=
  protocol0Callback0_selected

theorem protocol0Role1Callback0_position : protocol0Role1Callback0Occurrence.position = [1] := protocol0Callback0_position

def protocol0Role1Callback0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)]⟩ : Signature)
def protocol0Role1Callback0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role1Callback0Form : (Form [] [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
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
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons (b1) .nil) .nil (fun (input : Values (Component (assignment F G)) [.index, .index]) => (protocol0Role1Callback0Process ctx (input.get .here) (input.get (.there .here)))) "round").bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role1_readable (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (protocol0Role1Process (F := F) (G := G) ctx b0 b1) = (protocol0Role1ReadableProcess (F := F) (G := G) ctx b0 b1) := by
  have equation := Eq.refl (protocol0Role1Process (F := F) (G := G) ctx b0 b1)
  have callback0 := protocol0Role1Callback0_function (F := F) (G := G) ctx distinct
  unfold protocol0Role1Callback0Body protocol0Callback0Body at callback0
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

end
end Tests.Generated.StructuredBindingsGenericCallbacks
