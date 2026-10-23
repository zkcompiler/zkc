module

public import Tests.Generated.StructuredBindingsGenericInputs
public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.NormalForm.Sites
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Generated from admitted source by ZkcTools.StructuredSource.Bindings.Generate.
Regenerate; every independent presentation is checked by the kernel. -/

namespace Tests.Generated.StructuredBindingsGeneric
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section

abbrev sourceImported := Tests.Generated.StructuredBindingsGenericInputs.imported
abbrev program : Program := Tests.Generated.StructuredBindingsGenericInputs.program
abbrev payload : UnitPayload := program.payload
def sourceContracts := program.snapshot.contracts

abbrev definition0 : CheckedProtocol :=
  payload.protocols.get ⟨0, by decide +kernel⟩
theorem definition0_member : definition0 ∈ payload.protocols := List.get_mem _ _

def calleeKeys : List CalleeKey := [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)]

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
  (Fin.cases (fun ctx binders => actualCallees payload calleeKeys ⟨0, by decide +kernel⟩ ctx binders) (Fin.cases (fun ctx binders => actualCallees payload calleeKeys ⟨1, by decide +kernel⟩ ctx binders) (fun entry => entry.elim0)))

theorem protocol0Role0Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role0Callees input := by
  apply callees_from_bindings _ (actualCallees payload calleeKeys) _ input (callees_hold input)
  intro entry ctx binders distinct
  fin_cases entry
  · rfl
  · rfl

def protocol0Role0Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)]⟩ : Signature)
def protocol0Role0Pattern : InputPattern definition0.inputs := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role0Form : (Form [] [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" (.ret (.cons (.there .here) .nil)) (.input .here) (.cons (.input (.there .here)) .nil) .nil (.done (.cons (.read .here .here) .nil)))

set_option linter.unusedVariables false in
noncomputable def protocol0Role0Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons (b1) .nil) .nil ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.ret (.cons (.there .here) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role0_calls : protocol0Role0Form.CallsMatch := by
  kernel_rfl

theorem protocol0Role0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol0Role0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (protocol0Role0Callees) (.cons (b0) (.cons (b1) .nil))) =
      (protocol0Role0Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol0Role0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol0Role0Form [] =
      [(⟨[], "repeat", "round"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol0Role0_normalized : normalize protocol0Role0Signature definition0.body 0 2 protocol0Role0Pattern = .ok protocol0Role0Form := by
  kernel_rfl

noncomputable def protocol0Role0View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role0Process ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here))).bind fun out =>
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
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input) = (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role0_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here))))

theorem protocol0Role0_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition0.signature ctx (ctx.roles 0) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 0 2) (protocol0Role0View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol0Role0_invocation ctx distinct input⟩

theorem protocol0Role0_participant
    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G 0 input = protocol0Role0View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans (protocol0Role0_invocation {} (RosterDistinct.root _ _) input)

noncomputable def protocol0Role1Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Fin.cases (fun ctx binders => actualCallees payload calleeKeys ⟨0, by decide +kernel⟩ ctx binders) (Fin.cases (fun ctx binders => actualCallees payload calleeKeys ⟨1, by decide +kernel⟩ ctx binders) (fun entry => entry.elim0)))

theorem protocol0Role1Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role1Callees input := by
  apply callees_from_bindings _ (actualCallees payload calleeKeys) _ input (callees_hold input)
  intro entry ctx binders distinct
  fin_cases entry
  · rfl
  · rfl

def protocol0Role1Signature : Signature := (⟨[], false, false, [], [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)]⟩ : Signature)
def protocol0Role1Pattern : InputPattern definition0.inputs := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role1Form : (Form [] [(⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"counter", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey)] [(.component .index), (.component .index)] [.index]) :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" (.ret (.cons (.there .here) .nil)) (.input .here) (.cons (.input (.there .here)) .nil) .nil (.done (.cons (.read .here .here) .nil)))

set_option linter.unusedVariables false in
noncomputable def protocol0Role1Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons (b1) .nil) .nil ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.ret (.cons (.there .here) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol0Role1_calls : protocol0Role1Form.CallsMatch := by
  kernel_rfl

theorem protocol0Role1_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol0Role1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (protocol0Role1Callees) (.cons (b0) (.cons (b1) .nil))) =
      (protocol0Role1Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol0Role1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol0Role1Form [] =
      [(⟨[], "repeat", "round"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol0Role1_normalized : normalize protocol0Role1Signature definition0.body 1 2 protocol0Role1Pattern = .ok protocol0Role1Form := by
  kernel_rfl

noncomputable def protocol0Role1View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition0.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition0.outputs) :=
  (protocol0Role1Process ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here))).bind fun out =>
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
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input) = (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition0.outputScopes) out))
    (protocol0Role1_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition0.inputScopes) input)).get (.there .here))))

theorem protocol0Role1_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition0.signature ctx (ctx.roles 1) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 1 2) (protocol0Role1View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol0Role1_invocation ctx distinct input⟩

theorem protocol0Role1_participant
    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G 1 input = protocol0Role1View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans (protocol0Role1_invocation {} (RosterDistinct.root _ _) input)

end
end Tests.Generated.StructuredBindingsGeneric
