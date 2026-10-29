module

public import Tests.Generators.RoleViewControls
public import Zkc.Source.Structured.Bindings.Assembly
public import Zkc.Source.Structured.NormalForm.Sites
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

@[expose] public section

/-! Generated from admitted source by ZkcTools.StructuredSource.Bindings.Generate.
Regenerate; every independent presentation is checked by the kernel. -/

namespace Tests.Generated.NestedRoleBindings
open Zkc.Source Zkc.Source.Structured Zkc.Source.Structured.NormalForm Zkc.Source.Structured.Bindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
noncomputable section

abbrev sourceImported := (⟨Tests.Generators.RoleViewControls.nestedProgram, by kernel_rfl⟩ : Imported Tests.Generators.RoleViewControls.nested)
abbrev program : Program := Tests.Generators.RoleViewControls.nestedProgram
abbrev payload : UnitPayload := program.payload
def sourceContracts := program.snapshot.contracts

abbrev definition0 : CheckedProtocol :=
  payload.protocols.get ⟨0, by decide +kernel⟩
theorem definition0_member : definition0 ∈ payload.protocols := List.get_mem _ _

abbrev definition1 : CheckedProtocol :=
  payload.protocols.get ⟨1, by decide +kernel⟩
theorem definition1_member : definition1 ∈ payload.protocols := List.get_mem _ _

abbrev definition2 : CheckedProtocol :=
  payload.protocols.get ⟨2, by decide +kernel⟩
theorem definition2_member : definition2 ∈ payload.protocols := List.get_mem _ _

abbrev definition3 : CheckedProtocol :=
  payload.protocols.get ⟨3, by decide +kernel⟩
theorem definition3_member : definition3 ∈ payload.protocols := List.get_mem _ _

def calleeKeys : List CalleeKey := [(⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 0, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"booleanLeaf", ["Alice", "Bob"], [.boolean], [.boolean], [[1]], [[1]]⟩ : ProtocolSignature), 1, (.cons .optional .nil), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional .nil)), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 0, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey), (⟨(⟨"root", ["Alice", "Bob"], [.index, .index, .boolean], [.index], [[0, 1], [0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature), 1, (.cons .optional (.cons .optional (.cons .optional .nil))), []⟩ : CalleeKey)]

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

theorem callees_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) (actualCallees payload calleeKeys) input := by
  apply actualCallees_hold
  · intro entry
    fin_cases entry
    · exact ⟨definition0, definition0_member, rfl⟩
    · exact ⟨definition0, definition0_member, rfl⟩
    · exact ⟨definition1, definition1_member, rfl⟩
    · exact ⟨definition1, definition1_member, rfl⟩
    · exact ⟨definition2, definition2_member, rfl⟩
    · exact ⟨definition2, definition2_member, rfl⟩
    · exact ⟨definition3, definition3_member, rfl⟩
    · exact ⟨definition3, definition3_member, rfl⟩
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
def protocol0Role0Pattern : InputPattern definition0.inputs := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role0Form : Form protocol0Role0Signature.laws calleeKeys protocol0Role0Pattern.scope [.index] :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" (.ret (.cons (.there .here) .nil)) (.input .here) (.cons (.input (.there .here)) .nil) .nil (.done (.cons (.read .here .here) .nil)))

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

noncomputable def protocol0Role0BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ (fun ctx binders => protocol0Role0View (F := F) (G := G) ctx ((optionalPattern [.index, .index]).environment (ringModel F G) binders)))

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
def protocol0Role1Pattern : InputPattern definition0.inputs := (.cons .optional (.cons .optional .nil))

noncomputable def protocol0Role1Form : Form protocol0Role1Signature.laws calleeKeys protocol0Role1Pattern.scope [.index] :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" (.ret (.cons (.there .here) .nil)) (.input .here) (.cons (.input (.there .here)) .nil) .nil (.done (.cons (.read .here .here) .nil)))

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

noncomputable def protocol0Role1BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol0Role0BoundCallees) ⟨1, by decide +kernel⟩ (fun ctx binders => protocol0Role1View (F := F) (G := G) ctx ((optionalPattern [.index, .index]).environment (ringModel F G) binders)))

theorem protocol0Role1BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol0Role1BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol0Role0BoundCallees) ⟨1, by decide +kernel⟩ _ input (callees_hold input) (protocol0Role0BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol0Role1_invocation ctx distinct _

noncomputable def protocol1Role0Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  protocol0Role1BoundCallees

theorem protocol1Role0Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol1Role0Callees input :=
  protocol0Role1BoundCallees_hold input

def protocol1Role0Signature : Signature := ⟨projectionKeys, false, false, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol1Role0Pattern : InputPattern definition1.inputs := (.cons .optional .nil)

noncomputable def protocol1Role0Form : Form protocol1Role0Signature.laws calleeKeys protocol1Role0Pattern.scope [.boolean] :=
  (.done (.cons (.input .here) .nil))

noncomputable def protocol1Role0Process (_ctx : ProtocolContext) (b0 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .done ((.cons (b0) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol1Role0_calls : protocol1Role0Form.CallsMatch := by
  kernel_rfl

theorem protocol1Role0_presentation (ctx : ProtocolContext) (b0 : (Option (Bool))) :
    ((protocol1Role0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (protocol1Role0Callees) (.cons (b0) .nil)) =
      (protocol1Role0Process ctx (b0)) := by
  kernel_rfl

theorem protocol1Role0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol1Role0Form [] =
      [] := by
  decide +kernel

theorem protocol1Role0_normalized : normalize protocol1Role0Signature definition1.body 0 2 protocol1Role0Pattern = .ok protocol1Role0Form := by
  kernel_rfl

noncomputable def protocol1Role0View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition1.outputs) :=
  (protocol1Role0Process ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input)).get .here)).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition1.outputScopes) out)

theorem protocol1Role0_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition1.signature ctx
      (ctx.roles 0) input = protocol1Role0View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition1 definition1_member
    protocol1Role0Signature 0 2 protocol1Role0Pattern
    protocol1Role0Form protocol1Role0_normalized protocol1Role0_calls
    (projectionResults (F := F) (G := G)) protocol1Role0Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol1Role0Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input) = (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input).get .here) .nil) := by
    cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition1.outputScopes) out))
    (protocol1Role0_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition1.inputScopes) input)).get .here)))

theorem protocol1Role0_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition1.signature ctx (ctx.roles 0) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 0 2) (protocol1Role0View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol1Role0_invocation ctx distinct input⟩

noncomputable def protocol1Role0BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol0Role1BoundCallees) ⟨2, by decide +kernel⟩ (fun ctx binders => protocol1Role0View (F := F) (G := G) ctx ((optionalPattern [.boolean]).environment (ringModel F G) binders)))

theorem protocol1Role0BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol1Role0BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol0Role1BoundCallees) ⟨2, by decide +kernel⟩ _ input (callees_hold input) (protocol0Role1BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol1Role0_invocation ctx distinct _

noncomputable def protocol1Role1Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  protocol0Role1BoundCallees

theorem protocol1Role1Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol1Role1Callees input :=
  protocol0Role1BoundCallees_hold input

def protocol1Role1Signature : Signature := ⟨projectionKeys, false, false, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol1Role1Pattern : InputPattern definition1.inputs := (.cons .optional .nil)

noncomputable def protocol1Role1Form : Form protocol1Role1Signature.laws calleeKeys protocol1Role1Pattern.scope [.boolean] :=
  (.done (.cons (.input .here) .nil))

noncomputable def protocol1Role1Process (_ctx : ProtocolContext) (b0 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .done ((.cons (b0) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem protocol1Role1_calls : protocol1Role1Form.CallsMatch := by
  kernel_rfl

theorem protocol1Role1_presentation (ctx : ProtocolContext) (b0 : (Option (Bool))) :
    ((protocol1Role1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (protocol1Role1Callees) (.cons (b0) .nil)) =
      (protocol1Role1Process ctx (b0)) := by
  kernel_rfl

theorem protocol1Role1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol1Role1Form [] =
      [] := by
  decide +kernel

theorem protocol1Role1_normalized : normalize protocol1Role1Signature definition1.body 1 2 protocol1Role1Pattern = .ok protocol1Role1Form := by
  kernel_rfl

noncomputable def protocol1Role1View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition1.outputs) :=
  (protocol1Role1Process ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input)).get .here)).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition1.outputScopes) out)

theorem protocol1Role1_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition1.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition1.signature ctx
      (ctx.roles 1) input = protocol1Role1View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition1 definition1_member
    protocol1Role1Signature 1 2 protocol1Role1Pattern
    protocol1Role1Form protocol1Role1_normalized protocol1Role1_calls
    (projectionResults (F := F) (G := G)) protocol1Role1Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol1Role1Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input) = (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input).get .here) .nil) := by
    cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition1.outputScopes) out))
    (protocol1Role1_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition1.inputScopes) input)).get .here)))

theorem protocol1Role1_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition1.signature ctx (ctx.roles 1) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 1 2) (protocol1Role1View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol1Role1_invocation ctx distinct input⟩

noncomputable def protocol1Role1BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol1Role0BoundCallees) ⟨3, by decide +kernel⟩ (fun ctx binders => protocol1Role1View (F := F) (G := G) ctx ((optionalPattern [.boolean]).environment (ringModel F G) binders)))

theorem protocol1Role1BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol1Role1BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol1Role0BoundCallees) ⟨3, by decide +kernel⟩ _ input (callees_hold input) (protocol1Role0BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol1Role1_invocation ctx distinct _

noncomputable def protocol2Role0Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  protocol1Role1BoundCallees

theorem protocol2Role0Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol2Role0Callees input :=
  protocol1Role1BoundCallees_hold input

def protocol2Role0Signature : Signature := ⟨projectionKeys, false, false, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol2Role0Pattern : InputPattern definition2.inputs := (.cons .optional (.cons .optional .nil))

noncomputable def protocol2Role0Form : Form protocol2Role0Signature.laws calleeKeys protocol2Role0Pattern.scope [.index] :=
  (.apply ⟨1, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "swapped" (by change (Values (Argument [] [(.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.apply ⟨0, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "again" (by change (Values (Argument [] [(.tuple [.index]), (.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.read .here .here) (.cons (.input (.there (.there .here))) .nil))) (.done (.cons (.read .here .here) .nil))))

noncomputable def protocol2Role0Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol2Role0Callees ⟨1, by decide⟩) ((ctx).enter "swapped" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol2Role0Callees ⟨0, by decide⟩) ((ctx).enter "again" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b2).get .here) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol2Role0_calls : protocol2Role0Form.CallsMatch := by
  kernel_rfl

theorem protocol2Role0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol2Role0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (protocol2Role0Callees) (.cons (b0) (.cons (b1) .nil))) =
      (protocol2Role0Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol2Role0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol2Role0Form [] =
      [(⟨[], "apply", "swapped"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "apply", "again"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol2Role0_normalized : normalize protocol2Role0Signature definition2.body 0 2 protocol2Role0Pattern = .ok protocol2Role0Form := by
  kernel_rfl

noncomputable def protocol2Role0View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition2.outputs) :=
  (protocol2Role0Process ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input)).get (.there .here))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition2.outputScopes) out)

theorem protocol2Role0_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx
      (ctx.roles 0) input = protocol2Role0View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition2 definition2_member
    protocol2Role0Signature 0 2 protocol2Role0Pattern
    protocol2Role0Form protocol2Role0_normalized protocol2Role0_calls
    (projectionResults (F := F) (G := G)) protocol2Role0Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol2Role0Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input) = (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition2.outputScopes) out))
    (protocol2Role0_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition2.inputScopes) input)).get (.there .here))))

theorem protocol2Role0_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition2.signature ctx (ctx.roles 0) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 0 2) (protocol2Role0View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol2Role0_invocation ctx distinct input⟩

noncomputable def protocol2Role0BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol1Role1BoundCallees) ⟨4, by decide +kernel⟩ (fun ctx binders => protocol2Role0View (F := F) (G := G) ctx ((optionalPattern [.index, .index]).environment (ringModel F G) binders)))

theorem protocol2Role0BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol2Role0BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol1Role1BoundCallees) ⟨4, by decide +kernel⟩ _ input (callees_hold input) (protocol1Role1BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol2Role0_invocation ctx distinct _

noncomputable def protocol2Role1Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  protocol1Role1BoundCallees

theorem protocol2Role1Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol2Role1Callees input :=
  protocol1Role1BoundCallees_hold input

def protocol2Role1Signature : Signature := ⟨projectionKeys, false, false, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol2Role1Pattern : InputPattern definition2.inputs := (.cons .optional (.cons .optional .nil))

noncomputable def protocol2Role1Form : Form protocol2Role1Signature.laws calleeKeys protocol2Role1Pattern.scope [.index] :=
  (.apply ⟨0, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "swapped" (by change (Values (Argument [] [(.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.apply ⟨1, by decide⟩ (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "again" (by change (Values (Argument [] [(.tuple [.index]), (.component .index), (.component .index)]) [(.component .index), (.component .index)]); exact (.cons (.read .here .here) (.cons (.input (.there (.there .here))) .nil))) (.done (.cons (.read .here .here) .nil))))

noncomputable def protocol2Role1Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol2Role1Callees ⟨0, by decide⟩) ((ctx).enter "swapped" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol2Role1Callees ⟨1, by decide⟩) ((ctx).enter "again" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b2).get .here) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b3).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol2Role1_calls : protocol2Role1Form.CallsMatch := by
  kernel_rfl

theorem protocol2Role1_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) :
    ((protocol2Role1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (protocol2Role1Callees) (.cons (b0) (.cons (b1) .nil))) =
      (protocol2Role1Process ctx (b0) (b1)) := by
  kernel_rfl

theorem protocol2Role1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol2Role1Form [] =
      [(⟨[], "apply", "swapped"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "apply", "again"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol2Role1_normalized : normalize protocol2Role1Signature definition2.body 1 2 protocol2Role1Pattern = .ok protocol2Role1Form := by
  kernel_rfl

noncomputable def protocol2Role1View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition2.outputs) :=
  (protocol2Role1Process ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input)).get (.there .here))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition2.outputScopes) out)

theorem protocol2Role1_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition2.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition2.signature ctx
      (ctx.roles 1) input = protocol2Role1View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition2 definition2_member
    protocol2Role1Signature 1 2 protocol2Role1Pattern
    protocol2Role1Form protocol2Role1_normalized protocol2Role1_calls
    (projectionResults (F := F) (G := G)) protocol2Role1Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol2Role1Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input) = (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input).get (.there .here)) .nil)) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition2.outputScopes) out))
    (protocol2Role1_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition2.inputScopes) input)).get (.there .here))))

theorem protocol2Role1_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition2.signature ctx (ctx.roles 1) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 1 2) (protocol2Role1View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol2Role1_invocation ctx distinct input⟩

noncomputable def protocol2Role1BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol2Role0BoundCallees) ⟨5, by decide +kernel⟩ (fun ctx binders => protocol2Role1View (F := F) (G := G) ctx ((optionalPattern [.index, .index]).environment (ringModel F G) binders)))

theorem protocol2Role1BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol2Role1BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol2Role0BoundCallees) ⟨5, by decide +kernel⟩ _ input (callees_hold input) (protocol2Role0BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol2Role1_invocation ctx distinct _

noncomputable def protocol3Role0Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  protocol2Role1BoundCallees

theorem protocol3Role0Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol3Role0Callees input :=
  protocol2Role1BoundCallees_hold input

def protocol3Role0Signature : Signature := ⟨projectionKeys, false, true, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol3Role0Pattern : InputPattern definition3.inputs := (.cons .optional (.cons .optional (.cons .optional .nil)))

noncomputable def protocol3Role0Form : Form protocol3Role0Signature.laws calleeKeys protocol3Role0Pattern.scope [.index] :=
  (.apply ⟨5, by decide⟩ (⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "first" (by change (Values (Argument [] [(.component .index), (.component .index), (.component .boolean)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.apply ⟨4, by decide⟩ (⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "second" (by change (Values (Argument [] [(.tuple [.index]), (.component .index), (.component .index), (.component .boolean)]) [(.component .index), (.component .index)]); exact (.cons (.read .here .here) (.cons (.input (.there (.there .here))) .nil))) (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "outer" (.letOp (.mark "before") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "inner") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner") (.cons (.there .here) (.cons .here .nil)) (.cons (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) (.ret (.cons .here .nil)))))) (.input (.there (.there .here))) (.cons (.read .here .here) .nil) .nil (.done (.cons (.read .here .here) .nil)))))

noncomputable def protocol3Role0Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (_b2 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol3Role0Callees ⟨5, by decide⟩) ((ctx).enter "first" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol3Role0Callees ⟨4, by decide⟩) ((ctx).enter "second" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b3).get .here) (.cons (b1) .nil)))).bind fun (b4 : (Values (Component (assignment F G)) [.index])) =>
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons ((b4).get .here) .nil) .nil ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.letOp (.mark "before") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "inner") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner") (.cons (.there .here) (.cons .here .nil)) (.cons (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) (.ret (.cons .here .nil)))))))).bind fun (b5 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b5).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role0_calls : protocol3Role0Form.CallsMatch := by
  kernel_rfl

theorem protocol3Role0_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (b2 : (Option (Bool))) :
    ((protocol3Role0Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (protocol3Role0Callees) (.cons (b0) (.cons (b1) (.cons (b2) .nil)))) =
      (protocol3Role0Process ctx (b0) (b1) (b2)) := by
  kernel_rfl

theorem protocol3Role0_sites :
    Zkc.Source.Structured.NormalForm.sites protocol3Role0Form [] =
      [(⟨[], "apply", "first"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "apply", "second"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0], "repeat", "outer"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol3Role0_normalized : normalize protocol3Role0Signature definition3.body 0 2 protocol3Role0Pattern = .ok protocol3Role0Form := by
  kernel_rfl

noncomputable def protocol3Role0View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition3.outputs) :=
  (protocol3Role0Process ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input)).get (.there (.there .here)))).bind fun out =>
    .done (maskValues (ctx.roles 0) (ctx.mapScopes definition3.outputScopes) out)

theorem protocol3Role0_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 0 2)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition3.signature ctx
      (ctx.roles 0) input = protocol3Role0View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition3 definition3_member
    protocol3Role0Signature 0 2 protocol3Role0Pattern
    protocol3Role0Form protocol3Role0_normalized protocol3Role0_calls
    (projectionResults (F := F) (G := G)) protocol3Role0Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol3Role0Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input) = (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get (.there .here)) (.cons ((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input).get (.there (.there .here))) .nil))) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 0) (ctx.mapScopes definition3.outputScopes) out))
    (protocol3Role0_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input)).get .here) (((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 0) (ctx.mapScopes definition3.inputScopes) input)).get (.there (.there .here)))))

theorem protocol3Role0_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition3.signature ctx (ctx.roles 0) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 0 2) (protocol3Role0View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol3Role0_invocation ctx distinct input⟩

theorem protocol3Role0_participant
    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G 0 input = protocol3Role0View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans (protocol3Role0_invocation {} (RosterDistinct.root _ _) input)

noncomputable def protocol3Role0BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol2Role1BoundCallees) ⟨6, by decide +kernel⟩ (fun ctx binders => protocol3Role0View (F := F) (G := G) ctx ((optionalPattern [.index, .index, .boolean]).environment (ringModel F G) binders)))

theorem protocol3Role0BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol3Role0BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol2Role1BoundCallees) ⟨6, by decide +kernel⟩ _ input (callees_hold input) (protocol2Role1BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol3Role0_invocation ctx distinct _

noncomputable def protocol3Role1Callees : CalleeProcesses (ringModel F G) calleeKeys :=
  protocol2Role1BoundCallees

theorem protocol3Role1Callees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol3Role1Callees input :=
  protocol2Role1BoundCallees_hold input

def protocol3Role1Signature : Signature := ⟨projectionKeys, false, true, program.payload.definitions.map (·.helper), calleeKeys⟩
def protocol3Role1Pattern : InputPattern definition3.inputs := (.cons .optional (.cons .optional (.cons .optional .nil)))

noncomputable def protocol3Role1Form : Form protocol3Role1Signature.laws calleeKeys protocol3Role1Pattern.scope [.index] :=
  (.apply ⟨4, by decide⟩ (⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "first" (by change (Values (Argument [] [(.component .index), (.component .index), (.component .boolean)]) [(.component .index), (.component .index)]); exact (.cons (.input .here) (.cons (.input (.there .here)) .nil))) (.apply ⟨5, by decide⟩ (⟨"middle", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "second" (by change (Values (Argument [] [(.tuple [.index]), (.component .index), (.component .index), (.component .boolean)]) [(.component .index), (.component .index)]); exact (.cons (.read .here .here) (.cons (.input (.there (.there .here))) .nil))) (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "outer" (.letOp (.mark "before") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "inner") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner") (.cons (.there .here) (.cons .here .nil)) (.cons (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) (.ret (.cons .here .nil)))))) (.input (.there (.there .here))) (.cons (.read .here .here) .nil) .nil (.done (.cons (.read .here .here) .nil)))))

noncomputable def protocol3Role1Process (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (_b2 : (Option (Bool))) :
    (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  ((protocol3Role1Callees ⟨4, by decide⟩) ((ctx).enter "first" [1, 0]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons (b0) (.cons (b1) .nil)))).bind fun (b3 : (Values (Component (assignment F G)) [.index])) =>
  ((protocol3Role1Callees ⟨5, by decide⟩) ((ctx).enter "second" [0, 1]) (by change (Binders (ringModel F G) [(.component .index), (.component .index)]); exact (.cons ((b3).get .here) (.cons (b1) .nil)))).bind fun (b4 : (Values (Component (assignment F G)) [.index])) =>
  ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).run (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (b0) (.cons ((b4).get .here) .nil) .nil ((Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)).callback (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) (.letOp (.mark "before") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "before") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "inner") .nil .nil (.letOp (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "inner") (.cons (.there .here) (.cons .here .nil)) (.cons (.letOp (.mark "inside") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [0, 1] "inside") (.cons .here (.cons (.there .here) .nil)) .nil (.letOp (.mark "again") .nil .nil (.letOp (.protocolApply (⟨"leaf", ["Alice", "Bob"], [.index, .index], [.index], [[0, 1], [0, 1]], [[0, 1]]⟩ : ProtocolSignature) [1, 0] "again") (.cons (.there .here) (.cons .here .nil)) .nil (.ret (.cons .here .nil)))))) .nil) (.ret (.cons .here .nil)))))))).bind fun (b5 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b5).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem protocol3Role1_calls : protocol3Role1Form.CallsMatch := by
  kernel_rfl

theorem protocol3Role1_presentation (ctx : ProtocolContext) (b0 : (Option (Nat))) (b1 : (Option (Nat))) (b2 : (Option (Bool))) :
    ((protocol3Role1Form).denote (ringModel F G) ((helpers (F := F) (G := G) payload).toOn) (projectionResults (F := F) (G := G)) (ctx) (Runs.uniform (helpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (protocol3Role1Callees) (.cons (b0) (.cons (b1) (.cons (b2) .nil)))) =
      (protocol3Role1Process ctx (b0) (b1) (b2)) := by
  kernel_rfl

theorem protocol3Role1_sites :
    Zkc.Source.Structured.NormalForm.sites protocol3Role1Form [] =
      [(⟨[], "apply", "first"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0], "apply", "second"⟩ : Zkc.Source.Structured.NormalForm.Site), (⟨[0, 0], "repeat", "outer"⟩ : Zkc.Source.Structured.NormalForm.Site)] := by
  decide +kernel

theorem protocol3Role1_normalized : normalize protocol3Role1Signature definition3.body 1 2 protocol3Role1Pattern = .ok protocol3Role1Form := by
  kernel_rfl

noncomputable def protocol3Role1View (ctx : ProtocolContext)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) definition3.outputs) :=
  (protocol3Role1Process ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input)).get (.there (.there .here)))).bind fun out =>
    .done (maskValues (ctx.roles 1) (ctx.mapScopes definition3.outputScopes) out)

theorem protocol3Role1_invocation (ctx : ProtocolContext)
    (distinct : RosterDistinct ctx 1 2)
    (input : Values (Component (assignment F G)) definition3.inputs) :
    invokeProtocol (payload.plainProtocolTable F G) definition3.signature ctx
      (ctx.roles 1) input = protocol3Role1View ctx input := by
  have equation := invocation (F := F) (G := G) payload definition3 definition3_member
    protocol3Role1Signature 1 2 protocol3Role1Pattern
    protocol3Role1Form protocol3Role1_normalized protocol3Role1_calls
    (projectionResults (F := F) (G := G)) protocol3Role1Callees ctx distinct input
    (optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input))
    (optional_environment _ _) (projectionLaws_hold _) (protocol3Role1Callees_hold _)
  have binderEta : optionalBinders (ringModel F G) (maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input) = (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get .here) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get (.there .here)) (.cons ((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input).get (.there (.there .here))) .nil))) := by
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  rw [binderEta] at equation
  exact equation.trans (congrArg (fun p => p.bind fun out => .done (maskValues (ctx.roles 1) (ctx.mapScopes definition3.outputScopes) out))
    (protocol3Role1_presentation (F := F) (G := G) ctx (((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input)).get .here) (((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input)).get (.there .here)) (((maskValues (ctx.roles 1) (ctx.mapScopes definition3.inputScopes) input)).get (.there (.there .here)))))

theorem protocol3Role1_certificate :
    Zkc.Verification.Certificate sourceImported
      (fun p ctx input => invokeProtocol (p.payload.plainProtocolTable F G) definition3.signature ctx (ctx.roles 1) input)
      (Zkc.Source.Structured.Bindings.Contract (fun ctx _ => RosterDistinct ctx 1 2) (protocol3Role1View (F := F) (G := G))) := by
  exact ⟨fun ctx input distinct => protocol3Role1_invocation ctx distinct input⟩

theorem protocol3Role1_participant
    (input : Values (Component (assignment F G)) program.payload.entry.inputs) :
    program.participant F G 1 input = protocol3Role1View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans (protocol3Role1_invocation {} (RosterDistinct.root _ _) input)

noncomputable def protocol3Role1BoundCallees : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (protocol3Role0BoundCallees) ⟨7, by decide +kernel⟩ (fun ctx binders => protocol3Role1View (F := F) (G := G) ctx ((optionalPattern [.index, .index, .boolean]).environment (ringModel F G) binders)))

theorem protocol3Role1BoundCallees_hold {inputs : List Ty}
    (input : Values (Component (assignment F G)) inputs) :
    CalleesHold (payload.plainProtocolTable F G) protocol3Role1BoundCallees input := by
  apply callees_update _ (actualCallees payload calleeKeys) (protocol3Role0BoundCallees) ⟨7, by decide +kernel⟩ _ input (callees_hold input) (protocol3Role0BoundCallees_hold input)
  intro ctx binders distinct
  exact protocol3Role1_invocation ctx distinct _

end
end Tests.Generated.NestedRoleBindings
