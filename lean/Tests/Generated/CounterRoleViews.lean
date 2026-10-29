module

public import Tests.Generated.CounterRoleBindingsCallbacks
public import Zkc.Source.Structured.LoopPresentation
public import Zkc.Source.Structured.InputVisibility
public import Zkc.Source.Structured.PlainHelpers
public import Zkc.Source.Structured.OccurrencePresentation
public import Zkc.Source.Structured.ProtocolPresentation

@[expose] public section

/-! Generated scope-derived source presentations. Regenerate with the Lean role-view printer. -/
namespace Tests.Generated.CounterRoleViews
open Zkc.Source Zkc.Source.Structured NormalForm Zkc.Source.Structured.Bindings
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option smartUnfolding false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxErrors 12
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
noncomputable section
variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]

abbrev program : Program := Tests.StructuredBindingsGeneric.program
abbrev payload := program.payload
abbrev calleeKeys := Tests.Generated.CounterRoleBindings.calleeKeys

theorem observedCallees_hold
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) {inputs : List Ty}
  (input : Values (Component (assignment F G)) inputs) :
  CalleesHold protocols (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) input := by
  apply ProtocolPresentation.callees_hold _ _ _ masked
  · intro entry binders others
    fin_cases entry <;> exact optional_fill _ _ binders others
  · intro entry
    fin_cases entry <;> decide +kernel

namespace Protocol0

abbrev bodyDefinition : CheckedProtocol := payload.protocols.get ⟨0, by decide +kernel⟩
abbrev bodyInputs : List Ty := [.index, .index]
abbrev bodyOutputs : List Ty := [.index]
abbrev bodyBody := bodyDefinition.body
theorem bodyBody_checked : bodyDefinition.body = bodyBody := rfl
theorem bodyBody_raw : bodyDefinition.raw = bodyBody.erase := by kernel_rfl

abbrev callback0State : List Ty := [.index]
abbrev callback0Captures : List Ty := []
abbrev callback0Maximum := 3
abbrev callback0Spec : RepeatSpec := (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec)
def callback0Body := Tests.Generated.CounterRoleBindingsCallbacks.protocol0Role0Callback0Body
theorem callback0_selected : findRepeat "round" bodyDefinition.body = some ⟨_, _, callback0Body⟩ := Tests.Generated.CounterRoleBindingsCallbacks.protocol0Role0Callback0_selected

def bodyFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, .index], [.index]) :=
  fun args => bodyBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def callback0Fn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, .index], [.index]) :=
  fun args => callback0Body.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

theorem callback0_occurrence (ctx : ProtocolContext) (self : Nat)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (args : Values (Component (assignment F G)) (.index :: (callback0Spec.state ++ callback0Spec.captures))) :
  callback0Body.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) self protocols ctx Occurrence.iterations) args.get =
    (callback0Fn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  simpa only [callback0Fn] using
    (OccurrencePresentation.local_callback payload ctx self callback0Body (by kernel_rfl) protocols
      (payload.plainProtocolTable F G) args)

def role0Callback0Finish : Values (fun _ : Ty => Carried) [.index] :=
  (.cons .optional .nil)

def role0Callback0State (input1 : (Option (Nat))) : Values (Component (assignment F G)) [.index] :=
  (.cons input1 .nil)

theorem role0Callback0State_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0) (input1 : (Option (Nat))) :
  maskValues self (ctx.mapScopes [[0, 1]]) (role0Callback0State (F := F) (G := G) input1) = (role0Callback0State (F := F) (G := G) input1) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 0 role0Callback0Finish _ rfl (.cons input1 .nil)

def role0Callback0Signature : Signature := ⟨[], true, false, [], calleeKeys⟩
def role0Callback0Pattern : InputPattern [.index, .index] := (.cons .present (.cons .optional .nil))
noncomputable def role0Callback0Form : Form role0Callback0Signature.laws role0Callback0Signature.callees role0Callback0Pattern.scope [.index] :=
  (.done (.cons (.input (.there .here)) .nil))

noncomputable def role0Callback0Process (input1 : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [(.index, true)])) :=
  .done (input1)

theorem role0Callback0_normalized : normalize role0Callback0Signature callback0Body 0 2 role0Callback0Pattern = .ok role0Callback0Form := by kernel_rfl
theorem role0Callback0_calls : role0Callback0Form.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem role0Callback0_finishes : role0Callback0Form.finishes role0Callback0Finish = true := by kernel_rfl

theorem role0Callback0_presentation (ctx : ProtocolContext) (input0 : Nat) (input1 : (Option (Nat))) :
  ((role0Callback0Form).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional .nil)) (.cons input0 (.cons input1 .nil))) = (role0Callback0Process (F := F) (G := G) input1) := by kernel_rfl

theorem role0Callback0_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (input0 : Nat) (input1 : (Option (Nat))) :
  callback0Body.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((role0Callback0Pattern).environment (ringModel F G) (.cons input0 (.cons input1 .nil))).get =
  role0Callback0Form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons input0 (.cons input1 .nil)) :=
  normalize_occurrence_sound role0Callback0Signature callback0Body 0 2
    role0Callback0Pattern role0Callback0Form role0Callback0_normalized role0Callback0_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem role0Callback0_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (input0 : Nat) (input1 : (Option (Nat))) :
  callback0Fn (F := F) (G := G) ctx self (.cons (some input0) ((role0Callback0State (F := F) (G := G) input1).append .nil)) =
    (role0Callback0Process (F := F) (G := G) input1).bind (fun result => .done (role0Callback0State (F := F) (G := G) result)) := by
  subst self
  exact (callback_sound_uniform role0Callback0Signature callback0Body 0 2 role0Callback0Pattern role0Callback0Finish role0Callback0Form
    role0Callback0_normalized role0Callback0_calls role0Callback0_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons input0 (.cons input1 .nil)) _ (by kernel_rfl) (emptyLaws _ _) (Tests.Generated.CounterRoleBindings.callees_hold _)).trans
    (congrArg₂ PIR.Process.bind (role0Callback0_presentation ctx input0 input1)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem role0Callback0_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (count : Nat) (bounded : count ≤ callback0Spec.maximum)
  (state : Values (Component (assignment F G)) [.index]) (initial : Tuple (assignment F G) (carried role0Callback0Finish))
  (start : maskValues (ctx.roles 0) (ctx.mapScopes callback0Spec.stateScopes) state = (role0Callback0State (F := F) (G := G) initial)) :
  denoteRepeat callback0Spec ctx (ctx.roles 0) (some count) state .nil (callback0Fn ctx (ctx.roles 0)) =
    (Finite.fold (fun result index => (role0Callback0Process (F := F) (G := G) result)) (List.range' 0 count) initial).bind (fun result => .done (role0Callback0State (F := F) (G := G) result)) := by
  exact LoopPresentation.presentUniform callback0Spec ctx (ctx.roles 0) (by simp) _ _
    (fun result => (role0Callback0State (F := F) (G := G) result)) (fun result => role0Callback0State_masked ctx _ rfl result)
    (fun result index => (role0Callback0Process (F := F) (G := G) result)) (fun result index => role0Callback0_process ctx _ rfl distinct index result) count bounded state initial start

def role0Signature : Signature := ⟨[], true, false, [], calleeKeys⟩
def role0Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))
noncomputable def role0Form : Form role0Signature.laws role0Signature.callees role0Pattern.scope [.index] :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" callback0Body (.input .here) (.cons (.input (.there .here)) .nil) .nil (.done (.cons (.read .here .here) .nil)))

noncomputable def role0Process (ctx : ProtocolContext) (input0 : (Option (Nat))) (input1 : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  (denoteRepeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) ctx (ctx.roles 0) (input0) (.cons (input1) .nil) .nil (callback0Fn ctx (ctx.roles 0))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem role0_normalized : normalize role0Signature bodyBody 0 2 role0Pattern = .ok role0Form := by kernel_rfl
theorem role0_calls : role0Form.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem role0_presentation (ctx : ProtocolContext) (input0 : (Option (Nat))) (input1 : (Option (Nat))) :
  ((role0Form).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons input0 (.cons input1 .nil))) = (role0Process (F := F) (G := G) ctx input0 input1) := by kernel_rfl

theorem role0_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (input0 : (Option (Nat))) (input1 : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((role0Pattern.environment (ringModel F G) (.cons input0 (.cons input1 .nil)))) = (role0Process (F := F) (G := G) ctx input0 input1) := by
  subst self
  exact (sound_uniform role0Signature bodyBody 0 2 role0Pattern role0Form
    role0_normalized role0_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons input0 (.cons input1 .nil)) _ rfl (emptyLaws _ _) (Tests.Generated.CounterRoleBindings.callees_hold _)).trans
    (role0_presentation ctx input0 input1)

theorem role0_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (input0 : (Option (Nat))) (input1 : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((role0Pattern.environment (ringModel F G) (.cons input0 (.cons input1 .nil)))).get =
  role0Form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons input0 (.cons input1 .nil)) :=
  normalize_occurrence_sound role0Signature bodyBody 0 2
    role0Pattern role0Form role0_normalized role0_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def role0View (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [.index, .index]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.index]) :=
  ((role0Process (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))).bind fun out => .done (.cons (out.get .here) .nil)

theorem role0_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (input : Values (Component (assignment F G)) [.index, .index]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 0) input = role0View ctx input := by
  have environment : role0Pattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) .nil)) =
      maskValues (ctx.roles 0) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) role0Signature 0 2 role0Pattern role0Form
    role0_normalized role0_calls (emptyResults _) (actualCallees payload calleeKeys) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) .nil))
    environment (emptyLaws _ _) (Tests.Generated.CounterRoleBindings.callees_hold _)
  rw [role0_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

theorem role0_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 0 input = role0View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans
    (role0_invocation {} (RosterDistinct.root _ _) input)

end Protocol0

noncomputable def boundCallees0 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ (fun ctx binders => Protocol0.role0View (F := F) (G := G) ctx ((optionalPattern [.index, .index]).environment (ringModel F G) binders)))
theorem boundCallees0_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees0 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ _ input (Tests.Generated.CounterRoleBindings.callees_hold input) (Tests.Generated.CounterRoleBindings.callees_hold input)
  intro ctx binders distinct
  exact Protocol0.role0_invocation ctx distinct _

namespace Protocol0

def role1Callback0Finish : Values (fun _ : Ty => Carried) [.index] :=
  (.cons .optional .nil)

def role1Callback0State (input1 : (Option (Nat))) : Values (Component (assignment F G)) [.index] :=
  (.cons input1 .nil)

theorem role1Callback0State_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1) (input1 : (Option (Nat))) :
  maskValues self (ctx.mapScopes [[0, 1]]) (role1Callback0State (F := F) (G := G) input1) = (role1Callback0State (F := F) (G := G) input1) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 1 role1Callback0Finish _ rfl (.cons input1 .nil)

def role1Callback0Signature : Signature := ⟨[], true, false, [], calleeKeys⟩
def role1Callback0Pattern : InputPattern [.index, .index] := (.cons .present (.cons .optional .nil))
noncomputable def role1Callback0Form : Form role1Callback0Signature.laws role1Callback0Signature.callees role1Callback0Pattern.scope [.index] :=
  (.done (.cons (.input (.there .here)) .nil))

noncomputable def role1Callback0Process (input1 : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [(.index, true)])) :=
  .done (input1)

theorem role1Callback0_normalized : normalize role1Callback0Signature callback0Body 1 2 role1Callback0Pattern = .ok role1Callback0Form := by kernel_rfl
theorem role1Callback0_calls : role1Callback0Form.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem role1Callback0_finishes : role1Callback0Form.finishes role1Callback0Finish = true := by kernel_rfl

theorem role1Callback0_presentation (ctx : ProtocolContext) (input0 : Nat) (input1 : (Option (Nat))) :
  ((role1Callback0Form).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional .nil)) (.cons input0 (.cons input1 .nil))) = (role1Callback0Process (F := F) (G := G) input1) := by kernel_rfl

theorem role1Callback0_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (input0 : Nat) (input1 : (Option (Nat))) :
  callback0Body.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((role1Callback0Pattern).environment (ringModel F G) (.cons input0 (.cons input1 .nil))).get =
  role1Callback0Form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons input0 (.cons input1 .nil)) :=
  normalize_occurrence_sound role1Callback0Signature callback0Body 1 2
    role1Callback0Pattern role1Callback0Form role1Callback0_normalized role1Callback0_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem role1Callback0_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (input0 : Nat) (input1 : (Option (Nat))) :
  callback0Fn (F := F) (G := G) ctx self (.cons (some input0) ((role1Callback0State (F := F) (G := G) input1).append .nil)) =
    (role1Callback0Process (F := F) (G := G) input1).bind (fun result => .done (role1Callback0State (F := F) (G := G) result)) := by
  subst self
  exact (callback_sound_uniform role1Callback0Signature callback0Body 1 2 role1Callback0Pattern role1Callback0Finish role1Callback0Form
    role1Callback0_normalized role1Callback0_calls role1Callback0_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons input0 (.cons input1 .nil)) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees0_hold _)).trans
    (congrArg₂ PIR.Process.bind (role1Callback0_presentation ctx input0 input1)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem role1Callback0_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (count : Nat) (bounded : count ≤ callback0Spec.maximum)
  (state : Values (Component (assignment F G)) [.index]) (initial : Tuple (assignment F G) (carried role1Callback0Finish))
  (start : maskValues (ctx.roles 1) (ctx.mapScopes callback0Spec.stateScopes) state = (role1Callback0State (F := F) (G := G) initial)) :
  denoteRepeat callback0Spec ctx (ctx.roles 1) (some count) state .nil (callback0Fn ctx (ctx.roles 1)) =
    (Finite.fold (fun result index => (role1Callback0Process (F := F) (G := G) result)) (List.range' 0 count) initial).bind (fun result => .done (role1Callback0State (F := F) (G := G) result)) := by
  exact LoopPresentation.presentUniform callback0Spec ctx (ctx.roles 1) (by simp) _ _
    (fun result => (role1Callback0State (F := F) (G := G) result)) (fun result => role1Callback0State_masked ctx _ rfl result)
    (fun result index => (role1Callback0Process (F := F) (G := G) result)) (fun result index => role1Callback0_process ctx _ rfl distinct index result) count bounded state initial start

def role1Signature : Signature := ⟨[], true, false, [], calleeKeys⟩
def role1Pattern : InputPattern [.index, .index] := (.cons .optional (.cons .optional .nil))
noncomputable def role1Form : Form role1Signature.laws role1Signature.callees role1Pattern.scope [.index] :=
  (.repeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) "round" callback0Body (.input .here) (.cons (.input (.there .here)) .nil) .nil (.done (.cons (.read .here .here) .nil)))

noncomputable def role1Process (ctx : ProtocolContext) (input0 : (Option (Nat))) (input1 : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.index])) :=
  (denoteRepeat (⟨[.index], [], [0, 1], [[0, 1]], 3⟩ : RepeatSpec) ctx (ctx.roles 1) (input0) (.cons (input1) .nil) .nil (callback0Fn ctx (ctx.roles 1))).bind fun (b2 : (Values (Component (assignment F G)) [.index])) =>
  .done ((.cons ((b2).get .here) .nil) : (Values (Component (assignment F G)) [.index]))

theorem role1_normalized : normalize role1Signature bodyBody 1 2 role1Pattern = .ok role1Form := by kernel_rfl
theorem role1_calls : role1Form.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem role1_presentation (ctx : ProtocolContext) (input0 : (Option (Nat))) (input1 : (Option (Nat))) :
  ((role1Form).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (.cons input0 (.cons input1 .nil))) = (role1Process (F := F) (G := G) ctx input0 input1) := by kernel_rfl

theorem role1_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (input0 : (Option (Nat))) (input1 : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((role1Pattern.environment (ringModel F G) (.cons input0 (.cons input1 .nil)))) = (role1Process (F := F) (G := G) ctx input0 input1) := by
  subst self
  exact (sound_uniform role1Signature bodyBody 1 2 role1Pattern role1Form
    role1_normalized role1_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons input0 (.cons input1 .nil)) _ rfl (emptyLaws _ _) (boundCallees0_hold _)).trans
    (role1_presentation ctx input0 input1)

theorem role1_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (input0 : (Option (Nat))) (input1 : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((role1Pattern.environment (ringModel F G) (.cons input0 (.cons input1 .nil)))).get =
  role1Form.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons input0 (.cons input1 .nil)) :=
  normalize_occurrence_sound role1Signature bodyBody 1 2
    role1Pattern role1Form role1_normalized role1_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def role1View (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [.index, .index]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.index]) :=
  ((role1Process (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)))).bind fun out => .done (.cons (out.get .here) .nil)

theorem role1_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (input : Values (Component (assignment F G)) [.index, .index]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 1) input = role1View ctx input := by
  have environment : role1Pattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) .nil)) =
      maskValues (ctx.roles 1) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) role1Signature 1 2 role1Pattern role1Form
    role1_normalized role1_calls (emptyResults _) (boundCallees0) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) .nil))
    environment (emptyLaws _ _) (boundCallees0_hold _)
  rw [role1_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

theorem role1_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 1 input = role1View {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans
    (role1_invocation {} (RosterDistinct.root _ _) input)

end Protocol0

noncomputable def boundCallees1 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees0) ⟨1, by decide +kernel⟩ (fun ctx binders => Protocol0.role1View (F := F) (G := G) ctx ((optionalPattern [.index, .index]).environment (ringModel F G) binders)))
theorem boundCallees1_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees1 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees0) ⟨1, by decide +kernel⟩ _ input (Tests.Generated.CounterRoleBindings.callees_hold input) (boundCallees0_hold input)
  intro ctx binders distinct
  exact Protocol0.role1_invocation ctx distinct _

namespace Protocol0

end Protocol0

end
end Tests.Generated.CounterRoleViews
