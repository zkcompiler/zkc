module

public import ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks
public import Zkc.Source.Structured.LoopPresentation
public import Zkc.Source.Structured.InputVisibility
public import Zkc.Source.Structured.PlainHelpers
public import Zkc.Source.Structured.OccurrencePresentation
public import Zkc.Source.Structured.ProtocolPresentation

@[expose] public section

/-! Generated scope-derived source presentations. Regenerate with the Lean role-view printer. -/
namespace ZkcExamples.Structured.Generated.Presentations.Gkr
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

abbrev program : Program := ZkcExamples.Structured.GkrSourceViews.program
abbrev payload := program.payload
abbrev calleeKeys := ZkcExamples.Structured.Generated.Bindings.GkrRounds.calleeKeys

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

namespace Rounds

abbrev roundsDefinition : CheckedProtocol := payload.protocols.get ⟨0, by decide +kernel⟩
abbrev roundsInputs : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
abbrev roundsOutputs : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev roundsBody := roundsDefinition.body
theorem roundsBody_checked : roundsDefinition.body = roundsBody := rfl
theorem roundsBody_raw : roundsDefinition.raw = roundsBody.erase := by kernel_rfl

abbrev roundState : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev roundCaptures : List Ty := [(.service "random.bls12-381.fr/0")]
abbrev roundMaximum := 4
abbrev roundSpec : RepeatSpec := (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec)
def roundBody := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol0Role0Callback0Body
theorem round_selected : findRepeat "s9" roundsDefinition.body = some ⟨_, _, roundBody⟩ := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol0Role0Callback0_selected

def roundsFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  fun args => roundsBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def roundFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  fun args => roundBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

theorem round_occurrence (ctx : ProtocolContext) (self : Nat)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (args : Values (Component (assignment F G)) (.index :: (roundSpec.state ++ roundSpec.captures))) :
  roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) self protocols ctx Occurrence.iterations) args.get =
    (roundFn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  simpa only [roundFn] using
    (OccurrencePresentation.local_callback payload ctx self roundBody (by kernel_rfl) protocols
      (payload.plainProtocolTable F G) args)

def proverFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent .nil)))))))

def proverState (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (point : (Option ((List F)))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons none (.cons none .nil)))))))

theorem proverState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (point : (Option ((List F)))) :
  maskValues self (ctx.mapScopes [[0], [0], [0], [0], [0], [1], [1]]) (proverState (F := F) (G := G) add mul left right point) = (proverState (F := F) (G := G) add mul left right point) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 0 proverFinish _ rfl (.cons add (.cons mul (.cons left (.cons right (.cons point .nil)))))

def proverSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent (.cons .optional .nil)))))))))
noncomputable def proverForm : Form proverSignature.laws proverSignature.callees proverPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input (.there .here)) (.halt .incomplete) (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.halt .incomplete) (.strict (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there .here)))) (.cons (.var (.there (.there .here))) (.cons (.var (.there .here)) (.cons (.var .here) .nil)))) (.send (.field "bls12-381.fr") "label_726f756e64_0" 1 (.result .here .here) (.send (.field "bls12-381.fr") "label_726f756e64_1" 1 (.result .here (.there .here)) (.send (.field "bls12-381.fr") "label_726f756e64_2" 1 (.result .here (.there (.there .here))) (.receive (.field "bls12-381.fr") "label_64656c6976657279_0" 1 (.strict (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var (.there (.there (.there .here)))) (.cons (.var (.there (.there .here))) (.cons (.var .here) .nil))))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil)) (.done (.cons (.present (.result (.there (.there .here)) .here)) (.cons (.present (.result (.there (.there .here)) (.there .here))) (.cons (.present (.result (.there (.there .here)) (.there (.there .here)))) (.cons (.present (.result (.there (.there .here)) (.there (.there (.there .here))))) (.cons (.present (.result .here .here)) (.cons .absent (.cons .absent .nil))))))))))))))))))))

noncomputable def proverProcess (ctx : ProtocolContext) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (point : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true), ((.vector "bls12-381.fr"), true), ((.vector "bls12-381.fr"), true), ((.vector "bls12-381.fr"), true), ((.vector "bls12-381.fr"), true)])) :=
  match add with
  | none =>
    .halt .incomplete
  | some b7 =>
    match mul with
    | none =>
      .halt .incomplete
    | some b8 =>
      match left with
      | none =>
        .halt .incomplete
      | some b9 =>
        match right with
        | none =>
          .halt .incomplete
        | some b10 =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e2f65d17b480da5da0270346faa1bd036c7a5f879e30f4b2b6bac1224b05e394", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b7) (.cons (b8) (.cons (b9) (.cons (b10) .nil))))).bind fun (b11 : (Values (assignment F G) [(.field "bls12-381.fr"), (.field "bls12-381.fr"), (.field "bls12-381.fr")])) =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_0") ((ctx).roles 1) ((b11).get .here)) fun _ =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_1") ((ctx).roles 1) ((b11).get (.there .here))) fun _ =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_2") ((ctx).roles 1) ((b11).get (.there (.there .here)))) fun _ =>
          .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 1)) fun (b12 : F) =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_36caebca415236dd6aac1763c9a581b89c25a00e62432b484ec92ae08e6a0099", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) (.cons (b7) (.cons (b8) (.cons (b9) (.cons (b10) (.cons (b12) .nil)))))).bind fun (b13 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")])) =>
          match point with
          | none =>
            .halt .incomplete
          | some b14 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b14) (.cons (b12) .nil))).bind fun (b15 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
            .done (((some ((b13).get .here))), (((some ((b13).get (.there .here)))), (((some ((b13).get (.there (.there .here))))), (((some ((b13).get (.there (.there (.there .here)))))), ((some ((b15).get .here)))))))

theorem prover_normalized : normalize proverSignature roundBody 0 2 proverPattern = .ok proverForm := by kernel_rfl
theorem prover_calls : proverForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem prover_finishes : proverForm.finishes proverFinish = true := by kernel_rfl

theorem prover_presentation (ctx : ProtocolContext) (index : Nat) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (point : (Option ((List F)))) (service : (Option (Nat))) :
  ((proverForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent .nil)))))))) (.cons index (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons service .nil)))))))) = (proverProcess (F := F) (G := G) ctx add mul left right point) := by kernel_rfl

theorem prover_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (point : (Option ((List F)))) (service : (Option (Nat))) :
  roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverPattern).environment (ringModel F G) (.cons index (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons service .nil)))))))).get =
  proverForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons service .nil))))))) :=
  normalize_occurrence_sound proverSignature roundBody 0 2
    proverPattern proverForm prover_normalized prover_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem prover_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (index : Nat) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (point : (Option ((List F)))) (service : (Option (Nat))) :
  roundFn (F := F) (G := G) ctx self (.cons (some index) ((proverState (F := F) (G := G) add mul left right point).append (.cons service .nil))) =
    (proverProcess (F := F) (G := G) ctx add mul left right point).bind (fun result => .done (proverState (F := F) (G := G) result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)) := by
  subst self
  exact (callback_sound_uniform proverSignature roundBody 0 2 proverPattern proverFinish proverForm
    prover_normalized prover_calls prover_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons index (.cons add (.cons mul (.cons left (.cons right (.cons point (.cons service .nil))))))) _ (by kernel_rfl) (emptyLaws _ _) (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold _)).trans
    (congrArg₂ PIR.Process.bind (prover_presentation ctx index add mul left right point service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem prover_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ roundSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried proverFinish))
  (start : maskValues (ctx.roles 0) (ctx.mapScopes roundSpec.stateScopes) state = (proverState (F := F) (G := G) initial.1 initial.2.1 initial.2.2.1 initial.2.2.2.1 initial.2.2.2.2)) :
  denoteRepeat roundSpec ctx (ctx.roles 0) (some count) state (.cons service .nil) (roundFn ctx (ctx.roles 0)) =
    (Finite.fold (fun result index => (proverProcess (F := F) (G := G) ctx result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)) (List.range' 0 count) initial).bind (fun result => .done (proverState (F := F) (G := G) result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)) := by
  exact LoopPresentation.presentUniform roundSpec ctx (ctx.roles 0) (by simp) _ _
    (fun result => (proverState (F := F) (G := G) result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)) (fun result => proverState_masked ctx _ rfl result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)
    (fun result index => (proverProcess (F := F) (G := G) ctx result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2)) (fun result index => prover_process ctx _ rfl distinct index result.1 result.2.1 result.2.2.1 result.2.2.2.1 result.2.2.2.2 service) count bounded state initial start

def proverRoundsSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverRoundsPattern : InputPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent (.cons .optional (.cons .absent .nil))))))))
noncomputable def proverRoundsForm : Form proverRoundsSignature.laws proverRoundsSignature.callees proverRoundsPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.strict (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) "s9" roundBody (.input (.there (.there (.there (.there (.there .here)))))) (.cons (.input (.there .here)) (.cons (.input (.there (.there .here))) (.cons (.input (.there (.there (.there .here)))) (.cons (.input (.there (.there (.there (.there .here))))) (.cons (.present (.result .here .here)) (.cons .absent (.cons .absent .nil))))))) (.cons .absent .nil) (.done (.cons (.read .here (.there (.there (.there (.there .here))))) (.cons (.read .here .here) (.cons (.read .here (.there .here)) (.cons (.read .here (.there (.there .here))) (.cons (.read .here (.there (.there (.there .here)))) (.cons .absent (.cons .absent .nil))))))))))

noncomputable def proverRoundsProcess (ctx : ProtocolContext) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (rounds : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) :=
  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil).bind fun (b5 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
  (denoteRepeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 0) (rounds) (.cons (add) (.cons (mul) (.cons (left) (.cons (right) (.cons ((some ((b5).get .here))) (.cons (none) (.cons (none) .nil))))))) (.cons (none) .nil) (roundFn ctx (ctx.roles 0))).bind fun (b6 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
  .done ((.cons ((b6).get (.there (.there (.there (.there .here))))) (.cons ((b6).get .here) (.cons ((b6).get (.there .here)) (.cons ((b6).get (.there (.there .here))) (.cons ((b6).get (.there (.there (.there .here)))) (.cons (none) (.cons (none) .nil))))))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))

theorem proverRounds_normalized : normalize proverRoundsSignature roundsBody 0 2 proverRoundsPattern = .ok proverRoundsForm := by kernel_rfl
theorem proverRounds_calls : proverRoundsForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem proverRounds_presentation (ctx : ProtocolContext) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (rounds : (Option (Nat))) :
  ((proverRoundsForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons add (.cons mul (.cons left (.cons right (.cons rounds .nil)))))) = (proverRoundsProcess (F := F) (G := G) ctx add mul left right rounds) := by kernel_rfl

theorem proverRounds_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (rounds : (Option (Nat))) :
  roundsFn (F := F) (G := G) ctx self ((proverRoundsPattern.environment (ringModel F G) (.cons add (.cons mul (.cons left (.cons right (.cons rounds .nil))))))) = (proverRoundsProcess (F := F) (G := G) ctx add mul left right rounds) := by
  subst self
  exact (sound_uniform proverRoundsSignature roundsBody 0 2 proverRoundsPattern proverRoundsForm
    proverRounds_normalized proverRounds_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons add (.cons mul (.cons left (.cons right (.cons rounds .nil))))) _ rfl (emptyLaws _ _) (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold _)).trans
    (proverRounds_presentation ctx add mul left right rounds)

theorem proverRounds_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (add : (Option ((List F)))) (mul : (Option ((List F)))) (left : (Option ((List F)))) (right : (Option ((List F)))) (rounds : (Option (Nat))) :
  roundsBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverRoundsPattern.environment (ringModel F G) (.cons add (.cons mul (.cons left (.cons right (.cons rounds .nil))))))).get =
  proverRoundsForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons add (.cons mul (.cons left (.cons right (.cons rounds .nil))))) :=
  normalize_occurrence_sound proverRoundsSignature roundsBody 0 2
    proverRoundsPattern proverRoundsForm proverRounds_normalized proverRounds_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def proverRoundsView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  ((proverRoundsProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)) (input.get (.there (.there .here))) (input.get (.there (.there (.there .here)))) (input.get (.there (.there (.there (.there (.there (.there .here))))))))).bind fun out => .done (.cons (out.get .here) (.cons (out.get (.there .here)) (.cons (out.get (.there (.there .here))) (.cons (out.get (.there (.there (.there .here)))) (.cons (out.get (.there (.there (.there (.there .here))))) (.cons none (.cons none .nil)))))))

theorem proverRounds_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) roundsDefinition.signature ctx (ctx.roles 0) input = proverRoundsView ctx input := by
  have environment : proverRoundsPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil))))) =
      maskValues (ctx.roles 0) (ctx.mapScopes roundsDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct roundsDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload roundsDefinition (List.get_mem _ _) proverRoundsSignature 0 2 proverRoundsPattern proverRoundsForm
    proverRounds_normalized proverRounds_calls (emptyResults _) (actualCallees payload calleeKeys) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))
    environment (emptyLaws _ _) (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold _)
  rw [proverRounds_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct roundsDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out; rfl

end Rounds

noncomputable def boundCallees0 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ (fun ctx binders => Rounds.proverRoundsView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees0_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees0 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold input) (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold input)
  intro ctx binders distinct
  exact Rounds.proverRounds_invocation ctx distinct _

namespace Rounds

def verifierFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional .nil)))))))

def verifierState (point : (Option ((List F)))) (claim : (Option (F))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons none (.cons none (.cons none (.cons none (.cons none (.cons point (.cons claim .nil)))))))

theorem verifierState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1) (point : (Option ((List F)))) (claim : (Option (F))) :
  maskValues self (ctx.mapScopes [[0], [0], [0], [0], [0], [1], [1]]) (verifierState (F := F) (G := G) point claim) = (verifierState (F := F) (G := G) point claim) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 1 verifierFinish _ rfl (.cons point (.cons claim .nil))

def verifierSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional .nil)))))))))
noncomputable def verifierForm : Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.receive (.field "bls12-381.fr") "label_726f756e64_0" 0 (.receive (.field "bls12-381.fr") "label_726f756e64_1" 0 (.receive (.field "bls12-381.fr") "label_726f756e64_2" 0 (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.guard (.field "bls12-381.fr") (.var .here) (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there .here)))) (.cons (.var (.there (.there (.there .here)))) .nil)) .here) (.cons (.var (.there (.there .here))) .nil)) .here) (.cons (.var (.there .here)) .nil)) .here) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.halt .incomplete) (.query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657279_0" 0 (.var .here) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there (.there (.there (.there .here)))))) .nil)) .here) .nil)) .here) .nil)) .here) .nil)) .here)) .nil))))))))))))))))))

noncomputable def verifierProcess (ctx : ProtocolContext) (service : (Option (Nat))) (point : (Option ((List F)))) (claim : (Option (F))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true), ((.field "bls12-381.fr"), true)])) :=
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_0") ((ctx).roles 0)) fun (b4 : F) =>
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_1") ((ctx).roles 0)) fun (b5 : F) =>
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_2") ((ctx).roles 0)) fun (b6 : F) =>
  match claim with
  | none =>
    .halt .incomplete
  | some b7 =>
    @ite _ ((b7) = (((((((b4) + (b4))) + (b5))) + (b6)))) (Equality.decide (ringModel F G) (.field "bls12-381.fr") (b7) (((((((b4) + (b4))) + (b5))) + (b6))))
      (
        match service with
        | none =>
          .halt .incomplete
        | some b8 =>
          .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6368616c6c656e6765") "bls12-381.fr" (.cons (b8) .nil)) fun (b9 : F) =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 0) (b9)) fun _ =>
          match point with
          | none =>
            .halt .incomplete
          | some b10 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b10) (.cons (b9) .nil))).bind fun (b11 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
            .done (((some ((b11).get .here))), ((some (((b4) + (((b9) * (((b5) + (((b9) * (b6)))))))))))))
      (.halt .reject)

theorem verifier_normalized : normalize verifierSignature roundBody 1 2 verifierPattern = .ok verifierForm := by kernel_rfl
theorem verifier_calls : verifierForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem verifier_finishes : verifierForm.finishes verifierFinish = true := by kernel_rfl

theorem verifier_presentation (ctx : ProtocolContext) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (service : (Option (Nat))) :
  ((verifierForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional .nil)))))))) (.cons index (.cons point (.cons claim (.cons service .nil))))) = (verifierProcess (F := F) (G := G) ctx service point claim) := by kernel_rfl

theorem verifier_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (service : (Option (Nat))) :
  roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierPattern).environment (ringModel F G) (.cons index (.cons point (.cons claim (.cons service .nil))))).get =
  verifierForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons point (.cons claim (.cons service .nil)))) :=
  normalize_occurrence_sound verifierSignature roundBody 1 2
    verifierPattern verifierForm verifier_normalized verifier_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem verifier_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (service : (Option (Nat))) :
  roundFn (F := F) (G := G) ctx self (.cons (some index) ((verifierState (F := F) (G := G) point claim).append (.cons service .nil))) =
    (verifierProcess (F := F) (G := G) ctx service point claim).bind (fun result => .done (verifierState (F := F) (G := G) result.1 result.2)) := by
  subst self
  exact (callback_sound_uniform verifierSignature roundBody 1 2 verifierPattern verifierFinish verifierForm
    verifier_normalized verifier_calls verifier_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons index (.cons point (.cons claim (.cons service .nil)))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees0_hold _)).trans
    (congrArg₂ PIR.Process.bind (verifier_presentation ctx index point claim service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem verifier_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ roundSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried verifierFinish))
  (start : maskValues (ctx.roles 1) (ctx.mapScopes roundSpec.stateScopes) state = (verifierState (F := F) (G := G) initial.1 initial.2)) :
  denoteRepeat roundSpec ctx (ctx.roles 1) (some count) state (.cons service .nil) (roundFn ctx (ctx.roles 1)) =
    (Finite.fold (fun result index => (verifierProcess (F := F) (G := G) ctx service result.1 result.2)) (List.range' 0 count) initial).bind (fun result => .done (verifierState (F := F) (G := G) result.1 result.2)) := by
  exact LoopPresentation.presentUniform roundSpec ctx (ctx.roles 1) (by simp) _ _
    (fun result => (verifierState (F := F) (G := G) result.1 result.2)) (fun result => verifierState_masked ctx _ rfl result.1 result.2)
    (fun result index => (verifierProcess (F := F) (G := G) ctx service result.1 result.2)) (fun result index => verifier_process ctx _ rfl distinct index result.1 result.2 service) count bounded state initial start

def verifierRoundsSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierRoundsPattern : InputPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")] := (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil))))))))
noncomputable def verifierRoundsForm : Form verifierRoundsSignature.laws verifierRoundsSignature.callees verifierRoundsPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input .here) (.halt .incomplete) (.split (.input (.there (.there .here))) (.halt .incomplete) (.strict (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) "s9" roundBody (.input (.there (.there (.there (.there (.there .here)))))) (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil))))))) (.cons (.input (.there (.there (.there (.there (.there (.there .here))))))) .nil) (.split (.read .here (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.split (.read (.there .here) (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.strict (⟨"zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.done (.cons (.read (.there (.there (.there .here))) (.there (.there (.there (.there .here))))) (.cons (.read (.there (.there (.there .here))) .here) (.cons (.read (.there (.there (.there .here))) (.there .here)) (.cons (.read (.there (.there (.there .here))) (.there (.there .here))) (.cons (.read (.there (.there (.there .here))) (.there (.there (.there .here)))) (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil)))))))))))))))

noncomputable def verifierRoundsProcess (ctx : ProtocolContext) (initialPoint : (Option ((List F)))) (claim : (Option (F))) (rounds : (Option (Nat))) (service : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) :=
  match initialPoint with
  | none =>
    .halt .incomplete
  | some b4 =>
    match claim with
    | none =>
      .halt .incomplete
    | some b5 =>
      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b4) (.cons (b5) .nil))).bind fun (b6 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      (denoteRepeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 1) (rounds) (.cons (none) (.cons (none) (.cons (none) (.cons (none) (.cons (none) (.cons ((some ((b6).get .here))) (.cons ((some ((b6).get (.there .here)))) .nil))))))) (.cons (service) .nil) (roundFn ctx (ctx.roles 1))).bind fun (b7 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      match (b7).get (.there (.there (.there (.there (.there .here))))) with
      | none =>
        .halt .incomplete
      | some b8 =>
        match (b7).get (.there (.there (.there (.there (.there (.there .here)))))) with
        | none =>
          .halt .incomplete
        | some b9 =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_bcddf8825098d44ae9ce732a7b45754c16637e2a47a4c9f29ef9a21612daeaa3", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b8) (.cons (b9) .nil))).bind fun (b10 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
          .done ((.cons ((b7).get (.there (.there (.there (.there .here))))) (.cons ((b7).get .here) (.cons ((b7).get (.there .here)) (.cons ((b7).get (.there (.there .here))) (.cons ((b7).get (.there (.there (.there .here)))) (.cons ((some ((b10).get .here))) (.cons ((some ((b10).get (.there .here)))) .nil))))))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))

theorem verifierRounds_normalized : normalize verifierRoundsSignature roundsBody 1 2 verifierRoundsPattern = .ok verifierRoundsForm := by kernel_rfl
theorem verifierRounds_calls : verifierRoundsForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem verifierRounds_presentation (ctx : ProtocolContext) (initialPoint : (Option ((List F)))) (claim : (Option (F))) (rounds : (Option (Nat))) (service : (Option (Nat))) :
  ((verifierRoundsForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (.cons initialPoint (.cons claim (.cons rounds (.cons service .nil))))) = (verifierRoundsProcess (F := F) (G := G) ctx initialPoint claim rounds service) := by kernel_rfl

theorem verifierRounds_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (initialPoint : (Option ((List F)))) (claim : (Option (F))) (rounds : (Option (Nat))) (service : (Option (Nat))) :
  roundsFn (F := F) (G := G) ctx self ((verifierRoundsPattern.environment (ringModel F G) (.cons initialPoint (.cons claim (.cons rounds (.cons service .nil)))))) = (verifierRoundsProcess (F := F) (G := G) ctx initialPoint claim rounds service) := by
  subst self
  exact (sound_uniform verifierRoundsSignature roundsBody 1 2 verifierRoundsPattern verifierRoundsForm
    verifierRounds_normalized verifierRounds_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons initialPoint (.cons claim (.cons rounds (.cons service .nil)))) _ rfl (emptyLaws _ _) (boundCallees0_hold _)).trans
    (verifierRounds_presentation ctx initialPoint claim rounds service)

theorem verifierRounds_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (initialPoint : (Option ((List F)))) (claim : (Option (F))) (rounds : (Option (Nat))) (service : (Option (Nat))) :
  roundsBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierRoundsPattern.environment (ringModel F G) (.cons initialPoint (.cons claim (.cons rounds (.cons service .nil)))))).get =
  verifierRoundsForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons initialPoint (.cons claim (.cons rounds (.cons service .nil)))) :=
  normalize_occurrence_sound verifierRoundsSignature roundsBody 1 2
    verifierRoundsPattern verifierRoundsForm verifierRounds_normalized verifierRounds_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def verifierRoundsView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  ((verifierRoundsProcess (F := F) (G := G) ctx (input.get (.there (.there (.there (.there .here))))) (input.get (.there (.there (.there (.there (.there .here)))))) (input.get (.there (.there (.there (.there (.there (.there .here))))))) (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))))).bind fun out => .done (.cons none (.cons none (.cons none (.cons none (.cons none (.cons (out.get (.there (.there (.there (.there (.there .here)))))) (.cons (out.get (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))))

theorem verifierRounds_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) roundsDefinition.signature ctx (ctx.roles 1) input = verifierRoundsView ctx input := by
  have environment : verifierRoundsPattern.environment (ringModel F G) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))) =
      maskValues (ctx.roles 1) (ctx.mapScopes roundsDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct roundsDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload roundsDefinition (List.get_mem _ _) verifierRoundsSignature 1 2 verifierRoundsPattern verifierRoundsForm
    verifierRounds_normalized verifierRounds_calls (emptyResults _) (boundCallees0) ctx distinct input (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))))
    environment (emptyLaws _ _) (boundCallees0_hold _)
  rw [verifierRounds_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct roundsDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out; rfl

end Rounds

noncomputable def boundCallees1 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees0) ⟨1, by decide +kernel⟩ (fun ctx binders => Rounds.verifierRoundsView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees1_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees1 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees0) ⟨1, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold input) (boundCallees0_hold input)
  intro ctx binders distinct
  exact Rounds.verifierRounds_invocation ctx distinct _

namespace Rounds

end Rounds

namespace Input

abbrev inputDefinition : CheckedProtocol := payload.protocols.get ⟨1, by decide +kernel⟩
abbrev inputInputs : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev inputOutputs : List Ty := [.boolean]
abbrev inputBody := inputDefinition.body
theorem inputBody_checked : inputDefinition.body = inputBody := rfl
theorem inputBody_raw : inputDefinition.raw = inputBody.erase := by kernel_rfl

def inputFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]) :=
  fun args => inputBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def verifierSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierPattern : InputPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] := (.cons .optional (.cons .optional (.cons .optional .nil)))
noncomputable def verifierForm : Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [.boolean] :=
  (.split (.input .here) (.halt .incomplete) (.split (.input (.there (.there .here))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.strict (⟨"zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper) (.cons (.var (.there (.there .here))) (.cons (.var (.there .here)) (.cons (.var .here) .nil))) (.done (.cons (.present (.result .here .here)) .nil))))))

noncomputable def verifierProcess (values : (Option ((List F)))) (point : (Option ((List F)))) (claim : (Option (F))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  match values with
  | none =>
    .halt .incomplete
  | some b3 =>
    match point with
    | none =>
      .halt .incomplete
    | some b4 =>
      match claim with
      | none =>
        .halt .incomplete
      | some b5 =>
        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_d74cb9bd9ed782590145b66a573f8104fca0e842c109c7d034296431308fc6b9", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean]⟩ : Helper) (.cons (b3) (.cons (b4) (.cons (b5) .nil)))).bind fun (b6 : (Values (assignment F G) [.boolean])) =>
        .done ((.cons ((some ((b6).get .here))) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem verifier_normalized : normalize verifierSignature inputBody 0 1 verifierPattern = .ok verifierForm := by kernel_rfl
theorem verifier_calls : verifierForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem verifier_presentation (ctx : ProtocolContext) (values : (Option ((List F)))) (point : (Option ((List F)))) (claim : (Option (F))) :
  ((verifierForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (boundCallees1) (.cons values (.cons point (.cons claim .nil)))) = (verifierProcess (F := F) (G := G) values point claim) := by kernel_rfl

theorem verifier_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 1) (values : (Option ((List F)))) (point : (Option ((List F)))) (claim : (Option (F))) :
  inputFn (F := F) (G := G) ctx self ((verifierPattern.environment (ringModel F G) (.cons values (.cons point (.cons claim .nil))))) = (verifierProcess (F := F) (G := G) values point claim) := by
  subst self
  exact (sound_uniform verifierSignature inputBody 0 1 verifierPattern verifierForm
    verifier_normalized verifier_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees1)
    (.cons values (.cons point (.cons claim .nil))) _ rfl (emptyLaws _ _) (boundCallees1_hold _)).trans
    (verifier_presentation ctx values point claim)

theorem verifier_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 1)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (values : (Option ((List F)))) (point : (Option ((List F)))) (claim : (Option (F))) :
  inputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((verifierPattern.environment (ringModel F G) (.cons values (.cons point (.cons claim .nil))))).get =
  verifierForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons values (.cons point (.cons claim .nil))) :=
  normalize_occurrence_sound verifierSignature inputBody 0 1
    verifierPattern verifierForm verifier_normalized verifier_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def verifierView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  ((verifierProcess (F := F) (G := G) (input.get .here) (input.get (.there .here)) (input.get (.there (.there .here))))).bind fun out => .done (.cons (out.get .here) .nil)

theorem verifier_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 1)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :
  invokeProtocol (payload.plainProtocolTable F G) inputDefinition.signature ctx (ctx.roles 0) input = verifierView ctx input := by
  have environment : verifierPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) .nil))) =
      maskValues (ctx.roles 0) (ctx.mapScopes inputDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct inputDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload inputDefinition (List.get_mem _ _) verifierSignature 0 1 verifierPattern verifierForm
    verifier_normalized verifier_calls (emptyResults _) (boundCallees1) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) .nil)))
    environment (emptyLaws _ _) (boundCallees1_hold _)
  rw [verifier_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct inputDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

end Input

noncomputable def boundCallees2 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees1) ⟨2, by decide +kernel⟩ (fun ctx binders => Input.verifierView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]).environment (ringModel F G) binders)))
theorem boundCallees2_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees2 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees1) ⟨2, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold input) (boundCallees1_hold input)
  intro ctx binders distinct
  exact Input.verifier_invocation ctx distinct _

namespace Input

end Input

namespace Root

abbrev gkrDefinition : CheckedProtocol := payload.protocols.get ⟨2, by decide +kernel⟩
abbrev gkrInputs : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]
abbrev gkrOutputs : List Ty := [.boolean]
abbrev gkrBody := gkrDefinition.body
theorem gkrBody_checked : gkrDefinition.body = gkrBody := rfl
theorem gkrBody_raw : gkrDefinition.raw = gkrBody.erase := by kernel_rfl

abbrev outputState : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]
abbrev outputCaptures : List Ty := [(.service "random.bls12-381.fr/0")]
abbrev outputMaximum := 4
abbrev outputSpec : RepeatSpec := (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[1], [0]], 4⟩ : RepeatSpec)
def outputBody := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol2Role0Callback0Body
theorem output_selected : findRepeat "s37" gkrDefinition.body = some ⟨_, _, outputBody⟩ := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol2Role0Callback0_selected

abbrev layerState : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev layerCaptures : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]
abbrev layerMaximum := 4
abbrev layerSpec : RepeatSpec := (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [0, 1], [[0], [1], [1]], 4⟩ : RepeatSpec)
def layerBody := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol2Role0Callback1Body
theorem layer_selected : findRepeat "s57" gkrDefinition.body = some ⟨_, _, layerBody⟩ := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol2Role0Callback1_selected

abbrev coefficientState : List Ty := [(.vector "bls12-381.fr")]
abbrev coefficientCaptures : List Ty := [(.vector "bls12-381.fr")]
abbrev coefficientMaximum := 4
abbrev coefficientSpec : RepeatSpec := (⟨[(.vector "bls12-381.fr")], [(.vector "bls12-381.fr")], [0, 1], [[1]], 4⟩ : RepeatSpec)
def coefficientBody := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol2Role0Callback2Body
theorem coefficient_selected : findRepeat "s91" gkrDefinition.body = some ⟨_, _, coefficientBody⟩ := ZkcExamples.Structured.Generated.Bindings.GkrRoundsCallbacks.protocol2Role0Callback2_selected

def gkrFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [.boolean]) :=
  fun args => gkrBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def outputFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]) :=
  fun args => outputBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def layerFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  fun args => layerBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def coefficientFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.vector "bls12-381.fr")]) :=
  fun args => coefficientBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

theorem output_occurrence (ctx : ProtocolContext) (self : Nat)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (args : Values (Component (assignment F G)) (.index :: (outputSpec.state ++ outputSpec.captures))) :
  outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) self protocols ctx Occurrence.iterations) args.get =
    (outputFn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  simpa only [outputFn] using
    (OccurrencePresentation.local_callback payload ctx self outputBody (by kernel_rfl) protocols
      (payload.plainProtocolTable F G) args)

theorem coefficient_occurrence (ctx : ProtocolContext) (self : Nat)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (args : Values (Component (assignment F G)) (.index :: (coefficientSpec.state ++ coefficientSpec.captures))) :
  coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) self protocols ctx Occurrence.iterations) args.get =
    (coefficientFn (F := F) (G := G) ctx self args).interpret Occurrence.actions := by
  simpa only [coefficientFn] using
    (OccurrencePresentation.local_callback payload ctx self coefficientBody (by kernel_rfl) protocols
      (payload.plainProtocolTable F G) args)

def proverOutputFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] :=
  (.cons .absent (.cons .optional .nil))

def proverOutputState (point : (Option ((List F)))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] :=
  (.cons none (.cons point .nil))

theorem proverOutputState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0) (point : (Option ((List F)))) :
  maskValues self (ctx.mapScopes [[1], [0]]) (proverOutputState (F := F) (G := G) point) = (proverOutputState (F := F) (G := G) point) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 0 proverOutputFinish _ rfl (.cons point .nil)

def proverOutputSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverOutputPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .absent (.cons .optional (.cons .optional .nil))))
noncomputable def proverOutputForm : Form proverOutputSignature.laws proverOutputSignature.callees proverOutputPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] :=
  (.receive (.field "bls12-381.fr") "label_6f75747075745f64656c6976657279_0" 1 (.split (.input (.there (.there .here))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done (.cons .absent (.cons (.present (.result .here .here)) .nil))))))

noncomputable def proverOutputProcess (ctx : ProtocolContext) (point : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true)])) :=
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_6f75747075745f64656c6976657279_0") ((ctx).roles 1)) fun (b3 : F) =>
  match point with
  | none =>
    .halt .incomplete
  | some b4 =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b4) (.cons (b3) .nil))).bind fun (b5 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
    .done ((some ((b5).get .here)))

theorem proverOutput_normalized : normalize proverOutputSignature outputBody 0 2 proverOutputPattern = .ok proverOutputForm := by kernel_rfl
theorem proverOutput_calls : proverOutputForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem proverOutput_finishes : proverOutputForm.finishes proverOutputFinish = true := by kernel_rfl

theorem proverOutput_presentation (ctx : ProtocolContext) (index : Nat) (point : (Option ((List F)))) (service : (Option (Nat))) :
  ((proverOutputForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (boundCallees2) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .absent (.cons .optional .nil))) (.cons index (.cons point (.cons service .nil)))) = (proverOutputProcess (F := F) (G := G) ctx point) := by kernel_rfl

theorem proverOutput_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (point : (Option ((List F)))) (service : (Option (Nat))) :
  outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverOutputPattern).environment (ringModel F G) (.cons index (.cons point (.cons service .nil)))).get =
  proverOutputForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons point (.cons service .nil))) :=
  normalize_occurrence_sound proverOutputSignature outputBody 0 2
    proverOutputPattern proverOutputForm proverOutput_normalized proverOutput_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem proverOutput_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (index : Nat) (point : (Option ((List F)))) (service : (Option (Nat))) :
  outputFn (F := F) (G := G) ctx self (.cons (some index) ((proverOutputState (F := F) (G := G) point).append (.cons service .nil))) =
    (proverOutputProcess (F := F) (G := G) ctx point).bind (fun result => .done (proverOutputState (F := F) (G := G) result)) := by
  subst self
  exact (callback_sound_uniform proverOutputSignature outputBody 0 2 proverOutputPattern proverOutputFinish proverOutputForm
    proverOutput_normalized proverOutput_calls proverOutput_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees2)
    (.cons index (.cons point (.cons service .nil))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees2_hold _)).trans
    (congrArg₂ PIR.Process.bind (proverOutput_presentation ctx index point service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem proverOutput_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ outputSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried proverOutputFinish))
  (start : maskValues (ctx.roles 0) (ctx.mapScopes outputSpec.stateScopes) state = (proverOutputState (F := F) (G := G) initial)) :
  denoteRepeat outputSpec ctx (ctx.roles 0) (some count) state (.cons service .nil) (outputFn ctx (ctx.roles 0)) =
    (Finite.fold (fun result index => (proverOutputProcess (F := F) (G := G) ctx result)) (List.range' 0 count) initial).bind (fun result => .done (proverOutputState (F := F) (G := G) result)) := by
  exact LoopPresentation.presentUniform outputSpec ctx (ctx.roles 0) (by simp) _ _
    (fun result => (proverOutputState (F := F) (G := G) result)) (fun result => proverOutputState_masked ctx _ rfl result)
    (fun result index => (proverOutputProcess (F := F) (G := G) ctx result)) (fun result index => proverOutput_process ctx _ rfl distinct index result service) count bounded state initial start

def proverLayerFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons .optional (.cons .absent (.cons .absent .nil)))

def proverLayerState (point : (Option ((List F)))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons point (.cons none (.cons none .nil)))

theorem proverLayerState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0) (point : (Option ((List F)))) :
  maskValues self (ctx.mapScopes [[0], [1], [1]]) (proverLayerState (F := F) (G := G) point) = (proverLayerState (F := F) (G := G) point) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 0 proverLayerFinish _ rfl (.cons point .nil)

def proverLayerSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverLayerPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .optional (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))))))))))
noncomputable def proverLayerForm : Form proverLayerSignature.laws proverLayerSignature.callees proverLayerPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.halt .incomplete) (.strict (⟨"zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var (.there (.there (.there .here)))) (.cons (.var (.there (.there .here))) (.cons (.var (.there .here)) (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) .nil))))))) (.strict (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.var (.there (.there .here))) .nil))) (.strict (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.var (.there (.there (.there .here)))) .nil))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.halt .incomplete) (.strict (⟨"zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) (.cons (.result (.there (.there .here)) .here) (.cons (.result (.there .here) .here) (.cons (.var .here) (.cons (.result (.there (.there (.there .here))) .here) (.cons (.var (.there (.there (.there (.there .here))))) .nil))))) (.apply ⟨0, by decide⟩ (⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩ : ProtocolSignature) [0, 1] "label_6c656674" (by change (Zkc.Source.Values (Zkc.Source.Structured.NormalForm.Argument [] [(.results [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]), (.value (.vector "bls12-381.fr")), (.results [(.vector "bls12-381.fr")]), (.results [(.vector "bls12-381.fr")]), (.results [(.vector "bls12-381.fr")]), (.value .index), (.value .index), (.value .index), (.value (.vector "bls12-381.fr")), (.value (.vector "bls12-381.fr")), (.value (.vector "bls12-381.fr")), (.value .index), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) (.cons (.present (.result .here (.there (.there .here)))) (.cons (.present (.result .here (.there (.there (.there .here))))) (.cons .absent (.cons .absent (.cons (.present (.var (.there (.there (.there (.there (.there .here))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))) .nil))))))))) (.apply ⟨0, by decide⟩ (⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩ : ProtocolSignature) [0, 1] "label_7269676874" (by change (Zkc.Source.Values (Zkc.Source.Structured.NormalForm.Argument [] [(.tuple [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.results [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]), (.value (.vector "bls12-381.fr")), (.results [(.vector "bls12-381.fr")]), (.results [(.vector "bls12-381.fr")]), (.results [(.vector "bls12-381.fr")]), (.value .index), (.value .index), (.value .index), (.value (.vector "bls12-381.fr")), (.value (.vector "bls12-381.fr")), (.value (.vector "bls12-381.fr")), (.value .index), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons (.read .here (.there .here)) (.cons (.read .here (.there (.there .here))) (.cons (.read .here (.there (.there (.there .here)))) (.cons (.read .here (.there (.there (.there (.there .here))))) (.cons .absent (.cons .absent (.cons (.present (.var (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) .nil))))))))) (.split (.read (.there .here) .here) (.halt .incomplete) (.split (.read (.there .here) .here) (.halt .incomplete) (.strict (⟨"zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))) .here) (.cons (.var (.there .here)) (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)))) (.strict (⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.result .here .here) (.cons (.index 0) .nil)) (.send (.field "bls12-381.fr") "label_6c696e655f636f6e7374616e74_0" 1 (.result .here .here) (.repeat (⟨[(.vector "bls12-381.fr")], [(.vector "bls12-381.fr")], [0, 1], [[1]], 4⟩ : RepeatSpec) "s91" coefficientBody (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons .absent .nil) (.cons (.present (.result (.there .here) .here)) .nil) (.receive (.field "bls12-381.fr") "label_6c696e655f64656c6976657279_0" 1 (.strict (⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var .here) .nil))) (.done (.cons (.present (.result .here .here)) (.cons .absent (.cons .absent .nil)))))))))))))))))))))))))

noncomputable def proverLayerProcess (ctx : ProtocolContext) (index : Nat) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) (point : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true)])) :=
  match add with
  | none =>
    .halt .incomplete
  | some b9 =>
    match mul with
    | none =>
      .halt .incomplete
    | some b10 =>
      match inputs with
      | none =>
        .halt .incomplete
      | some b11 =>
        match layers with
        | none =>
          .halt .incomplete
        | some b12 =>
          match selector with
          | none =>
            .halt .incomplete
          | some b13 =>
            match width with
            | none =>
              .halt .incomplete
            | some b14 =>
              (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_8c63ad97d926a7762c597860addde408bcd2077ea9cda1b99df123dc13e64af6", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b9) (.cons (b10) (.cons (b11) (.cons (b12) (.cons (b13) (.cons (b14) (.cons (index) .nil)))))))).bind fun (b15 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
              (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b9) (.cons (index) (.cons (b13) .nil)))).bind fun (b16 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
              (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b10) (.cons (index) (.cons (b13) .nil)))).bind fun (b17 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
              match point with
              | none =>
                .halt .incomplete
              | some b18 =>
                (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_d1f2756b99b17aad26e4b85a966eec4c9419609618b22e3ee7f8a3349cb1e33b", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) (.cons ((b16).get .here) (.cons ((b17).get .here) (.cons (b18) (.cons ((b15).get .here) (.cons (b14) .nil)))))).bind fun (b19 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")])) =>
                ((fun ctx binders => Rounds.proverRoundsView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))) ((ctx).enter "label_6c656674" [0, 1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons ((some ((b19).get .here))) (.cons ((some ((b19).get (.there .here)))) (.cons ((some ((b19).get (.there (.there .here))))) (.cons ((some ((b19).get (.there (.there (.there .here)))))) (.cons (none) (.cons (none) (.cons ((some (b14))) (.cons (service) .nil)))))))))).bind fun (b20 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
                ((fun ctx binders => Rounds.proverRoundsView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))) ((ctx).enter "label_7269676874" [0, 1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons ((b20).get (.there .here)) (.cons ((b20).get (.there (.there .here))) (.cons ((b20).get (.there (.there (.there .here)))) (.cons ((b20).get (.there (.there (.there (.there .here))))) (.cons (none) (.cons (none) (.cons ((some (b14))) (.cons (service) .nil)))))))))).bind fun (b21 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
                match (b20).get .here with
                | none =>
                  .halt .incomplete
                | some b22 =>
                  match (b21).get .here with
                  | none =>
                    .halt .incomplete
                  | some b23 =>
                    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_91fe8ea73b5db3432f90fc8fe9725c8455fce8782b4cc4d2839d05826de71b8f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons ((b15).get .here) (.cons (b22) (.cons (b23) (.cons (b14) .nil))))).bind fun (b24 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_6ba53ec68a0230031d706e4a93e78f80425c51108d34ecc0a5aa5681eded9c8e", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")]⟩ : Helper) (.cons ((b24).get .here) (.cons (0) .nil))).bind fun (b25 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
                    .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f636f6e7374616e74_0") ((ctx).roles 1) ((b25).get .here)) fun _ =>
                    (denoteRepeat (⟨[(.vector "bls12-381.fr")], [(.vector "bls12-381.fr")], [0, 1], [[1]], 4⟩ : RepeatSpec) ctx (ctx.roles 0) ((some (b14))) (.cons (none) .nil) (.cons ((some ((b24).get .here))) .nil) (coefficientFn ctx (ctx.roles 0))).bind fun (_b26 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr")])) =>
                    .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f64656c6976657279_0") ((ctx).roles 1)) fun (b27 : F) =>
                    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b22) (.cons (b23) (.cons (b27) .nil)))).bind fun (b28 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                    .done ((some ((b28).get .here)))

theorem proverLayer_normalized : normalize proverLayerSignature layerBody 0 2 proverLayerPattern = .ok proverLayerForm := by kernel_rfl
theorem proverLayer_calls : proverLayerForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem proverLayer_finishes : proverLayerForm.finishes proverLayerFinish = true := by kernel_rfl

theorem proverLayer_presentation (ctx : ProtocolContext) (index : Nat) (point : (Option ((List F)))) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  ((proverLayerForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (boundCallees2) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional (.cons .absent (.cons .absent .nil)))) (.cons index (.cons point (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))))) = (proverLayerProcess (F := F) (G := G) ctx index inputs add mul layers selector width service point) := by kernel_rfl

theorem proverLayer_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (point : (Option ((List F)))) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverLayerPattern).environment (ringModel F G) (.cons index (.cons point (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))))).get =
  proverLayerForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons point (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))) :=
  normalize_occurrence_sound proverLayerSignature layerBody 0 2
    proverLayerPattern proverLayerForm proverLayer_normalized proverLayer_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem proverLayer_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (index : Nat) (point : (Option ((List F)))) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  layerFn (F := F) (G := G) ctx self (.cons (some index) ((proverLayerState (F := F) (G := G) point).append (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))) =
    (proverLayerProcess (F := F) (G := G) ctx index inputs add mul layers selector width service point).bind (fun result => .done (proverLayerState (F := F) (G := G) result)) := by
  subst self
  exact (callback_sound_uniform proverLayerSignature layerBody 0 2 proverLayerPattern proverLayerFinish proverLayerForm
    proverLayer_normalized proverLayer_calls proverLayer_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees2)
    (.cons index (.cons point (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees2_hold _)).trans
    (congrArg₂ PIR.Process.bind (proverLayer_presentation ctx index point inputs add mul layers selector width service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem proverLayer_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ layerSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried proverLayerFinish))
  (start : maskValues (ctx.roles 0) (ctx.mapScopes layerSpec.stateScopes) state = (proverLayerState (F := F) (G := G) initial)) :
  denoteRepeat layerSpec ctx (ctx.roles 0) (some count) state (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))) (layerFn ctx (ctx.roles 0)) =
    (Finite.fold (fun result index => (proverLayerProcess (F := F) (G := G) ctx index inputs add mul layers selector width service result)) (List.range' 0 count) initial).bind (fun result => .done (proverLayerState (F := F) (G := G) result)) := by
  exact LoopPresentation.presentUniform layerSpec ctx (ctx.roles 0) (by simp) _ _
    (fun result => (proverLayerState (F := F) (G := G) result)) (fun result => proverLayerState_masked ctx _ rfl result)
    (fun result index => (proverLayerProcess (F := F) (G := G) ctx index inputs add mul layers selector width service result)) (fun result index => proverLayer_process ctx _ rfl distinct index result inputs add mul layers selector width service) count bounded state initial start

def proverCoefficientFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr")] :=
  (.cons .absent .nil)

def proverCoefficientState  : Values (Component (assignment F G)) [(.vector "bls12-381.fr")] :=
  (.cons none .nil)

theorem proverCoefficientState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)  :
  maskValues self (ctx.mapScopes [[1]]) (proverCoefficientState (F := F) (G := G)) = (proverCoefficientState (F := F) (G := G)) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 0 proverCoefficientFinish _ rfl .nil

def proverCoefficientSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverCoefficientPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr")] := (.cons .present (.cons .absent (.cons .optional .nil)))
noncomputable def proverCoefficientForm : Form proverCoefficientSignature.laws proverCoefficientSignature.callees proverCoefficientPattern.scope [(.vector "bls12-381.fr")] :=
  (.split (.input (.there .here)) (.halt .incomplete) (.strict (⟨"zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.send (.field "bls12-381.fr") "label_6c696e655f636f656666696369656e74_0" 1 (.result .here .here) (.done (.cons .absent .nil)))))

noncomputable def proverCoefficientProcess (ctx : ProtocolContext) (index : Nat) (line : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [])) :=
  match line with
  | none =>
    .halt .incomplete
  | some b2 =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_ca5df6081733f8afff4ae42147eb8eba3338d5a96600a7155f619346f19e4b47", .local, [(.vector "bls12-381.fr"), .index], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (b2) (.cons (index) .nil))).bind fun (b3 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
    .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f636f656666696369656e74_0") ((ctx).roles 1) ((b3).get .here)) fun _ =>
    .done ()

theorem proverCoefficient_normalized : normalize proverCoefficientSignature coefficientBody 0 2 proverCoefficientPattern = .ok proverCoefficientForm := by kernel_rfl
theorem proverCoefficient_calls : proverCoefficientForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem proverCoefficient_finishes : proverCoefficientForm.finishes proverCoefficientFinish = true := by kernel_rfl

theorem proverCoefficient_presentation (ctx : ProtocolContext) (index : Nat) (line : (Option ((List F)))) :
  ((proverCoefficientForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (boundCallees2) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .absent .nil)) (.cons index (.cons line .nil))) = (proverCoefficientProcess (F := F) (G := G) ctx index line) := by kernel_rfl

theorem proverCoefficient_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (line : (Option ((List F)))) :
  coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverCoefficientPattern).environment (ringModel F G) (.cons index (.cons line .nil))).get =
  proverCoefficientForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons line .nil)) :=
  normalize_occurrence_sound proverCoefficientSignature coefficientBody 0 2
    proverCoefficientPattern proverCoefficientForm proverCoefficient_normalized proverCoefficient_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem proverCoefficient_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (index : Nat) (line : (Option ((List F)))) :
  coefficientFn (F := F) (G := G) ctx self (.cons (some index) ((proverCoefficientState (F := F) (G := G)).append (.cons line .nil))) =
    (proverCoefficientProcess (F := F) (G := G) ctx index line).bind (fun result => .done (proverCoefficientState (F := F) (G := G))) := by
  subst self
  exact (callback_sound_uniform proverCoefficientSignature coefficientBody 0 2 proverCoefficientPattern proverCoefficientFinish proverCoefficientForm
    proverCoefficient_normalized proverCoefficient_calls proverCoefficient_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees2)
    (.cons index (.cons line .nil)) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees2_hold _)).trans
    (congrArg₂ PIR.Process.bind (proverCoefficient_presentation ctx index line)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem proverCoefficient_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2) (line : (Option ((List F))))
  (count : Nat) (bounded : count ≤ coefficientSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried proverCoefficientFinish))
  (start : maskValues (ctx.roles 0) (ctx.mapScopes coefficientSpec.stateScopes) state = (proverCoefficientState (F := F) (G := G))) :
  denoteRepeat coefficientSpec ctx (ctx.roles 0) (some count) state (.cons line .nil) (coefficientFn ctx (ctx.roles 0)) =
    (Finite.fold (fun result index => (proverCoefficientProcess (F := F) (G := G) ctx index line)) (List.range' 0 count) initial).bind (fun result => .done (proverCoefficientState (F := F) (G := G))) := by
  exact LoopPresentation.presentUniform coefficientSpec ctx (ctx.roles 0) (by simp) _ _
    (fun result => (proverCoefficientState (F := F) (G := G))) (fun result => proverCoefficientState_masked ctx _ rfl )
    (fun result index => (proverCoefficientProcess (F := F) (G := G) ctx index line)) (fun result index => proverCoefficient_process ctx _ rfl distinct index line) count bounded state initial start

def proverSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverPattern : InputPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .absent (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent .nil))))))))
noncomputable def proverForm : Form proverSignature.laws proverSignature.callees proverPattern.scope [.boolean] :=
  (.strict (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[1], [0]], 4⟩ : RepeatSpec) "s37" outputBody (.input (.there (.there (.there (.there (.there (.there .here))))))) (.cons .absent (.cons (.present (.result .here .here)) .nil)) (.cons .absent .nil) (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [0, 1], [[0], [1], [1]], 4⟩ : RepeatSpec) "s57" layerBody (.input (.there (.there (.there (.there (.there .here)))))) (.cons (.read .here (.there .here)) (.cons .absent (.cons .absent .nil))) (.cons (.input (.there (.there .here))) (.cons (.input (.there (.there (.there .here)))) (.cons (.input (.there (.there (.there (.there .here))))) (.cons (.input (.there (.there (.there (.there (.there .here)))))) (.cons (.input (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .absent .nil))))))) (.done (.cons .absent .nil)))))

noncomputable def proverProcess (ctx : ProtocolContext) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil).bind fun (b6 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
  (denoteRepeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[1], [0]], 4⟩ : RepeatSpec) ctx (ctx.roles 0) (width) (.cons (none) (.cons ((some ((b6).get .here))) .nil)) (.cons (none) .nil) (outputFn ctx (ctx.roles 0))).bind fun (b7 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")])) =>
  (denoteRepeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [0, 1], [[0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 0) (layers) (.cons ((b7).get (.there .here)) (.cons (none) (.cons (none) .nil))) (.cons (inputs) (.cons (add) (.cons (mul) (.cons (layers) (.cons (selector) (.cons (width) (.cons (none) .nil))))))) (layerFn ctx (ctx.roles 0))).bind fun (_b8 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
  .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem prover_normalized : normalize proverSignature gkrBody 0 2 proverPattern = .ok proverForm := by kernel_rfl
theorem prover_calls : proverForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem prover_presentation (ctx : ProtocolContext) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) :
  ((proverForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (boundCallees2) (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil))))))) = (proverProcess (F := F) (G := G) ctx inputs add mul layers selector width) := by kernel_rfl

theorem prover_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) :
  gkrFn (F := F) (G := G) ctx self ((proverPattern.environment (ringModel F G) (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil)))))))) = (proverProcess (F := F) (G := G) ctx inputs add mul layers selector width) := by
  subst self
  exact (sound_uniform proverSignature gkrBody 0 2 proverPattern proverForm
    prover_normalized prover_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees2)
    (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil)))))) _ rfl (emptyLaws _ _) (boundCallees2_hold _)).trans
    (prover_presentation ctx inputs add mul layers selector width)

theorem prover_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) :
  gkrBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverPattern.environment (ringModel F G) (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil)))))))).get =
  proverForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width .nil)))))) :=
  normalize_occurrence_sound proverSignature gkrBody 0 2
    proverPattern proverForm prover_normalized prover_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def proverView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  ((proverProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there (.there .here))) (input.get (.there (.there (.there .here)))) (input.get (.there (.there (.there (.there .here))))) (input.get (.there (.there (.there (.there (.there .here)))))) (input.get (.there (.there (.there (.there (.there (.there .here))))))))).bind fun out => .done (.cons none .nil)

theorem prover_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) gkrDefinition.signature ctx (ctx.roles 0) input = proverView ctx input := by
  have environment : proverPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil)))))) =
      maskValues (ctx.roles 0) (ctx.mapScopes gkrDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct gkrDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload gkrDefinition (List.get_mem _ _) proverSignature 0 2 proverPattern proverForm
    prover_normalized prover_calls (emptyResults _) (boundCallees2) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil))))))
    environment (emptyLaws _ _) (boundCallees2_hold _)
  rw [prover_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct gkrDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

theorem prover_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 0 input = proverView {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans
    (prover_invocation {} (RosterDistinct.root _ _) input)

end Root

noncomputable def boundCallees3 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees2) ⟨3, by decide +kernel⟩ (fun ctx binders => Root.proverView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees3_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees3 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees2) ⟨3, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold input) (boundCallees2_hold input)
  intro ctx binders distinct
  exact Root.prover_invocation ctx distinct _

namespace Root

def verifierOutputFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] :=
  (.cons .optional (.cons .absent .nil))

def verifierOutputState (point : (Option ((List F)))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] :=
  (.cons point (.cons none .nil))

theorem verifierOutputState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1) (point : (Option ((List F)))) :
  maskValues self (ctx.mapScopes [[1], [0]]) (verifierOutputState (F := F) (G := G) point) = (verifierOutputState (F := F) (G := G) point) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 1 verifierOutputFinish _ rfl (.cons point .nil)

def verifierOutputSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierOutputPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .optional (.cons .absent (.cons .optional .nil))))
noncomputable def verifierOutputForm : Form verifierOutputSignature.laws verifierOutputSignature.callees verifierOutputPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")] :=
  (.split (.input (.there (.there .here))) (.halt .incomplete) (.query "label_6f7574707574" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_6f75747075745f64656c6976657279_0" 0 (.var .here) (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done (.cons (.present (.result .here .here)) (.cons .absent .nil))))))))

noncomputable def verifierOutputProcess (ctx : ProtocolContext) (service : (Option (Nat))) (point : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true)])) :=
  match service with
  | none =>
    .halt .incomplete
  | some b3 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6f7574707574") "bls12-381.fr" (.cons (b3) .nil)) fun (b4 : F) =>
    .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_6f75747075745f64656c6976657279_0") ((ctx).roles 0) (b4)) fun _ =>
    match point with
    | none =>
      .halt .incomplete
    | some b5 =>
      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b5) (.cons (b4) .nil))).bind fun (b6 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
      .done ((some ((b6).get .here)))

theorem verifierOutput_normalized : normalize verifierOutputSignature outputBody 1 2 verifierOutputPattern = .ok verifierOutputForm := by kernel_rfl
theorem verifierOutput_calls : verifierOutputForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem verifierOutput_finishes : verifierOutputForm.finishes verifierOutputFinish = true := by kernel_rfl

theorem verifierOutput_presentation (ctx : ProtocolContext) (index : Nat) (point : (Option ((List F)))) (service : (Option (Nat))) :
  ((verifierOutputForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees3) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional (.cons .absent .nil))) (.cons index (.cons point (.cons service .nil)))) = (verifierOutputProcess (F := F) (G := G) ctx service point) := by kernel_rfl

theorem verifierOutput_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (point : (Option ((List F)))) (service : (Option (Nat))) :
  outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierOutputPattern).environment (ringModel F G) (.cons index (.cons point (.cons service .nil)))).get =
  verifierOutputForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons point (.cons service .nil))) :=
  normalize_occurrence_sound verifierOutputSignature outputBody 1 2
    verifierOutputPattern verifierOutputForm verifierOutput_normalized verifierOutput_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem verifierOutput_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (index : Nat) (point : (Option ((List F)))) (service : (Option (Nat))) :
  outputFn (F := F) (G := G) ctx self (.cons (some index) ((verifierOutputState (F := F) (G := G) point).append (.cons service .nil))) =
    (verifierOutputProcess (F := F) (G := G) ctx service point).bind (fun result => .done (verifierOutputState (F := F) (G := G) result)) := by
  subst self
  exact (callback_sound_uniform verifierOutputSignature outputBody 1 2 verifierOutputPattern verifierOutputFinish verifierOutputForm
    verifierOutput_normalized verifierOutput_calls verifierOutput_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees3)
    (.cons index (.cons point (.cons service .nil))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees3_hold _)).trans
    (congrArg₂ PIR.Process.bind (verifierOutput_presentation ctx index point service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem verifierOutput_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ outputSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried verifierOutputFinish))
  (start : maskValues (ctx.roles 1) (ctx.mapScopes outputSpec.stateScopes) state = (verifierOutputState (F := F) (G := G) initial)) :
  denoteRepeat outputSpec ctx (ctx.roles 1) (some count) state (.cons service .nil) (outputFn ctx (ctx.roles 1)) =
    (Finite.fold (fun result index => (verifierOutputProcess (F := F) (G := G) ctx service result)) (List.range' 0 count) initial).bind (fun result => .done (verifierOutputState (F := F) (G := G) result)) := by
  exact LoopPresentation.presentUniform outputSpec ctx (ctx.roles 1) (by simp) _ _
    (fun result => (verifierOutputState (F := F) (G := G) result)) (fun result => verifierOutputState_masked ctx _ rfl result)
    (fun result index => (verifierOutputProcess (F := F) (G := G) ctx service result)) (fun result index => verifierOutput_process ctx _ rfl distinct index result service) count bounded state initial start

def verifierLayerFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons .absent (.cons .optional (.cons .optional .nil)))

def verifierLayerState (point : (Option ((List F)))) (claim : (Option (F))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons none (.cons point (.cons claim .nil)))

theorem verifierLayerState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1) (point : (Option ((List F)))) (claim : (Option (F))) :
  maskValues self (ctx.mapScopes [[0], [1], [1]]) (verifierLayerState (F := F) (G := G) point claim) = (verifierLayerState (F := F) (G := G) point claim) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 1 verifierLayerFinish _ rfl (.cons point (.cons claim .nil))

def verifierLayerSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierLayerPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .absent (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))))))))))
noncomputable def verifierLayerForm : Form verifierLayerSignature.laws verifierLayerSignature.callees verifierLayerPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input (.there .here)) (.halt .incomplete) (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.strict (⟨"zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.strict (⟨"zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.result .here (.there .here)) .nil) (.apply ⟨1, by decide⟩ (⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩ : ProtocolSignature) [0, 1] "label_6c656674" (by change (Zkc.Source.Values (Zkc.Source.Structured.NormalForm.Argument [] [(.results [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.results [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.value (.field "bls12-381.fr")), (.value (.vector "bls12-381.fr")), (.value .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil))))))))) (.apply ⟨1, by decide⟩ (⟨"zkl_5a80545f362c672054af2a3a1c33ef1f972bb503c8360b0dc7d4a80c436a43ba", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [0], [1], [1]]⟩ : ProtocolSignature) [0, 1] "label_7269676874" (by change (Zkc.Source.Values (Zkc.Source.Structured.NormalForm.Argument [] [(.tuple [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.results [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.results [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.value (.field "bls12-381.fr")), (.value (.vector "bls12-381.fr")), (.value .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.read .here (.there (.there (.there (.there (.there .here)))))) (.cons (.read .here (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil))))))))) (.split (.read .here (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.split (.read (.there .here) (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.strict (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.strict (⟨"zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", .local, [(.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) (.cons (.result .here .here) .nil) (.receive (.field "bls12-381.fr") "label_6c696e655f636f6e7374616e74_0" 0 (.strict (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.result .here .here) (.cons (.var (.there .here)) .nil)) (.repeat (⟨[(.vector "bls12-381.fr")], [(.vector "bls12-381.fr")], [0, 1], [[1]], 4⟩ : RepeatSpec) "s91" coefficientBody (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.present (.result .here .here)) .nil) (.cons .absent .nil) (.split (.read .here .here) (.halt .incomplete) (.strict (⟨"zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) .nil) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.halt .incomplete) (.strict (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.var .here) .nil))) (.strict (⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.result .here .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.there .here)) .nil)))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))) (.halt .incomplete) (.strict (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))) (.cons (.var (.there (.there (.there .here)))) .nil))) (.strict (⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.result .here .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.there .here)) .nil)))) (.guard (.field "bls12-381.fr") (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.there .here)) (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.result (.there (.there (.there .here))) .here) (.cons (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) (.cons (.result (.there (.there (.there (.there (.there (.there (.there .here))))))) .here) .nil)) .here) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.result .here .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))) .nil)) .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there .here))))))) .here) .nil)) .here) .nil)) .here) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))))))))) (.halt .incomplete) (.query "label_6c696e655f6368616c6c656e6765" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_6c696e655f64656c6976657279_0" 0 (.var .here) (.strict (⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .here) (.cons (.result (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.there .here)) (.cons (.var .here) .nil))) (.strict (⟨"zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.cons (.var (.there .here)) .nil)) (.strict (⟨"zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.result (.there .here) .here) (.cons (.result .here .here) .nil)) (.done (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil))))))))))))))))))))))))))))))))))

noncomputable def verifierLayerProcess (ctx : ProtocolContext) (index : Nat) (add : (Option ((List F)))) (mul : (Option ((List F)))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) (point : (Option ((List F)))) (claim : (Option (F))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true), ((.field "bls12-381.fr"), true)])) :=
  match point with
  | none =>
    .halt .incomplete
  | some b10 =>
    match claim with
    | none =>
      .halt .incomplete
    | some b11 =>
      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e0f7a4e58ae24eb13e9b2033c42c179b2766ff6cdb4ae1470bf7ef9b1721d646", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b10) (.cons (b11) .nil))).bind fun (b12 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e1405e1bb4604e60f337203132c746492bf7c31b55302426ae19c2c021c2da1a", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons ((b12).get (.there .here)) .nil)).bind fun (b13 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      ((fun ctx binders => Rounds.verifierRoundsView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))) ((ctx).enter "label_6c656674" [0, 1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons (none) (.cons (none) (.cons (none) (.cons (none) (.cons ((some ((b13).get .here))) (.cons ((some ((b13).get (.there .here)))) (.cons (width) (.cons (service) .nil)))))))))).bind fun (b14 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      ((fun ctx binders => Rounds.verifierRoundsView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))) ((ctx).enter "label_7269676874" [0, 1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons (none) (.cons (none) (.cons (none) (.cons (none) (.cons ((b14).get (.there (.there (.there (.there (.there .here)))))) (.cons ((b14).get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (width) (.cons (service) .nil)))))))))).bind fun (b15 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      match (b15).get (.there (.there (.there (.there (.there .here))))) with
      | none =>
        .halt .incomplete
      | some b16 =>
        match (b15).get (.there (.there (.there (.there (.there (.there .here)))))) with
        | none =>
          .halt .incomplete
        | some b17 =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_bd4f0d76e787de675c5732a4a96fc396d45486f32b3dcda5182ccc324969c825", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b16) (.cons (b17) .nil))).bind fun (b18 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_cfcf40daaab145a916368cf7a01eccd9ba0e536fbbc30a06c4a25e7ec96ecbe7", .local, [(.vector "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]⟩ : Helper) (.cons ((b18).get .here) .nil)).bind fun (b19 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")])) =>
          .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f636f6e7374616e74_0") ((ctx).roles 0)) fun (b20 : F) =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil).bind fun (b21 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons ((b21).get .here) (.cons (b20) .nil))).bind fun (b22 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
          (denoteRepeat (⟨[(.vector "bls12-381.fr")], [(.vector "bls12-381.fr")], [0, 1], [[1]], 4⟩ : RepeatSpec) ctx (ctx.roles 1) (width) (.cons ((some ((b22).get .here))) .nil) (.cons (none) .nil) (coefficientFn ctx (ctx.roles 1))).bind fun (b23 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr")])) =>
          match (b23).get .here with
          | none =>
            .halt .incomplete
          | some b24 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_6ec6b9d6cb41b6bf4ef8e898ba1b283d099252f7de2db0b173f26714e3a46216", .local, [(.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (b24) .nil)).bind fun (b25 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
            match add with
            | none =>
              .halt .incomplete
            | some b26 =>
              match selector with
              | none =>
                .halt .incomplete
              | some b27 =>
                (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b26) (.cons (index) (.cons (b27) .nil)))).bind fun (b28 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons ((b28).get .here) (.cons ((b12).get .here) (.cons ((b19).get .here) (.cons ((b19).get (.there .here)) .nil))))).bind fun (b29 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
                match mul with
                | none =>
                  .halt .incomplete
                | some b30 =>
                  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c019abe42d43d9f2b24ebe6716aad9e3a3c425a78c3b3ff212966c3ef4db181e", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b30) (.cons (index) (.cons (b27) .nil)))).bind fun (b31 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_161d519d8d5fe2674feddb6e6d14269c9cca82ff216b6b3205ade46cc8b8d35f", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons ((b31).get .here) (.cons ((b12).get .here) (.cons ((b19).get .here) (.cons ((b19).get (.there .here)) .nil))))).bind fun (b32 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
                  @ite _ (((b18).get (.there .here)) = ((((((b29).get .here) * (((b20) + ((b25).get .here))))) + ((((((b32).get .here) * (b20))) * ((b25).get .here)))))) (Equality.decide (ringModel F G) (.field "bls12-381.fr") ((b18).get (.there .here)) ((((((b29).get .here) * (((b20) + ((b25).get .here))))) + ((((((b32).get .here) * (b20))) * ((b25).get .here))))))
                    (
                      match service with
                      | none =>
                        .halt .incomplete
                      | some b33 =>
                        .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f6368616c6c656e6765") "bls12-381.fr" (.cons (b33) .nil)) fun (b34 : F) =>
                        .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f64656c6976657279_0") ((ctx).roles 0) (b34)) fun _ =>
                        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_1f2e31017a1a0403a56241b1d83eac39d1ecc40b298cd066516f78ae9c5b3434", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons ((b19).get .here) (.cons ((b19).get (.there .here)) (.cons (b34) .nil)))).bind fun (b35 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_21465134b1aa848c616c790eff1907b1a442ba76730b77da2be48acd923d6ff7", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (b24) (.cons (b34) .nil))).bind fun (b36 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
                        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons ((b35).get .here) (.cons ((b36).get .here) .nil))).bind fun (b37 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
                        .done (((some ((b37).get .here))), ((some ((b37).get (.there .here))))))
                    (.halt .reject)

theorem verifierLayer_normalized : normalize verifierLayerSignature layerBody 1 2 verifierLayerPattern = .ok verifierLayerForm := by kernel_rfl
theorem verifierLayer_calls : verifierLayerForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem verifierLayer_finishes : verifierLayerForm.finishes verifierLayerFinish = true := by kernel_rfl

theorem verifierLayer_presentation (ctx : ProtocolContext) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  ((verifierLayerForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees3) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .absent (.cons .optional (.cons .optional .nil)))) (.cons index (.cons point (.cons claim (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))))) = (verifierLayerProcess (F := F) (G := G) ctx index add mul selector width service point claim) := by kernel_rfl

theorem verifierLayer_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierLayerPattern).environment (ringModel F G) (.cons index (.cons point (.cons claim (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))))).get =
  verifierLayerForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons point (.cons claim (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))))) :=
  normalize_occurrence_sound verifierLayerSignature layerBody 1 2
    verifierLayerPattern verifierLayerForm verifierLayer_normalized verifierLayer_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem verifierLayer_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  layerFn (F := F) (G := G) ctx self (.cons (some index) ((verifierLayerState (F := F) (G := G) point claim).append (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))) =
    (verifierLayerProcess (F := F) (G := G) ctx index add mul selector width service point claim).bind (fun result => .done (verifierLayerState (F := F) (G := G) result.1 result.2)) := by
  subst self
  exact (callback_sound_uniform verifierLayerSignature layerBody 1 2 verifierLayerPattern verifierLayerFinish verifierLayerForm
    verifierLayer_normalized verifierLayer_calls verifierLayer_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees3)
    (.cons index (.cons point (.cons claim (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees3_hold _)).trans
    (congrArg₂ PIR.Process.bind (verifierLayer_presentation ctx index point claim inputs add mul layers selector width service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem verifierLayer_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (inputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ layerSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried verifierLayerFinish))
  (start : maskValues (ctx.roles 1) (ctx.mapScopes layerSpec.stateScopes) state = (verifierLayerState (F := F) (G := G) initial.1 initial.2)) :
  denoteRepeat layerSpec ctx (ctx.roles 1) (some count) state (.cons inputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))) (layerFn ctx (ctx.roles 1)) =
    (Finite.fold (fun result index => (verifierLayerProcess (F := F) (G := G) ctx index add mul selector width service result.1 result.2)) (List.range' 0 count) initial).bind (fun result => .done (verifierLayerState (F := F) (G := G) result.1 result.2)) := by
  exact LoopPresentation.presentUniform layerSpec ctx (ctx.roles 1) (by simp) _ _
    (fun result => (verifierLayerState (F := F) (G := G) result.1 result.2)) (fun result => verifierLayerState_masked ctx _ rfl result.1 result.2)
    (fun result index => (verifierLayerProcess (F := F) (G := G) ctx index add mul selector width service result.1 result.2)) (fun result index => verifierLayer_process ctx _ rfl distinct index result.1 result.2 inputs add mul layers selector width service) count bounded state initial start

def verifierCoefficientFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr")] :=
  (.cons .optional .nil)

def verifierCoefficientState (coefficients : (Option ((List F)))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr")] :=
  (.cons coefficients .nil)

theorem verifierCoefficientState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1) (coefficients : (Option ((List F)))) :
  maskValues self (ctx.mapScopes [[1]]) (verifierCoefficientState (F := F) (G := G) coefficients) = (verifierCoefficientState (F := F) (G := G) coefficients) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 1 verifierCoefficientFinish _ rfl (.cons coefficients .nil)

def verifierCoefficientSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierCoefficientPattern : InputPattern [.index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr")] := (.cons .present (.cons .optional (.cons .optional .nil)))
noncomputable def verifierCoefficientForm : Form verifierCoefficientSignature.laws verifierCoefficientSignature.callees verifierCoefficientPattern.scope [(.vector "bls12-381.fr")] :=
  (.receive (.field "bls12-381.fr") "label_6c696e655f636f656666696369656e74_0" 0 (.split (.input (.there (.there .here))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done (.cons (.present (.result .here .here)) .nil)))))

noncomputable def verifierCoefficientProcess (ctx : ProtocolContext) (coefficients : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true)])) :=
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_6c696e655f636f656666696369656e74_0") ((ctx).roles 0)) fun (b3 : F) =>
  match coefficients with
  | none =>
    .halt .incomplete
  | some b4 =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b4) (.cons (b3) .nil))).bind fun (b5 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
    .done ((some ((b5).get .here)))

theorem verifierCoefficient_normalized : normalize verifierCoefficientSignature coefficientBody 1 2 verifierCoefficientPattern = .ok verifierCoefficientForm := by kernel_rfl
theorem verifierCoefficient_calls : verifierCoefficientForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem verifierCoefficient_finishes : verifierCoefficientForm.finishes verifierCoefficientFinish = true := by kernel_rfl

theorem verifierCoefficient_presentation (ctx : ProtocolContext) (index : Nat) (coefficients : (Option ((List F)))) (line : (Option ((List F)))) :
  ((verifierCoefficientForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees3) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional .nil)) (.cons index (.cons coefficients (.cons line .nil)))) = (verifierCoefficientProcess (F := F) (G := G) ctx coefficients) := by kernel_rfl

theorem verifierCoefficient_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (coefficients : (Option ((List F)))) (line : (Option ((List F)))) :
  coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierCoefficientPattern).environment (ringModel F G) (.cons index (.cons coefficients (.cons line .nil)))).get =
  verifierCoefficientForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons coefficients (.cons line .nil))) :=
  normalize_occurrence_sound verifierCoefficientSignature coefficientBody 1 2
    verifierCoefficientPattern verifierCoefficientForm verifierCoefficient_normalized verifierCoefficient_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem verifierCoefficient_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (index : Nat) (coefficients : (Option ((List F)))) (line : (Option ((List F)))) :
  coefficientFn (F := F) (G := G) ctx self (.cons (some index) ((verifierCoefficientState (F := F) (G := G) coefficients).append (.cons line .nil))) =
    (verifierCoefficientProcess (F := F) (G := G) ctx coefficients).bind (fun result => .done (verifierCoefficientState (F := F) (G := G) result)) := by
  subst self
  exact (callback_sound_uniform verifierCoefficientSignature coefficientBody 1 2 verifierCoefficientPattern verifierCoefficientFinish verifierCoefficientForm
    verifierCoefficient_normalized verifierCoefficient_calls verifierCoefficient_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees3)
    (.cons index (.cons coefficients (.cons line .nil))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees3_hold _)).trans
    (congrArg₂ PIR.Process.bind (verifierCoefficient_presentation ctx index coefficients line)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem verifierCoefficient_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (line : (Option ((List F))))
  (count : Nat) (bounded : count ≤ coefficientSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried verifierCoefficientFinish))
  (start : maskValues (ctx.roles 1) (ctx.mapScopes coefficientSpec.stateScopes) state = (verifierCoefficientState (F := F) (G := G) initial)) :
  denoteRepeat coefficientSpec ctx (ctx.roles 1) (some count) state (.cons line .nil) (coefficientFn ctx (ctx.roles 1)) =
    (Finite.fold (fun result index => (verifierCoefficientProcess (F := F) (G := G) ctx result)) (List.range' 0 count) initial).bind (fun result => .done (verifierCoefficientState (F := F) (G := G) result)) := by
  exact LoopPresentation.presentUniform coefficientSpec ctx (ctx.roles 1) (by simp) _ _
    (fun result => (verifierCoefficientState (F := F) (G := G) result)) (fun result => verifierCoefficientState_masked ctx _ rfl result)
    (fun result index => (verifierCoefficientProcess (F := F) (G := G) ctx result)) (fun result index => verifierCoefficient_process ctx _ rfl distinct index result line) count bounded state initial start

def verifierSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierPattern : InputPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil))))))))
noncomputable def verifierForm : Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [.boolean] :=
  (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.strict (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (.index 4) (.cons (.var .here) .nil)) (.guard .boolean (.calc .booleanEqual rfl (.cons (.result .here .here) (.cons (.bool false) .nil)) .here) (.bool true) (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.strict (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (.index 4) (.cons (.var .here) .nil)) (.guard .boolean (.calc .booleanEqual rfl (.cons (.result .here .here) (.cons (.bool false) .nil)) .here) (.bool true) (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.strict (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.index 1) .nil))) (.guard .boolean (.result .here .here) (.bool true) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.halt .incomplete) (.strict (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) (.cons (.index 1) .nil))) (.guard .boolean (.result .here .here) (.bool true) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) (.halt .incomplete) (.strict (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil)) (.strict (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (.result .here .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil)) (.strict (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (.result .here .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil)) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.halt .incomplete) (.strict (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (.var .here) (.cons (.result (.there .here) .here) (.cons (.index 1) .nil))) (.guard .boolean (.result .here .here) (.bool true) (.strict (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))) .nil)) (.strict (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (.result .here .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) .nil)) (.strict (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (.result .here .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))) .nil)) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))) (.halt .incomplete) (.strict (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (.var .here) (.cons (.result (.there .here) .here) (.cons (.index 1) .nil))) (.guard .boolean (.result .here .here) (.bool true) (.strict (⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) .nil) (.strict (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (.result .here .here) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) .nil)) (.guard .boolean (.calc .booleanEqual rfl (.cons (.result .here .here) (.cons (.bool false) .nil)) .here) (.bool true) (.strict (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[1], [0]], 4⟩ : RepeatSpec) "s37" outputBody (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.present (.result .here .here)) (.cons .absent .nil)) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))) .nil) (.split (.read .here .here) (.halt .incomplete) (.strict (⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))) (.cons (.var .here) .nil)) (.strict (⟨"zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.result .here .here) .nil)) (.repeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [0, 1], [[0], [1], [1]], 4⟩ : RepeatSpec) "s57" layerBody (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.cons (.read (.there (.there (.there .here))) (.there .here)) (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil))) (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))) (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))) (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))) (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))) (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))))))))))))))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))))))))))))) .nil))))))) (.apply ⟨2, by decide⟩ (⟨"zkl_9719be65739d901a935dbaa0f3f8323a785562f7eee1e60cc8c8c9676f8fdb55", ["role00000000"], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [.boolean], [[0], [0], [0]], [[0]]⟩ : ProtocolSignature) [1] "label_696e707574" (by change (Zkc.Source.Values (Zkc.Source.Structured.NormalForm.Argument [] [(.tuple [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.results [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.results [(.field "bls12-381.fr")]), (.value (.vector "bls12-381.fr")), (.tuple [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")]), (.results [(.vector "bls12-381.fr")]), (.results [.boolean]), (.results [.index]), (.results [.boolean]), (.value (.vector "bls12-381.fr")), (.results [.index]), (.results [.index]), (.results [.index]), (.results [.boolean]), (.value (.vector "bls12-381.fr")), (.results [.index]), (.results [.index]), (.results [.index]), (.value .index), (.results [.boolean]), (.value (.vector "bls12-381.fr")), (.results [.boolean]), (.value (.vector "bls12-381.fr")), (.results [.boolean]), (.value .index), (.results [.boolean]), (.value .index), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr"))]); exact (.cons (.present (.var (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))))))))))))))) (.cons (.read .here (.there .here)) (.cons (.read .here (.there (.there .here))) .nil)))) (.done (.cons (.read .here .here) .nil)))))))))))))))))))))))))))))))))))))

noncomputable def verifierProcess (ctx : ProtocolContext) (inputs : (Option ((List F)))) (outputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  match width with
  | none =>
    .halt .incomplete
  | some b8 =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (4) (.cons (b8) .nil))).bind fun (b9 : (Values (assignment F G) [.boolean])) =>
    @ite _ (((((b9).get .here) == (false))) = (true)) (Equality.decide (ringModel F G) .boolean ((((b9).get .here) == (false))) (true))
      (
        match layers with
        | none =>
          .halt .incomplete
        | some b10 =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (4) (.cons (b10) .nil))).bind fun (b11 : (Values (assignment F G) [.boolean])) =>
          @ite _ (((((b11).get .here) == (false))) = (true)) (Equality.decide (ringModel F G) .boolean ((((b11).get .here) == (false))) (true))
            (
              match inputs with
              | none =>
                .halt .incomplete
              | some b12 =>
                (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (b12) (.cons (b8) (.cons (1) .nil)))).bind fun (b13 : (Values (assignment F G) [.boolean])) =>
                @ite _ (((b13).get .here) = (true)) (Equality.decide (ringModel F G) .boolean ((b13).get .here) (true))
                  (
                    match outputs with
                    | none =>
                      .halt .incomplete
                    | some b14 =>
                      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (b14) (.cons (b8) (.cons (1) .nil)))).bind fun (b15 : (Values (assignment F G) [.boolean])) =>
                      @ite _ (((b15).get .here) = (true)) (Equality.decide (ringModel F G) .boolean ((b15).get .here) (true))
                        (
                          match selector with
                          | none =>
                            .halt .incomplete
                          | some b16 =>
                            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (b16) (.cons (b8) .nil))).bind fun (b17 : (Values (assignment F G) [.index])) =>
                            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons ((b17).get .here) (.cons (b8) .nil))).bind fun (b18 : (Values (assignment F G) [.index])) =>
                            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons ((b18).get .here) (.cons (b8) .nil))).bind fun (b19 : (Values (assignment F G) [.index])) =>
                            match add with
                            | none =>
                              .halt .incomplete
                            | some b20 =>
                              (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (b20) (.cons ((b19).get .here) (.cons (1) .nil)))).bind fun (b21 : (Values (assignment F G) [.boolean])) =>
                              @ite _ (((b21).get .here) = (true)) (Equality.decide (ringModel F G) .boolean ((b21).get .here) (true))
                                (
                                  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons (b16) (.cons (b8) .nil))).bind fun (b22 : (Values (assignment F G) [.index])) =>
                                  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons ((b22).get .here) (.cons (b8) .nil))).bind fun (b23 : (Values (assignment F G) [.index])) =>
                                  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h7072656c7564659h696e6465785f616464", .local, [.index, .index], [.index]⟩ : Helper) (.cons ((b23).get .here) (.cons (b8) .nil))).bind fun (b24 : (Values (assignment F G) [.index])) =>
                                  match mul with
                                  | none =>
                                    .halt .incomplete
                                  | some b25 =>
                                    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_84866a528a9e472fae644df45c457b704b5e44f2a5edb0a5aa068a3ce5519655", .local, [(.vector "bls12-381.fr"), .index, .index], [.boolean]⟩ : Helper) (.cons (b25) (.cons ((b24).get .here) (.cons (1) .nil)))).bind fun (b26 : (Values (assignment F G) [.boolean])) =>
                                    @ite _ (((b26).get .here) = (true)) (Equality.decide (ringModel F G) .boolean ((b26).get .here) (true))
                                      (
                                        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h676b7212h706f7765725f6f665f74776f", .local, [.index], [.index]⟩ : Helper) (.cons (b16) .nil)).bind fun (b27 : (Values (assignment F G) [.index])) =>
                                        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons ((b27).get .here) (.cons (b10) .nil))).bind fun (b28 : (Values (assignment F G) [.boolean])) =>
                                        @ite _ (((((b28).get .here) == (false))) = (true)) (Equality.decide (ringModel F G) .boolean ((((b28).get .here) == (false))) (true))
                                          (
                                            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil).bind fun (b29 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                                            (denoteRepeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[1], [0]], 4⟩ : RepeatSpec) ctx (ctx.roles 1) ((some (b8))) (.cons ((some ((b29).get .here))) (.cons (none) .nil)) (.cons (service) .nil) (outputFn ctx (ctx.roles 1))).bind fun (b30 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")])) =>
                                            match (b30).get .here with
                                            | none =>
                                              .halt .incomplete
                                            | some b31 =>
                                              (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_28c1498dbf9d83fc38ed7b21a89d56146297abcbf1ac78968a8b454c9eef5496", .local, [(.vector "bls12-381.fr"), (.vector "bls12-381.fr")], [(.field "bls12-381.fr")]⟩ : Helper) (.cons (b14) (.cons (b31) .nil))).bind fun (b32 : (Values (assignment F G) [(.field "bls12-381.fr")])) =>
                                              (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_7b9dfa97fa3e158d428459ec12d8a2d5aa171a060ab79f314eeccc53ee772b17", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b31) (.cons ((b32).get .here) .nil))).bind fun (b33 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
                                              (denoteRepeat (⟨[(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")], [0, 1], [[0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 1) ((some (b10))) (.cons ((b30).get (.there .here)) (.cons ((some ((b33).get .here))) (.cons ((some ((b33).get (.there .here)))) .nil))) (.cons ((some (b12))) (.cons ((some (b20))) (.cons ((some (b25))) (.cons ((some (b10))) (.cons ((some (b16))) (.cons ((some (b8))) (.cons (service) .nil))))))) (layerFn ctx (ctx.roles 1))).bind fun (b34 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
                                              ((fun ctx binders => Input.verifierView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean]))) ((ctx).enter "label_696e707574" [1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr"))]); exact (.cons ((some (b12))) (.cons ((b34).get (.there .here)) (.cons ((b34).get (.there (.there .here))) .nil))))).bind fun (b35 : (Values (Component (assignment F G)) [.boolean])) =>
                                              .done ((.cons ((b35).get .here) .nil) : (Values (Component (assignment F G)) [.boolean])))
                                          (.halt .reject))
                                      (.halt .reject))
                                (.halt .reject))
                        (.halt .reject))
                  (.halt .reject))
            (.halt .reject))
      (.halt .reject)

theorem verifier_normalized : normalize verifierSignature gkrBody 1 2 verifierPattern = .ok verifierForm := by kernel_rfl
theorem verifier_calls : verifierForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem verifier_presentation (ctx : ProtocolContext) (inputs : (Option ((List F)))) (outputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  ((verifierForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees3) (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil))))))))) = (verifierProcess (F := F) (G := G) ctx inputs outputs add mul layers selector width service) := by kernel_rfl

theorem verifier_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (inputs : (Option ((List F)))) (outputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  gkrFn (F := F) (G := G) ctx self ((verifierPattern.environment (ringModel F G) (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))))) = (verifierProcess (F := F) (G := G) ctx inputs outputs add mul layers selector width service) := by
  subst self
  exact (sound_uniform verifierSignature gkrBody 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees3)
    (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))) _ rfl (emptyLaws _ _) (boundCallees3_hold _)).trans
    (verifier_presentation ctx inputs outputs add mul layers selector width service)

theorem verifier_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (inputs : (Option ((List F)))) (outputs : (Option ((List F)))) (add : (Option ((List F)))) (mul : (Option ((List F)))) (layers : (Option (Nat))) (selector : (Option (Nat))) (width : (Option (Nat))) (service : (Option (Nat))) :
  gkrBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierPattern.environment (ringModel F G) (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))))).get =
  verifierForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons inputs (.cons outputs (.cons add (.cons mul (.cons layers (.cons selector (.cons width (.cons service .nil)))))))) :=
  normalize_occurrence_sound verifierSignature gkrBody 1 2
    verifierPattern verifierForm verifier_normalized verifier_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def verifierView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  ((verifierProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)) (input.get (.there (.there .here))) (input.get (.there (.there (.there .here)))) (input.get (.there (.there (.there (.there .here))))) (input.get (.there (.there (.there (.there (.there .here)))))) (input.get (.there (.there (.there (.there (.there (.there .here))))))) (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))))).bind fun out => .done (.cons (out.get .here) .nil)

theorem verifier_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) gkrDefinition.signature ctx (ctx.roles 1) input = verifierView ctx input := by
  have environment : verifierPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil)))))))) =
      maskValues (ctx.roles 1) (ctx.mapScopes gkrDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct gkrDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload gkrDefinition (List.get_mem _ _) verifierSignature 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls (emptyResults _) (boundCallees3) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) (.cons (input.get (.there (.there (.there (.there (.there (.there (.there .here)))))))) .nil))))))))
    environment (emptyLaws _ _) (boundCallees3_hold _)
  rw [verifier_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct gkrDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

theorem verifier_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 1 input = verifierView {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans
    (verifier_invocation {} (RosterDistinct.root _ _) input)

end Root

noncomputable def boundCallees4 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees3) ⟨4, by decide +kernel⟩ (fun ctx binders => Root.verifierView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees4_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees4 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees3) ⟨4, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Bindings.GkrRounds.callees_hold input) (boundCallees3_hold input)
  intro ctx binders distinct
  exact Root.verifier_invocation ctx distinct _

namespace Root

end Root

end
end ZkcExamples.Structured.Generated.Presentations.Gkr
