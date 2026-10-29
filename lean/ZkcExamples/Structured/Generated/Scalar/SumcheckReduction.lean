module

public import ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindingsCallbacks
public import Zkc.Source.Structured.LoopPresentation
public import Zkc.Source.Structured.InputVisibility
public import Zkc.Source.Structured.PlainHelpers
public import Zkc.Source.Structured.OccurrencePresentation
public import Zkc.Source.Structured.ProtocolPresentation

@[expose] public section

/-! Generated scope-derived source presentations. Regenerate with the Lean role-view printer. -/
namespace ZkcExamples.Structured.Generated.Scalar.SumcheckReduction
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

abbrev program : Program := ZkcExamples.Structured.SumcheckReduceViews.program
abbrev payload := program.payload
abbrev calleeKeys := ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.calleeKeys

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

namespace Reduce

abbrev bodyDefinition : CheckedProtocol := payload.protocols.get ⟨0, by decide +kernel⟩
abbrev bodyInputs : List Ty := [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
abbrev bodyOutputs : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev bodyBody := bodyDefinition.body
theorem bodyBody_checked : bodyDefinition.body = bodyBody := rfl
theorem bodyBody_raw : bodyDefinition.raw = bodyBody.erase := by kernel_rfl

abbrev roundState : List Ty := [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev roundCaptures : List Ty := [(.service "random.bls12-381.fr/0")]
abbrev roundMaximum := 4
abbrev roundSpec : RepeatSpec := (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec)
def roundBody := ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindingsCallbacks.protocol0Role0Callback0Body
theorem round_selected : findRepeat "s18" bodyDefinition.body = some ⟨_, _, roundBody⟩ := ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindingsCallbacks.protocol0Role0Callback0_selected

def bodyFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  fun args => bodyBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def roundFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([.index, (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
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

def proverRoundFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent .nil))))))

def proverRoundState (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (proverPoint : (Option ((List F)))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons entries (.cons dimension (.cons width (.cons proverPoint (.cons none (.cons none .nil))))))

theorem proverRoundState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (proverPoint : (Option ((List F)))) :
  maskValues self (ctx.mapScopes [[0], [0], [0], [0], [1], [1]]) (proverRoundState (F := F) (G := G) entries dimension width proverPoint) = (proverRoundState (F := F) (G := G) entries dimension width proverPoint) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 0 proverRoundFinish _ rfl (.cons entries (.cons dimension (.cons width (.cons proverPoint .nil))))

def proverRoundSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverRoundPattern : InputPattern [.index, (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent (.cons .optional .nil))))))))
noncomputable def proverRoundForm : Form proverRoundSignature.laws proverRoundSignature.callees proverRoundPattern.scope [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input (.there .here)) (.halt .incomplete) (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.strict (⟨"zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", .local, [(.vector "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there (.there .here))) (.cons (.var (.there .here)) (.cons (.var .here) .nil))) (.send (.field "bls12-381.fr") "label_726f756e64_0" 1 (.result .here .here) (.send (.field "bls12-381.fr") "label_726f756e64_1" 1 (.result .here (.there .here)) (.receive (.field "bls12-381.fr") "label_64656c6976657279_0" 1 (.strict (⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩ : Helper) (.cons (.var (.there (.there (.there (.there .here))))) (.cons (.var (.there (.there (.there .here)))) (.cons (.var (.there (.there .here))) (.cons (.var .here) .nil)))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil)) (.done (.cons (.present (.result (.there (.there .here)) .here)) (.cons (.present (.result (.there (.there .here)) (.there .here))) (.cons (.present (.result (.there (.there .here)) (.there (.there .here)))) (.cons (.present (.result .here .here)) (.cons .absent (.cons .absent .nil)))))))))))))))))

noncomputable def proverRoundProcess (ctx : ProtocolContext) (index : Nat) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (proverPoint : (Option ((List F)))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true), (.index, true), (.index, true), ((.vector "bls12-381.fr"), true)])) :=
  match entries with
  | none =>
    .halt .incomplete
  | some b6 =>
    match dimension with
    | none =>
      .halt .incomplete
    | some b7 =>
      match width with
      | none =>
        .halt .incomplete
      | some b8 =>
        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_532a609cf36a935835501ca51308940142121e647ca360843a880bf231f04aa6", .local, [(.vector "bls12-381.fr"), .index, .index], [(.field "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b6) (.cons (b7) (.cons (b8) .nil)))).bind fun (b9 : (Values (assignment F G) [(.field "bls12-381.fr"), (.field "bls12-381.fr")])) =>
        .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_0") ((ctx).roles 1) ((b9).get .here)) fun _ =>
        .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_1") ((ctx).roles 1) ((b9).get (.there .here))) fun _ =>
        .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 1)) fun (b10 : F) =>
        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_3ae183e4974ba027dee61c318edb42bcf3a64a69d220d82168474d3a3169ff4d", .local, [(.vector "bls12-381.fr"), .index, .index, (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), .index, .index]⟩ : Helper) (.cons (b6) (.cons (b7) (.cons (b8) (.cons (b10) .nil))))).bind fun (b11 : (Values (assignment F G) [(.vector "bls12-381.fr"), .index, .index])) =>
        match proverPoint with
        | none =>
          .halt .incomplete
        | some b12 =>
          (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b12) (.cons (b10) .nil))).bind fun (b13 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
          .done (((some ((b11).get .here))), (((some ((b11).get (.there .here)))), (((some ((b11).get (.there (.there .here))))), ((some ((b13).get .here))))))

theorem proverRound_normalized : normalize proverRoundSignature roundBody 0 2 proverRoundPattern = .ok proverRoundForm := by kernel_rfl
theorem proverRound_calls : proverRoundForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem proverRound_finishes : proverRoundForm.finishes proverRoundFinish = true := by kernel_rfl

theorem proverRound_presentation (ctx : ProtocolContext) (index : Nat) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (proverPoint : (Option ((List F)))) (service : (Option (Nat))) :
  ((proverRoundForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent .nil))))))) (.cons index (.cons entries (.cons dimension (.cons width (.cons proverPoint (.cons service .nil))))))) = (proverRoundProcess (F := F) (G := G) ctx index entries dimension width proverPoint) := by kernel_rfl

theorem proverRound_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (proverPoint : (Option ((List F)))) (service : (Option (Nat))) :
  roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverRoundPattern).environment (ringModel F G) (.cons index (.cons entries (.cons dimension (.cons width (.cons proverPoint (.cons service .nil))))))).get =
  proverRoundForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons entries (.cons dimension (.cons width (.cons proverPoint (.cons service .nil)))))) :=
  normalize_occurrence_sound proverRoundSignature roundBody 0 2
    proverRoundPattern proverRoundForm proverRound_normalized proverRound_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem proverRound_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (index : Nat) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (proverPoint : (Option ((List F)))) (service : (Option (Nat))) :
  roundFn (F := F) (G := G) ctx self (.cons (some index) ((proverRoundState (F := F) (G := G) entries dimension width proverPoint).append (.cons service .nil))) =
    (proverRoundProcess (F := F) (G := G) ctx index entries dimension width proverPoint).bind (fun result => .done (proverRoundState (F := F) (G := G) result.1 result.2.1 result.2.2.1 result.2.2.2)) := by
  subst self
  exact (callback_sound_uniform proverRoundSignature roundBody 0 2 proverRoundPattern proverRoundFinish proverRoundForm
    proverRound_normalized proverRound_calls proverRound_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons index (.cons entries (.cons dimension (.cons width (.cons proverPoint (.cons service .nil)))))) _ (by kernel_rfl) (emptyLaws _ _) (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold _)).trans
    (congrArg₂ PIR.Process.bind (proverRound_presentation ctx index entries dimension width proverPoint service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem proverRound_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ roundSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried proverRoundFinish))
  (start : maskValues (ctx.roles 0) (ctx.mapScopes roundSpec.stateScopes) state = (proverRoundState (F := F) (G := G) initial.1 initial.2.1 initial.2.2.1 initial.2.2.2)) :
  denoteRepeat roundSpec ctx (ctx.roles 0) (some count) state (.cons service .nil) (roundFn ctx (ctx.roles 0)) =
    (Finite.fold (fun result index => (proverRoundProcess (F := F) (G := G) ctx index result.1 result.2.1 result.2.2.1 result.2.2.2)) (List.range' 0 count) initial).bind (fun result => .done (proverRoundState (F := F) (G := G) result.1 result.2.1 result.2.2.1 result.2.2.2)) := by
  exact LoopPresentation.presentUniform roundSpec ctx (ctx.roles 0) (by simp) _ _
    (fun result => (proverRoundState (F := F) (G := G) result.1 result.2.1 result.2.2.1 result.2.2.2)) (fun result => proverRoundState_masked ctx _ rfl result.1 result.2.1 result.2.2.1 result.2.2.2)
    (fun result index => (proverRoundProcess (F := F) (G := G) ctx index result.1 result.2.1 result.2.2.1 result.2.2.2)) (fun result index => proverRound_process ctx _ rfl distinct index result.1 result.2.1 result.2.2.1 result.2.2.2 service) count bounded state initial start

def proverSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverPattern : InputPattern [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent (.cons .optional (.cons .absent .nil)))))))
noncomputable def proverForm : Form proverSignature.laws proverSignature.callees proverPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.math (⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (.input .here) (.cons (.input (.there .here)) (.cons (.input (.there (.there .here))) .nil))) (.split (.read .here .here) (.halt .incomplete) (.guard .index (.var .here) (.index 1) (.math (⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (.input (.there (.there .here))) (.cons (.input (.there (.there (.there .here)))) (.cons (.input (.there (.there (.there (.there .here))))) .nil))) (.split (.read .here .here) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.halt .incomplete) (.strict (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.guard .boolean (.calc .booleanEqual rfl (.cons (.result .here .here) (.cons (.bool false) .nil)) .here) (.bool true) (.strict (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil (.repeat (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) "s18" roundBody (.present (.var (.there (.there .here)))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.cons (.present (.result .here .here)) (.cons .absent (.cons .absent .nil)))))) (.cons .absent .nil) (.done (.cons (.read .here (.there (.there (.there .here)))) (.cons (.read .here .here) (.cons (.read .here (.there .here)) (.cons (.read .here (.there (.there .here))) (.cons .absent (.cons .absent .nil)))))))))))))))))

noncomputable def proverProcess (ctx : ProtocolContext) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (count : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) :=
  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (entries) (.cons (dimension) (.cons (width) .nil)))).bind fun (b4 : (Values (Component (assignment F G)) [.index])) =>
  match (b4).get .here with
  | none =>
    .halt .incomplete
  | some b5 =>
    @ite _ ((b5) = (1)) (Equality.decide (ringModel F G) .index (b5) (1))
      (
        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (entries) (.cons (dimension) (.cons (width) .nil)))).bind fun (b6 : (Values (Component (assignment F G)) [.index])) =>
        match (b6).get .here with
        | none =>
          .halt .incomplete
        | some b7 =>
          match count with
          | none =>
            .halt .incomplete
          | some b8 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"s3h7a6b637h696e64696365734h6c657373", .local, [.index, .index], [.boolean]⟩ : Helper) (.cons (b7) (.cons (b8) .nil))).bind fun (b9 : (Values (assignment F G) [.boolean])) =>
            @ite _ (((((b9).get .here) == (false))) = (true)) (Equality.decide (ringModel F G) .boolean ((((b9).get .here) == (false))) (true))
              (
                (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e079e1b3b9b36b339af5ada50497ef0577edcd5a30324fa8945b1f7d1b40765f", .local, [], [(.vector "bls12-381.fr")]⟩ : Helper) .nil).bind fun (b10 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
                (denoteRepeat (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 0) ((some (b8))) (.cons (entries) (.cons (dimension) (.cons (width) (.cons ((some ((b10).get .here))) (.cons (none) (.cons (none) .nil)))))) (.cons (none) .nil) (roundFn ctx (ctx.roles 0))).bind fun (b11 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
                .done ((.cons ((b11).get (.there (.there (.there .here)))) (.cons ((b11).get .here) (.cons ((b11).get (.there .here)) (.cons ((b11).get (.there (.there .here))) (.cons (none) (.cons (none) .nil)))))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")])))
              (.halt .reject))
      (.halt .reject)

theorem prover_normalized : normalize proverSignature bodyBody 0 2 proverPattern = .ok proverForm := by kernel_rfl
theorem prover_calls : proverForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem prover_presentation (ctx : ProtocolContext) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (count : (Option (Nat))) :
  ((proverForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons entries (.cons dimension (.cons width (.cons count .nil))))) = (proverProcess (F := F) (G := G) ctx entries dimension width count) := by kernel_rfl

theorem prover_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (count : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((proverPattern.environment (ringModel F G) (.cons entries (.cons dimension (.cons width (.cons count .nil)))))) = (proverProcess (F := F) (G := G) ctx entries dimension width count) := by
  subst self
  exact (sound_uniform proverSignature bodyBody 0 2 proverPattern proverForm
    prover_normalized prover_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons entries (.cons dimension (.cons width (.cons count .nil)))) _ rfl (emptyLaws _ _) (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold _)).trans
    (prover_presentation ctx entries dimension width count)

theorem prover_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (width : (Option (Nat))) (count : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverPattern.environment (ringModel F G) (.cons entries (.cons dimension (.cons width (.cons count .nil)))))).get =
  proverForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons entries (.cons dimension (.cons width (.cons count .nil)))) :=
  normalize_occurrence_sound proverSignature bodyBody 0 2
    proverPattern proverForm prover_normalized prover_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def proverView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  ((proverProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)) (input.get (.there (.there .here))) (input.get (.there (.there (.there (.there (.there .here)))))))).bind fun out => .done (.cons (out.get .here) (.cons (out.get (.there .here)) (.cons (out.get (.there (.there .here))) (.cons (out.get (.there (.there (.there .here)))) (.cons none (.cons none .nil))))))

theorem prover_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 0) input = proverView ctx input := by
  have environment : proverPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) .nil)))) =
      maskValues (ctx.roles 0) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) proverSignature 0 2 proverPattern proverForm
    prover_normalized prover_calls (emptyResults _) (actualCallees payload calleeKeys) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) .nil))))
    environment (emptyLaws _ _) (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold _)
  rw [prover_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out; rfl

end Reduce

noncomputable def boundCallees0 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ (fun ctx binders => Reduce.proverView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees0_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees0 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold input) (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold input)
  intro ctx binders distinct
  exact Reduce.prover_invocation ctx distinct _

namespace Reduce

def verifierRoundFinish : Values (fun _ : Ty => Carried) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional .nil))))))

def verifierRoundState (point : (Option ((List F)))) (claim : (Option (F))) : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.cons none (.cons none (.cons none (.cons none (.cons point (.cons claim .nil))))))

theorem verifierRoundState_masked (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1) (point : (Option ((List F)))) (claim : (Option (F))) :
  maskValues self (ctx.mapScopes [[0], [0], [0], [0], [1], [1]]) (verifierRoundState (F := F) (G := G) point claim) = (verifierRoundState (F := F) (G := G) point claim) := by
  subst self
  exact maskValues_embed (Value := assignment F G) ctx 1 verifierRoundFinish _ rfl (.cons point (.cons claim .nil))

def verifierRoundSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierRoundPattern : InputPattern [.index, (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0")] := (.cons .present (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional .nil))))))))
noncomputable def verifierRoundForm : Form verifierRoundSignature.laws verifierRoundSignature.callees verifierRoundPattern.scope [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.receive (.field "bls12-381.fr") "label_726f756e64_0" 0 (.receive (.field "bls12-381.fr") "label_726f756e64_1" 0 (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.guard (.field "bls12-381.fr") (.var .here) (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there .here)) .nil)) .here) (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657279_0" 0 (.var .here) (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.halt .incomplete) (.strict (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) (.cons (.var (.there .here)) .nil)) (.done (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.calc (.fieldSubtract "bls12-381.fr") rfl (.cons (.field "bls12-381.fr" 1) (.cons (.var (.there (.there .here))) .nil)) .here) (.cons (.var (.there (.there (.there (.there (.there (.there .here))))))) .nil)) .here) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there (.there (.there (.there .here)))))) .nil)) .here) .nil)) .here)) .nil))))))))))))))))

noncomputable def verifierRoundProcess (ctx : ProtocolContext) (service : (Option (Nat))) (point : (Option ((List F)))) (claim : (Option (F))) : (PIR.Process (Interface (ringModel F G)) (Tuple (assignment F G) [((.vector "bls12-381.fr"), true), ((.field "bls12-381.fr"), true)])) :=
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_0") ((ctx).roles 0)) fun (b4 : F) =>
  .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_726f756e64_1") ((ctx).roles 0)) fun (b5 : F) =>
  match claim with
  | none =>
    .halt .incomplete
  | some b6 =>
    @ite _ ((b6) = (((b4) + (b5)))) (Equality.decide (ringModel F G) (.field "bls12-381.fr") (b6) (((b4) + (b5))))
      (
        match service with
        | none =>
          .halt .incomplete
        | some b7 =>
          .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6368616c6c656e6765") "bls12-381.fr" (.cons (b7) .nil)) fun (b8 : F) =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 0) (b8)) fun _ =>
          match point with
          | none =>
            .halt .incomplete
          | some b9 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_08763b0dc78a869ee1ab72b02c31b0587181b10d6b99ff47d041839795c25e7d", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (b9) (.cons (b8) .nil))).bind fun (b10 : (Values (assignment F G) [(.vector "bls12-381.fr")])) =>
            .done (((some ((b10).get .here))), ((some ((((((((fieldLiteral (ringModel F G).toFieldModel "bls12-381.fr" 1)) - (b8))) * (b4))) + (((b8) * (b5)))))))))
      (.halt .reject)

theorem verifierRound_normalized : normalize verifierRoundSignature roundBody 1 2 verifierRoundPattern = .ok verifierRoundForm := by kernel_rfl
theorem verifierRound_calls : verifierRoundForm.CallsMatch := by apply Prod.ext <;> kernel_rfl
theorem verifierRound_finishes : verifierRoundForm.finishes verifierRoundFinish = true := by kernel_rfl

theorem verifierRound_presentation (ctx : ProtocolContext) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (service : (Option (Nat))) :
  ((verifierRoundForm).denoteWith (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (finishLeaf (ringModel F G) (emptyResults (ringModel F G)) (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional .nil))))))) (.cons index (.cons point (.cons claim (.cons service .nil))))) = (verifierRoundProcess (F := F) (G := G) ctx service point claim) := by kernel_rfl

theorem verifierRound_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (service : (Option (Nat))) :
  roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierRoundPattern).environment (ringModel F G) (.cons index (.cons point (.cons claim (.cons service .nil))))).get =
  verifierRoundForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons index (.cons point (.cons claim (.cons service .nil)))) :=
  normalize_occurrence_sound verifierRoundSignature roundBody 1 2
    verifierRoundPattern verifierRoundForm verifierRound_normalized verifierRound_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

theorem verifierRound_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (index : Nat) (point : (Option ((List F)))) (claim : (Option (F))) (service : (Option (Nat))) :
  roundFn (F := F) (G := G) ctx self (.cons (some index) ((verifierRoundState (F := F) (G := G) point claim).append (.cons service .nil))) =
    (verifierRoundProcess (F := F) (G := G) ctx service point claim).bind (fun result => .done (verifierRoundState (F := F) (G := G) result.1 result.2)) := by
  subst self
  exact (callback_sound_uniform verifierRoundSignature roundBody 1 2 verifierRoundPattern verifierRoundFinish verifierRoundForm
    verifierRound_normalized verifierRound_calls verifierRound_finishes ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons index (.cons point (.cons claim (.cons service .nil)))) _ (by kernel_rfl) (emptyLaws _ _) (boundCallees0_hold _)).trans
    (congrArg₂ PIR.Process.bind (verifierRound_presentation ctx index point claim service)
      (by funext result; exact congrArg PIR.Process.done (by kernel_rfl)))

theorem verifierRound_fold (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2) (service : (Option (Nat)))
  (count : Nat) (bounded : count ≤ roundSpec.maximum)
  (state : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) (initial : Tuple (assignment F G) (carried verifierRoundFinish))
  (start : maskValues (ctx.roles 1) (ctx.mapScopes roundSpec.stateScopes) state = (verifierRoundState (F := F) (G := G) initial.1 initial.2)) :
  denoteRepeat roundSpec ctx (ctx.roles 1) (some count) state (.cons service .nil) (roundFn ctx (ctx.roles 1)) =
    (Finite.fold (fun result index => (verifierRoundProcess (F := F) (G := G) ctx service result.1 result.2)) (List.range' 0 count) initial).bind (fun result => .done (verifierRoundState (F := F) (G := G) result.1 result.2)) := by
  exact LoopPresentation.presentUniform roundSpec ctx (ctx.roles 1) (by simp) _ _
    (fun result => (verifierRoundState (F := F) (G := G) result.1 result.2)) (fun result => verifierRoundState_masked ctx _ rfl result.1 result.2)
    (fun result index => (verifierRoundProcess (F := F) (G := G) ctx service result.1 result.2)) (fun result index => verifierRound_process ctx _ rfl distinct index result.1 result.2 service) count bounded state initial start

def verifierSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierPattern : InputPattern [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")] := (.cons .absent (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional (.cons .optional .nil)))))))
noncomputable def verifierForm : Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.math (⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons .absent (.cons .absent (.cons .absent .nil))) (.split (.read .here .here) (.math (⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons .absent (.cons .absent (.cons .absent .nil))) (.split (.input (.there (.there .here))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.strict (⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.repeat (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) "s18" roundBody (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil)))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) .nil) (.split (.read .here (.there (.there (.there (.there .here))))) (.halt .incomplete) (.split (.read (.there .here) (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.strict (⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.done (.cons (.read (.there (.there (.there .here))) (.there (.there (.there .here)))) (.cons (.read (.there (.there (.there .here))) .here) (.cons (.read (.there (.there (.there .here))) (.there .here)) (.cons (.read (.there (.there (.there .here))) (.there (.there .here))) (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil))))))))))))))) (.math (⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons .absent (.cons .absent (.cons .absent .nil))) (.split (.input (.there (.there (.there .here)))) (.halt .incomplete) (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.strict (⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.repeat (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) "s18" roundBody (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.cons .absent (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil)))))) (.cons (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) .nil) (.split (.read .here (.there (.there (.there (.there .here))))) (.halt .incomplete) (.split (.read (.there .here) (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.strict (⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) .nil)) (.done (.cons (.read (.there (.there (.there .here))) (.there (.there (.there .here)))) (.cons (.read (.there (.there (.there .here))) .here) (.cons (.read (.there (.there (.there .here))) (.there .here)) (.cons (.read (.there (.there (.there .here))) (.there (.there .here))) (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) .nil)))))))))))))))))

noncomputable def verifierProcess (ctx : ProtocolContext) (point : (Option ((List F)))) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) :=
  (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (none) (.cons (none) (.cons (none) .nil)))).bind fun (b4 : (Values (Component (assignment F G)) [.index])) =>
  match (b4).get .here with
  | none =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (none) (.cons (none) (.cons (none) .nil)))).bind fun (_b6 : (Values (Component (assignment F G)) [.index])) =>
    match point with
    | none =>
      .halt .incomplete
    | some b7 =>
      match claim with
      | none =>
        .halt .incomplete
      | some b8 =>
        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b7) (.cons (b8) .nil))).bind fun (b9 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
        (denoteRepeat (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 1) (count) (.cons (none) (.cons (none) (.cons (none) (.cons (none) (.cons ((some ((b9).get .here))) (.cons ((some ((b9).get (.there .here)))) .nil)))))) (.cons (service) .nil) (roundFn ctx (ctx.roles 1))).bind fun (b10 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
        match (b10).get (.there (.there (.there (.there .here)))) with
        | none =>
          .halt .incomplete
        | some b11 =>
          match (b10).get (.there (.there (.there (.there (.there .here))))) with
          | none =>
            .halt .incomplete
          | some b12 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b11) (.cons (b12) .nil))).bind fun (b13 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
            .done ((.cons ((b10).get (.there (.there (.there .here)))) (.cons ((b10).get .here) (.cons ((b10).get (.there .here)) (.cons ((b10).get (.there (.there .here))) (.cons ((some ((b13).get .here))) (.cons ((some ((b13).get (.there .here)))) .nil)))))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))
  | some _b5 =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", .math, [(.vector "bls12-381.fr"), .index, .index], [.index]⟩ : Helper) (.cons (none) (.cons (none) (.cons (none) .nil)))).bind fun (_b14 : (Values (Component (assignment F G)) [.index])) =>
    match point with
    | none =>
      .halt .incomplete
    | some b15 =>
      match claim with
      | none =>
        .halt .incomplete
      | some b16 =>
        (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_e8df957aab384c1d5416600c13a571512206e97abfbf6e0e9cddac5c84860d07", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b15) (.cons (b16) .nil))).bind fun (b17 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
        (denoteRepeat (⟨[(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.service "random.bls12-381.fr/0")], [0, 1], [[0], [0], [0], [0], [1], [1]], 4⟩ : RepeatSpec) ctx (ctx.roles 1) (count) (.cons (none) (.cons (none) (.cons (none) (.cons (none) (.cons ((some ((b17).get .here))) (.cons ((some ((b17).get (.there .here)))) .nil)))))) (.cons (service) .nil) (roundFn ctx (ctx.roles 1))).bind fun (b18 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
        match (b18).get (.there (.there (.there (.there .here)))) with
        | none =>
          .halt .incomplete
        | some b19 =>
          match (b18).get (.there (.there (.there (.there (.there .here))))) with
          | none =>
            .halt .incomplete
          | some b20 =>
            (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c36a2d2c6bd38573735fb9b90d1a3848c562d2c1f688234e2b669408e9c9eea9", .local, [(.vector "bls12-381.fr"), (.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b19) (.cons (b20) .nil))).bind fun (b21 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
            .done ((.cons ((b18).get (.there (.there (.there .here)))) (.cons ((b18).get .here) (.cons ((b18).get (.there .here)) (.cons ((b18).get (.there (.there .here))) (.cons ((some ((b21).get .here))) (.cons ((some ((b21).get (.there .here)))) .nil)))))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))

theorem verifier_normalized : normalize verifierSignature bodyBody 1 2 verifierPattern = .ok verifierForm := by kernel_rfl
theorem verifier_calls : verifierForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem verifier_presentation (ctx : ProtocolContext) (point : (Option ((List F)))) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) :
  ((verifierForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (.cons point (.cons claim (.cons count (.cons service .nil))))) = (verifierProcess (F := F) (G := G) ctx point claim count service) := by kernel_rfl

theorem verifier_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (point : (Option ((List F)))) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((verifierPattern.environment (ringModel F G) (.cons point (.cons claim (.cons count (.cons service .nil)))))) = (verifierProcess (F := F) (G := G) ctx point claim count service) := by
  subst self
  exact (sound_uniform verifierSignature bodyBody 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons point (.cons claim (.cons count (.cons service .nil)))) _ rfl (emptyLaws _ _) (boundCallees0_hold _)).trans
    (verifier_presentation ctx point claim count service)

theorem verifier_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (point : (Option ((List F)))) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierPattern.environment (ringModel F G) (.cons point (.cons claim (.cons count (.cons service .nil)))))).get =
  verifierForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons point (.cons claim (.cons count (.cons service .nil)))) :=
  normalize_occurrence_sound verifierSignature bodyBody 1 2
    verifierPattern verifierForm verifier_normalized verifier_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def verifierView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  ((verifierProcess (F := F) (G := G) ctx (input.get (.there (.there (.there .here)))) (input.get (.there (.there (.there (.there .here))))) (input.get (.there (.there (.there (.there (.there .here)))))) (input.get (.there (.there (.there (.there (.there (.there .here))))))))).bind fun out => .done (.cons none (.cons none (.cons none (.cons none (.cons (out.get (.there (.there (.there (.there .here))))) (.cons (out.get (.there (.there (.there (.there (.there .here)))))) .nil))))))

theorem verifier_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 1) input = verifierView ctx input := by
  have environment : verifierPattern.environment (ringModel F G) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil)))) =
      maskValues (ctx.roles 1) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) verifierSignature 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls (emptyResults _) (boundCallees0) ctx distinct input (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil))))
    environment (emptyLaws _ _) (boundCallees0_hold _)
  rw [verifier_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out; rfl

end Reduce

noncomputable def boundCallees1 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees0) ⟨1, by decide +kernel⟩ (fun ctx binders => Reduce.verifierView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees1_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees1 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees0) ⟨1, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold input) (boundCallees0_hold input)
  intro ctx binders distinct
  exact Reduce.verifier_invocation ctx distinct _

namespace Reduce

end Reduce

namespace Root

abbrev bodyDefinition : CheckedProtocol := payload.protocols.get ⟨1, by decide +kernel⟩
abbrev bodyInputs : List Ty := [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]
abbrev bodyOutputs : List Ty := [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]
abbrev bodyBody := bodyDefinition.body
theorem bodyBody_checked : bodyDefinition.body = bodyBody := rfl
theorem bodyBody_raw : bodyDefinition.raw = bodyBody.erase := by kernel_rfl

def bodyFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  fun args => bodyBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def proverSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverPattern : InputPattern [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .optional (.cons .absent (.cons .optional (.cons .absent .nil)))))
noncomputable def proverForm : Form proverSignature.laws proverSignature.callees proverPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input .here) (.halt .incomplete) (.split (.input (.there (.there .here))) (.halt .incomplete) (.strict (⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩ : Helper) (.cons (.var (.there .here)) (.cons (.var .here) (.cons (.index 1) .nil))) (.apply ⟨0, by decide⟩ (⟨"zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [1], [1]]⟩ : ProtocolSignature) [0, 1] "s5" (by change (Values (Argument [] [(.results [(.vector "bls12-381.fr"), .index, .index]), (.value .index), (.value (.vector "bls12-381.fr")), (.component (.vector "bls12-381.fr")), (.component .index), (.component .index)]) [(.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) (.cons (.present (.result .here (.there (.there .here)))) (.cons .absent (.cons .absent (.cons (.input (.there (.there (.there (.there (.there .here)))))) (.cons .absent .nil)))))))) (.math (⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (.read .here (.there .here)) (.cons (.read .here (.there (.there .here))) (.cons (.read .here (.there (.there (.there .here)))) .nil))) (.done (.cons (.read (.there .here) .here) (.cons (.read .here .here) (.cons .absent (.cons .absent .nil))))))))))

noncomputable def proverProcess (ctx : ProtocolContext) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (count : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) :=
  match entries with
  | none =>
    .halt .incomplete
  | some b3 =>
    match dimension with
    | none =>
      .halt .incomplete
    | some b4 =>
      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_8ef40b11d6cf00ead63fb713e26ae93987287c607cdcdc4860180f6744dc588a", .local, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr"), .index, .index]⟩ : Helper) (.cons (b3) (.cons (b4) (.cons (1) .nil)))).bind fun (b5 : (Values (assignment F G) [(.vector "bls12-381.fr"), .index, .index])) =>
      ((fun ctx binders => Reduce.proverView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))) ((ctx).enter "s5" [0, 1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons ((some ((b5).get .here))) (.cons ((some ((b5).get (.there .here)))) (.cons ((some ((b5).get (.there (.there .here))))) (.cons (none) (.cons (none) (.cons (count) (.cons (none) .nil))))))))).bind fun (b6 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
      (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons ((b6).get (.there .here)) (.cons ((b6).get (.there (.there .here))) (.cons ((b6).get (.there (.there (.there .here)))) .nil)))).bind fun (b7 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr")])) =>
      .done ((.cons ((b6).get .here) (.cons ((b7).get .here) (.cons (none) (.cons (none) .nil)))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))

theorem prover_normalized : normalize proverSignature bodyBody 0 2 proverPattern = .ok proverForm := by kernel_rfl
theorem prover_calls : proverForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem prover_presentation (ctx : ProtocolContext) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (count : (Option (Nat))) :
  ((proverForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (boundCallees1) (.cons entries (.cons dimension (.cons count .nil)))) = (proverProcess (F := F) (G := G) ctx entries dimension count) := by kernel_rfl

theorem prover_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (count : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((proverPattern.environment (ringModel F G) (.cons entries (.cons dimension (.cons count .nil))))) = (proverProcess (F := F) (G := G) ctx entries dimension count) := by
  subst self
  exact (sound_uniform proverSignature bodyBody 0 2 proverPattern proverForm
    prover_normalized prover_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees1)
    (.cons entries (.cons dimension (.cons count .nil))) _ rfl (emptyLaws _ _) (boundCallees1_hold _)).trans
    (prover_presentation ctx entries dimension count)

theorem prover_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (entries : (Option ((List F)))) (dimension : (Option (Nat))) (count : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverPattern.environment (ringModel F G) (.cons entries (.cons dimension (.cons count .nil))))).get =
  proverForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons entries (.cons dimension (.cons count .nil))) :=
  normalize_occurrence_sound proverSignature bodyBody 0 2
    proverPattern proverForm prover_normalized prover_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def proverView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  ((proverProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)) (input.get (.there (.there (.there .here)))))).bind fun out => .done (.cons (out.get .here) (.cons (out.get (.there .here)) (.cons none (.cons none .nil))))

theorem prover_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 0) input = proverView ctx input := by
  have environment : proverPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there (.there .here)))) .nil))) =
      maskValues (ctx.roles 0) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) proverSignature 0 2 proverPattern proverForm
    prover_normalized prover_calls (emptyResults _) (boundCallees1) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there (.there .here)))) .nil)))
    environment (emptyLaws _ _) (boundCallees1_hold _)
  rw [prover_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out; rfl

theorem prover_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 0 input = proverView {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans
    (prover_invocation {} (RosterDistinct.root _ _) input)

end Root

noncomputable def boundCallees2 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees1) ⟨2, by decide +kernel⟩ (fun ctx binders => Root.proverView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees2_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees2 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees1) ⟨2, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold input) (boundCallees1_hold input)
  intro ctx binders distinct
  exact Root.prover_invocation ctx distinct _

namespace Root

def verifierSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierPattern : InputPattern [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")] := (.cons .absent (.cons .absent (.cons .optional (.cons .optional (.cons .optional .nil)))))
noncomputable def verifierForm : Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")] :=
  (.split (.input .here) (.halt .incomplete) (.strict (⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (.var .here) .nil) (.apply ⟨1, by decide⟩ (⟨"zkl_145fec0475c3361a656f102bec3f8b514a2557e3ec22afda8a8f34050f1bff6d", ["role00000000", "role00000001"], [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")], [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")], [[0], [0], [0], [1], [1], [0, 1], [1]], [[0], [0], [0], [0], [1], [1]]⟩ : ProtocolSignature) [0, 1] "s5" (by change (Values (Argument [] [(.results [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]), (.value (.field "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) [(.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons .absent (.cons .absent (.cons .absent (.cons (.present (.result .here .here)) (.cons (.present (.result .here (.there .here))) (.cons (.input (.there (.there (.there .here)))) (.cons (.input (.there (.there (.there (.there .here))))) .nil)))))))) (.math (⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons .absent (.cons .absent (.cons .absent .nil))) (.done (.cons .absent (.cons (.read .here .here) (.cons (.read (.there .here) (.there (.there (.there (.there .here))))) (.cons (.read (.there .here) (.there (.there (.there (.there (.there .here)))))) .nil)))))))))

noncomputable def verifierProcess (ctx : ProtocolContext) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) :=
  match claim with
  | none =>
    .halt .incomplete
  | some b3 =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).closed (⟨"zkl_c0a3a2b8b5f989e0e9c138a171631d20dc8bd296769b6ee7636d2d79a8518ba0", .local, [(.field "bls12-381.fr")], [(.vector "bls12-381.fr"), (.field "bls12-381.fr")]⟩ : Helper) (.cons (b3) .nil)).bind fun (b4 : (Values (assignment F G) [(.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
    ((fun ctx binders => Reduce.verifierView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders) : ProtocolContext → (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]) → (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))) ((ctx).enter "s5" [0, 1]) (by change (Binders (ringModel F G) [(.component (.vector "bls12-381.fr")), (.component .index), (.component .index), (.component (.vector "bls12-381.fr")), (.component (.field "bls12-381.fr")), (.component .index), (.component (.service "random.bls12-381.fr/0"))]); exact (.cons (none) (.cons (none) (.cons (none) (.cons ((some ((b4).get .here))) (.cons ((some ((b4).get (.there .here)))) (.cons (count) (.cons (service) .nil))))))))).bind fun (b5 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), .index, .index, (.vector "bls12-381.fr"), (.field "bls12-381.fr")])) =>
    (invoke ((plainHelpers (F := F) (G := G) payload).toOn).components (⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", .math, [(.vector "bls12-381.fr"), .index, .index], [(.vector "bls12-381.fr")]⟩ : Helper) (.cons (none) (.cons (none) (.cons (none) .nil)))).bind fun (b6 : (Values (Component (assignment F G)) [(.vector "bls12-381.fr")])) =>
    .done ((.cons (none) (.cons ((b6).get .here) (.cons ((b5).get (.there (.there (.there (.there .here))))) (.cons ((b5).get (.there (.there (.there (.there (.there .here)))))) .nil)))) : (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]))

theorem verifier_normalized : normalize verifierSignature bodyBody 1 2 verifierPattern = .ok verifierForm := by kernel_rfl
theorem verifier_calls : verifierForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem verifier_presentation (ctx : ProtocolContext) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) :
  ((verifierForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees2) (.cons claim (.cons count (.cons service .nil)))) = (verifierProcess (F := F) (G := G) ctx claim count service) := by kernel_rfl

theorem verifier_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((verifierPattern.environment (ringModel F G) (.cons claim (.cons count (.cons service .nil))))) = (verifierProcess (F := F) (G := G) ctx claim count service) := by
  subst self
  exact (sound_uniform verifierSignature bodyBody 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees2)
    (.cons claim (.cons count (.cons service .nil))) _ rfl (emptyLaws _ _) (boundCallees2_hold _)).trans
    (verifier_presentation ctx claim count service)

theorem verifier_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (claim : (Option (F))) (count : (Option (Nat))) (service : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierPattern.environment (ringModel F G) (.cons claim (.cons count (.cons service .nil))))).get =
  verifierForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons claim (.cons count (.cons service .nil))) :=
  normalize_occurrence_sound verifierSignature bodyBody 1 2
    verifierPattern verifierForm verifier_normalized verifier_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def verifierView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [(.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.vector "bls12-381.fr"), (.field "bls12-381.fr")]) :=
  ((verifierProcess (F := F) (G := G) ctx (input.get (.there (.there .here))) (input.get (.there (.there (.there .here)))) (input.get (.there (.there (.there (.there .here))))))).bind fun out => .done (.cons none (.cons none (.cons (out.get (.there (.there .here))) (.cons (out.get (.there (.there (.there .here)))) .nil))))

theorem verifier_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (input : Values (Component (assignment F G)) [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 1) input = verifierView ctx input := by
  have environment : verifierPattern.environment (ringModel F G) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) .nil))) =
      maskValues (ctx.roles 1) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) verifierSignature 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls (emptyResults _) (boundCallees2) ctx distinct input (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) .nil)))
    environment (emptyLaws _ _) (boundCallees2_hold _)
  rw [verifier_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out with | cons _ out => cases out; rfl

theorem verifier_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 1 input = verifierView {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans
    (verifier_invocation {} (RosterDistinct.root _ _) input)

end Root

noncomputable def boundCallees3 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees2) ⟨3, by decide +kernel⟩ (fun ctx binders => Root.verifierView (F := F) (G := G) ctx ((optionalPattern [(.vector "bls12-381.fr"), .index, (.field "bls12-381.fr"), .index, (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees3_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees3 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees2) ⟨3, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Scalar.SumcheckReductionBindings.callees_hold input) (boundCallees2_hold input)
  intro ctx binders distinct
  exact Root.verifier_invocation ctx distinct _

namespace Root

end Root

end
end ZkcExamples.Structured.Generated.Scalar.SumcheckReduction
