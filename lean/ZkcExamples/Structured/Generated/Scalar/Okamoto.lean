module

public import ZkcExamples.Structured.Generated.Scalar.OkamotoBindingsCallbacks
public import Zkc.Source.Structured.LoopPresentation
public import Zkc.Source.Structured.InputVisibility
public import Zkc.Source.Structured.PlainHelpers
public import Zkc.Source.Structured.OccurrencePresentation
public import Zkc.Source.Structured.ProtocolPresentation

@[expose] public section

/-! Generated scope-derived source presentations. Regenerate with the Lean role-view printer. -/
namespace ZkcExamples.Structured.Generated.Scalar.Okamoto
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

abbrev program : Program := ZkcExamples.Structured.OkamotoViews.program
abbrev payload := program.payload
abbrev calleeKeys := ZkcExamples.Structured.Generated.Scalar.OkamotoBindings.calleeKeys

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

namespace Root

abbrev bodyDefinition : CheckedProtocol := payload.protocols.get ⟨0, by decide +kernel⟩
abbrev bodyInputs : List Ty := [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]
abbrev bodyOutputs : List Ty := [.boolean]
abbrev bodyBody := bodyDefinition.body
theorem bodyBody_checked : bodyDefinition.body = bodyBody := rfl
theorem bodyBody_raw : bodyDefinition.raw = bodyBody.erase := by kernel_rfl

def bodyFn (ctx : ProtocolContext) (self : Nat) : RegionFunction (Component (assignment F G)) (participantInterface F G) ([(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")], [.boolean]) :=
  fun args => bodyBody.denote (participantMeaningWith (.silent _) (participantActions F G) (plainHelpers payload) self (payload.plainProtocolTable F G) ctx) args.get

def proverSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def proverPattern : InputPattern [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .optional (.cons .absent .nil)))))))
noncomputable def proverForm : Form proverSignature.laws proverSignature.callees proverPattern.scope [.boolean] :=
  (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.query "label_66697273745f6e6f6e6365" "bls12-381.fr" (.cons (.var .here) .nil) (.query "label_7365636f6e645f6e6f6e6365" "bls12-381.fr" (.cons (.var (.there .here)) .nil) (.split (.input (.there (.there (.there .here)))) (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.halt .incomplete)) (.split (.input (.there (.there (.there (.there (.there .here)))))) (.halt .incomplete) (.send (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 1 (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.var (.there (.there (.there .here)))) .nil)) .here) (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there .here))) .nil)) .here) .nil)) .here) (.receive (.field "bls12-381.fr") "label_64656c6976657279_0" 1 (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.halt .incomplete) (.send (.field "bls12-381.fr") "label_66697273745f726573706f6e7365_0" 1 (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.var .here) .nil)) .here) .nil)) .here) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))))) (.halt .incomplete) (.send (.field "bls12-381.fr") "label_7365636f6e645f726573706f6e7365_0" 1 (.calc (.fieldAdd "bls12-381.fr") rfl (.cons (.var (.there (.there (.there (.there (.there .here)))))) (.cons (.calc (.fieldMultiply "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var .here) .nil)) .here) .nil)) .here) (.done (.cons .absent .nil)))))))))))))

noncomputable def proverProcess (ctx : ProtocolContext) (firstBase : (Option (G))) (secondBase : (Option (G))) (firstScalar : (Option (F))) (secondScalar : (Option (F))) (nonces : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  match nonces with
  | none =>
    .halt .incomplete
  | some b6 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f6e6f6e6365") "bls12-381.fr" (.cons (b6) .nil)) fun (b7 : F) =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f6e6f6e6365") "bls12-381.fr" (.cons (b6) .nil)) fun (b8 : F) =>
    match firstBase with
    | none =>
      match secondBase with
      | none =>
        .halt .incomplete
      | some _b10 =>
        .halt .incomplete
    | some b9 =>
      match secondBase with
      | none =>
        .halt .incomplete
      | some b11 =>
        .call (.send (ty := (.group "bls12-381.g1")) (qualifyProtocolSite (ctx).applicationPrefix "label_636f6d6d69746d656e74_0") ((ctx).roles 1) (((((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b7) (b9))) + (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b8) (b11)))))) fun _ =>
        .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 1)) fun (b12 : F) =>
        match firstScalar with
        | none =>
          .halt .incomplete
        | some b13 =>
          .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f726573706f6e7365_0") ((ctx).roles 1) (((b7) + (((b12) * (b13)))))) fun _ =>
          match secondScalar with
          | none =>
            .halt .incomplete
          | some b14 =>
            .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f726573706f6e7365_0") ((ctx).roles 1) (((b8) + (((b12) * (b14)))))) fun _ =>
            .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem prover_normalized : normalize proverSignature bodyBody 0 2 proverPattern = .ok proverForm := by kernel_rfl
theorem prover_calls : proverForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem prover_presentation (ctx : ProtocolContext) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (firstScalar : (Option (F))) (secondScalar : (Option (F))) (nonces : (Option (Nat))) :
  ((proverForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 0)) (actualCallees payload calleeKeys) (.cons firstBase (.cons secondBase (.cons point (.cons firstScalar (.cons secondScalar (.cons nonces .nil))))))) = (proverProcess (F := F) (G := G) ctx firstBase secondBase firstScalar secondScalar nonces) := by kernel_rfl

theorem prover_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 0)
  (distinct : RosterDistinct ctx 0 2) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (firstScalar : (Option (F))) (secondScalar : (Option (F))) (nonces : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((proverPattern.environment (ringModel F G) (.cons firstBase (.cons secondBase (.cons point (.cons firstScalar (.cons secondScalar (.cons nonces .nil)))))))) = (proverProcess (F := F) (G := G) ctx firstBase secondBase firstScalar secondScalar nonces) := by
  subst self
  exact (sound_uniform proverSignature bodyBody 0 2 proverPattern proverForm
    prover_normalized prover_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (actualCallees payload calleeKeys)
    (.cons firstBase (.cons secondBase (.cons point (.cons firstScalar (.cons secondScalar (.cons nonces .nil)))))) _ rfl (emptyLaws _ _) (ZkcExamples.Structured.Generated.Scalar.OkamotoBindings.callees_hold _)).trans
    (prover_presentation ctx firstBase secondBase point firstScalar secondScalar nonces)

theorem prover_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (firstScalar : (Option (F))) (secondScalar : (Option (F))) (nonces : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 0) protocols ctx Occurrence.iterations)
    ((proverPattern.environment (ringModel F G) (.cons firstBase (.cons secondBase (.cons point (.cons firstScalar (.cons secondScalar (.cons nonces .nil)))))))).get =
  proverForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 0)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons firstBase (.cons secondBase (.cons point (.cons firstScalar (.cons secondScalar (.cons nonces .nil)))))) :=
  normalize_occurrence_sound proverSignature bodyBody 0 2
    proverPattern proverForm prover_normalized prover_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def proverView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  ((proverProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)) (input.get (.there (.there (.there .here)))) (input.get (.there (.there (.there (.there .here))))) (input.get (.there (.there (.there (.there (.there .here)))))))).bind fun out => .done (.cons none .nil)

theorem prover_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 0 2)
  (input : Values (Component (assignment F G)) [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 0) input = proverView ctx input := by
  have environment : proverPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) .nil)))))) =
      maskValues (ctx.roles 0) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) proverSignature 0 2 proverPattern proverForm
    prover_normalized prover_calls (emptyResults _) (actualCallees payload calleeKeys) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there .here)))) (.cons (input.get (.there (.there (.there (.there .here))))) (.cons (input.get (.there (.there (.there (.there (.there .here)))))) .nil))))))
    environment (emptyLaws _ _) (ZkcExamples.Structured.Generated.Scalar.OkamotoBindings.callees_hold _)
  rw [prover_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

theorem prover_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 0 input = proverView {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 0 input).trans
    (prover_invocation {} (RosterDistinct.root _ _) input)

end Root

noncomputable def boundCallees0 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ (fun ctx binders => Root.proverView (F := F) (G := G) ctx ((optionalPattern [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees0_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees0 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (actualCallees payload calleeKeys) ⟨0, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Scalar.OkamotoBindings.callees_hold input) (ZkcExamples.Structured.Generated.Scalar.OkamotoBindings.callees_hold input)
  intro ctx binders distinct
  exact Root.prover_invocation ctx distinct _

namespace Root

def verifierSignature : Signature := ⟨[], true, false, [], calleeKeys⟩
def verifierPattern : InputPattern [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")] := (.cons .optional (.cons .optional (.cons .optional (.cons .absent (.cons .absent (.cons .absent (.cons .optional .nil)))))))
noncomputable def verifierForm : Form verifierSignature.laws verifierSignature.callees verifierPattern.scope [.boolean] :=
  (.receive (.group "bls12-381.g1") "label_636f6d6d69746d656e74_0" 0 (.split (.input (.there (.there (.there (.there .here))))) (.halt .incomplete) (.query "label_6368616c6c656e6765" "bls12-381.fr" (.cons (.var .here) .nil) (.send (.field "bls12-381.fr") "label_64656c6976657279_0" 0 (.var .here) (.receive (.field "bls12-381.fr") "label_66697273745f726573706f6e7365_0" 0 (.receive (.field "bls12-381.fr") "label_7365636f6e645f726573706f6e7365_0" 0 (.split (.input (.there (.there (.there (.there (.there .here)))))) (.split (.input (.there (.there (.there (.there (.there (.there .here))))))) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.done (.cons .absent .nil)) (.done (.cons .absent .nil))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.done (.cons .absent .nil)) (.done (.cons .absent .nil)))) (.split (.input (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there .here))))))))) (.done (.cons .absent .nil)) (.done (.cons .absent .nil))) (.split (.input (.there (.there (.there (.there (.there (.there (.there (.there (.there .here)))))))))) (.done (.cons .absent .nil)) (.done (.cons (.present (.calc (.groupEqual "bls12-381.g1") rfl (.cons (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there (.there .here))) (.cons (.var (.there (.there (.there (.there .here))))) .nil)) .here) (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var (.there .here)) (.cons (.var (.there (.there (.there .here)))) .nil)) .here) .nil)) .here) (.cons (.calc (.groupAdd "bls12-381.g1") rfl (.cons (.var (.there (.there (.there (.there (.there (.there (.there .here)))))))) (.cons (.calc (.groupScale "bls12-381.g1" "bls12-381.fr") rfl (.cons (.var .here) (.cons (.var (.there (.there (.there (.there (.there .here)))))) .nil)) .here) .nil)) .here) .nil)) .here)) .nil)))))))))))

noncomputable def verifierProcess (ctx : ProtocolContext) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (challenges : (Option (Nat))) : (PIR.Process (Interface (ringModel F G)) (Values (Component (assignment F G)) [.boolean])) :=
  .call (.receive (.group "bls12-381.g1") (qualifyProtocolSite (ctx).applicationPrefix "label_636f6d6d69746d656e74_0") ((ctx).roles 0)) fun (b4 : G) =>
  match challenges with
  | none =>
    .halt .incomplete
  | some b5 =>
    .call (.query (qualifyProtocolSite (ctx).applicationPrefix "label_6368616c6c656e6765") "bls12-381.fr" (.cons (b5) .nil)) fun (b6 : F) =>
    .call (.send (ty := (.field "bls12-381.fr")) (qualifyProtocolSite (ctx).applicationPrefix "label_64656c6976657279_0") ((ctx).roles 0) (b6)) fun _ =>
    .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_66697273745f726573706f6e7365_0") ((ctx).roles 0)) fun (b7 : F) =>
    .call (.receive (.field "bls12-381.fr") (qualifyProtocolSite (ctx).applicationPrefix "label_7365636f6e645f726573706f6e7365_0") ((ctx).roles 0)) fun (b8 : F) =>
    match firstBase with
    | none =>
      match secondBase with
      | none =>
        match point with
        | none =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
        | some _b11 =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
      | some _b10 =>
        match point with
        | none =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
        | some _b12 =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
    | some b9 =>
      match secondBase with
      | none =>
        match point with
        | none =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
        | some _b14 =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
      | some b13 =>
        match point with
        | none =>
          .done ((.cons (none) .nil) : (Values (Component (assignment F G)) [.boolean]))
        | some b15 =>
          .done ((.cons ((some (((Op.evalTotal (ringModel F G) (.groupEqual "bls12-381.g1") rfl (.cons (((((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b7) (b9))) + (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b8) (b13))))) (.cons (((b4) + (((ringModel F G).smul "bls12-381.g1" "bls12-381.fr" (b6) (b15))))) .nil))).get .here)))) .nil) : (Values (Component (assignment F G)) [.boolean]))

theorem verifier_normalized : normalize verifierSignature bodyBody 1 2 verifierPattern = .ok verifierForm := by kernel_rfl
theorem verifier_calls : verifierForm.CallsMatch := by apply Prod.ext <;> kernel_rfl

theorem verifier_presentation (ctx : ProtocolContext) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (challenges : (Option (Nat))) :
  ((verifierForm).denote (ringModel F G) ((plainHelpers (F := F) (G := G) payload).toOn) (emptyResults (ringModel F G)) (ctx) (Runs.uniform (plainHelpers payload) (payload.plainProtocolTable F G) ctx (ctx.roles 1)) (boundCallees0) (.cons firstBase (.cons secondBase (.cons point (.cons challenges .nil))))) = (verifierProcess (F := F) (G := G) ctx firstBase secondBase point challenges) := by kernel_rfl

theorem verifier_process (ctx : ProtocolContext) (self : Nat) (role : self = ctx.roles 1)
  (distinct : RosterDistinct ctx 1 2) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (challenges : (Option (Nat))) :
  bodyFn (F := F) (G := G) ctx self ((verifierPattern.environment (ringModel F G) (.cons firstBase (.cons secondBase (.cons point (.cons challenges .nil)))))) = (verifierProcess (F := F) (G := G) ctx firstBase secondBase point challenges) := by
  subst self
  exact (sound_uniform verifierSignature bodyBody 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls ctx distinct
    (plainHelpers payload) (payload.plainProtocolTable F G) (emptyResults _) (boundCallees0)
    (.cons firstBase (.cons secondBase (.cons point (.cons challenges .nil)))) _ rfl (emptyLaws _ _) (boundCallees0_hold _)).trans
    (verifier_presentation ctx firstBase secondBase point challenges)

theorem verifier_observed (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
  (masked : ProtocolPresentation.Masked protocols) (firstBase : (Option (G))) (secondBase : (Option (G))) (point : (Option (G))) (challenges : (Option (Nat))) :
  bodyBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    (Occurrence.helpers (ringModel F G) payload) (ctx.roles 1) protocols ctx Occurrence.iterations)
    ((verifierPattern.environment (ringModel F G) (.cons firstBase (.cons secondBase (.cons point (.cons challenges .nil)))))).get =
  verifierForm.denoteOn (ringModel F G) Occurrence.actions (Occurrence.helpers (ringModel F G) payload)
    (emptyResults _) ctx (runsAtOn (ringModel F G) Occurrence.actions Occurrence.iterations
      (Occurrence.helpers (ringModel F G) payload) protocols ctx 1)
    (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) (.cons firstBase (.cons secondBase (.cons point (.cons challenges .nil)))) :=
  normalize_occurrence_sound verifierSignature bodyBody 1 2
    verifierPattern verifierForm verifier_normalized verifier_calls distinct
    (emptyResults _) (ProtocolPresentation.callees (ringModel F G) calleeKeys protocols) _ (emptyLaws _ _) (observedCallees_hold protocols masked _)

noncomputable def verifierView (ctx : ProtocolContext) (input : Values (Component (assignment F G)) [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]) :
    PIR.Process (participantInterface F G) (Values (Component (assignment F G)) [.boolean]) :=
  ((verifierProcess (F := F) (G := G) ctx (input.get .here) (input.get (.there .here)) (input.get (.there (.there .here))) (input.get (.there (.there (.there (.there (.there (.there .here))))))))).bind fun out => .done (.cons (out.get .here) .nil)

theorem verifier_invocation (ctx : ProtocolContext) (distinct : RosterDistinct ctx 1 2)
  (input : Values (Component (assignment F G)) [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]) :
  invokeProtocol (payload.plainProtocolTable F G) bodyDefinition.signature ctx (ctx.roles 1) input = verifierView ctx input := by
  have environment : verifierPattern.environment (ringModel F G) (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil)))) =
      maskValues (ctx.roles 1) (ctx.mapScopes bodyDefinition.inputScopes) input := by
    rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.inputScopes (by decide +kernel)]
    cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input with | cons _ input => cases input; rfl
  have equation := invocation payload bodyDefinition (List.get_mem _ _) verifierSignature 1 2 verifierPattern verifierForm
    verifier_normalized verifier_calls (emptyResults _) (boundCallees0) ctx distinct input (.cons (input.get .here) (.cons (input.get (.there .here)) (.cons (input.get (.there (.there .here))) (.cons (input.get (.there (.there (.there (.there (.there (.there .here))))))) .nil))))
    environment (emptyLaws _ _) (boundCallees0_hold _)
  rw [verifier_presentation] at equation
  refine equation.trans ?_
  apply congrArg (PIR.Process.bind _)
  funext out
  rw [InputVisibility.mask_context (model := ringModel F G) distinct bodyDefinition.outputScopes (by decide +kernel)]
  cases out with | cons _ out => cases out; rfl

theorem verifier_participant (input : Values (Component (assignment F G)) payload.entry.inputs) :
  program.participant F G 1 input = verifierView {} input := by
  exact (payload.protocolTable_forgetSites (F := F) (G := G) payload.entry.signature {} 1 input).trans
    (verifier_invocation {} (RosterDistinct.root _ _) input)

end Root

noncomputable def boundCallees1 : CalleeProcesses (ringModel F G) calleeKeys :=
  (Function.update (boundCallees0) ⟨1, by decide +kernel⟩ (fun ctx binders => Root.verifierView (F := F) (G := G) ctx ((optionalPattern [(.group "bls12-381.g1"), (.group "bls12-381.g1"), (.group "bls12-381.g1"), (.field "bls12-381.fr"), (.field "bls12-381.fr"), (.service "random.bls12-381.fr/0"), (.service "random.bls12-381.fr/0")]).environment (ringModel F G) binders)))
theorem boundCallees1_hold {inputs : List Ty} (input : Values (Component (assignment F G)) inputs) :
  CalleesHold (payload.plainProtocolTable F G) boundCallees1 input := by
  apply callees_update _ (actualCallees payload calleeKeys) (boundCallees0) ⟨1, by decide +kernel⟩ _ input (ZkcExamples.Structured.Generated.Scalar.OkamotoBindings.callees_hold input) (boundCallees0_hold input)
  intro ctx binders distinct
  exact Root.verifier_invocation ctx distinct _

namespace Root

end Root

end
end ZkcExamples.Structured.Generated.Scalar.Okamoto
