module

public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsSumcheck
public import Zkc.Construction.Uniform.ScalarHandles

@[expose] public section

/-! Capability naturality of the complete TwoSums source, before compilation.
Both captured calls, optional helper results and all source refusals remain in
this equation. No constructed artifact or routing simulation is used. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.ComposedSumcheckSourceHandles
open Zkc.Source Zkc.Source.Structured Zkc.Construction Zkc.Construction.Uniform
open ZkcExamples.Structured
open OriginalSumcheckLibrary SumcheckVerifierBodies
attribute [local implicit_reducible] CheckedProtocol.signature
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev payload := Generated.Original.TwoSums.payload
abbrev project : PIR.OperationInterpretation (Occurrence.signature (uniformCarriers F G)) (Actions F G) :=
  fun operation => (Occurrence.erase operation).interpret CommonAdapter.project

private def closedTables : Evaluation.ComponentTables F G closedInterface :=
  payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩

private theorem closed_lift : Evaluation.ComponentTables.Interprets
    (closedLift (I := Occurrence.signature (uniformCarriers F G)))
    (closedTables (F := F) (G := G)) (helpers payload) :=
  Evaluation.ComponentTables.fold_interpret _ (SiteObservations.silent_interpret _) (.empty _) payload.definitions

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem closed_natural {A : Type} (process : PIR.Process closedInterface A) (handle : Nat) :
    ((process.interpret (closedLift (I := Occurrence.signature (uniformCarriers F G)))).interpret project).interpret
      (ScalarHandles.replace handle) =
    (process.interpret (closedLift (I := Occurrence.signature (uniformCarriers F G)))).interpret project := by
  simp only [PIR.Process.interpret_comp]
  congr 1
  funext impossible
  exact nomatch impossible

private theorem helper_closed (entry : Helper) (arguments : Values (assignment F G) entry.inputs) (handle : Nat) :
    ((invoke (helpers payload).closed entry arguments).interpret project).interpret (ScalarHandles.replace handle) =
    (invoke (helpers payload).closed entry arguments).interpret project := by
  rw [← closed_lift.closed]
  exact closed_natural _ handle

private theorem helper_components (entry : Helper)
    (arguments : Values (Component (assignment F G)) entry.inputs) (handle : Nat) :
    ((invoke (helpers payload).components entry arguments).interpret project).interpret (ScalarHandles.replace handle) =
    (invoke (helpers payload).components entry arguments).interpret project := by
  rw [← closed_lift.components]
  exact closed_natural _ handle

private theorem owned (self owner : Nat) (entry : Helper)
    (arguments : Values (Component (assignment F G)) entry.inputs) (handle : Nat) :
    ((Participant.owned self owner (invoke (helpers payload).closed entry) arguments).interpret project).interpret
      (ScalarHandles.replace handle) =
    (Participant.owned self owner (invoke (helpers payload).closed entry) arguments).interpret project := by
  unfold Participant.owned
  split
  · split
    · rfl
    · simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
      rw [helper_closed (G := G)]
  · rfl

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem round_natural (ctx : ProtocolContext) (original replacement : Nat)
    (point : Option (List F)) (claim : Option F) :
    (((SumcheckVerifierLaws.roundPlain (G := G) ctx (some original) (point, claim)).interpret
      CommonAdapter.project).interpret (ScalarHandles.replace replacement)) =
    (SumcheckVerifierLaws.roundPlain ctx (some replacement) (point, claim)).interpret CommonAdapter.project := by
  simp only [SumcheckVerifierLaws.roundPlain, PIR.Process.interpret, CommonAdapter.project,
    ScalarHandles.replace, PIR.Process.bind]
  congr 1
  funext low
  congr 1
  funext high
  cases claim with
  | none => rfl
  | some claim =>
    dsimp only
    by_cases valid : claim = low + high
    all_goals simp only [valid, ite_true, ite_false, PIR.Process.interpret, CommonAdapter.project,
      ScalarHandles.replace, PIR.Process.bind]
    · congr 1
      funext answer
      congr 1
      funext acknowledgement
      cases point <;> rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
private theorem actions_project {A : Type} (process : PIR.Process (participantInterface F G) A) :
    (process.interpret actions).interpret project = process.interpret CommonAdapter.project := by
  rw [PIR.Process.interpret_comp]
  congr 1
  funext operation
  simp only [actions, Occurrence.actions, project, Occurrence.erase, PIR.Process.interpret,
    PIR.Process.bind_done]

private theorem callback_natural (maximum : Nat) (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (original replacement index : Nat)
    (state : Values (Component (assignment F G)) repeatState) :
    ((Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) ctx (ctx.roles 1)
      (.cons (some original) .nil) (round payload ctx (ctx.roles 1)) state index
      Occurrence.iterations repeatSite).interpret project).interpret (ScalarHandles.replace replacement) =
    (Repeat.stepOn (carriers := uniformCarriers F G) (repeatSpec maximum) ctx (ctx.roles 1)
      (.cons (some replacement) .nil) (round payload ctx (ctx.roles 1)) state index
      Occurrence.iterations repeatSite).interpret project := by
  cases state with
  | cons a state =>
    cases state with
    | cons b state =>
      cases state with
      | cons c state =>
        cases state with
        | cons d state =>
          cases state with
          | cons point state =>
            cases state with
            | cons claim state =>
              cases state
              have mask : maskValues (ctx.roles 1) (ctx.mapScopes (repeatSpec maximum).stateScopes)
                  (.cons a (.cons b (.cons c (.cons d (.cons point (.cons claim .nil)))))) =
                  SumcheckVerifierLaws.embedV (G := G) (point, claim) := by
                simp [maskValues, ProtocolContext.mapScopes, SumcheckVerifierLaws.embedV,
                  SumcheckRoundNormalForms.verifierState, Participant.restrict, Ne.symm separate]
              simp only [Repeat.stepOn, mask, IterationObservations.within, Occurrence.iterations,
                PIR.Process.interpret_bind, PIR.Process.interpret, project, Occurrence.erase, PIR.Process.bind]
              rw [round_verifier payload Generated.Bindings.TwoSumsSumcheck.helper_bodies _ _ rfl separate,
                round_verifier payload Generated.Bindings.TwoSumsSumcheck.helper_bodies _ _ rfl separate]
              simp only [PIR.Process.interpret_bind, PIR.Process.interpret, PIR.Process.bind_done,
                actions_project, round_natural]

private theorem repeat_natural (maximum : Nat) (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (original replacement : Nat) (count : Option Nat)
    (state : Values (Component (assignment F G)) repeatState) :
    ((denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec maximum) ctx (ctx.roles 1) count state
      (.cons (some original) .nil) (round payload ctx (ctx.roles 1)) Occurrence.iterations repeatSite).interpret
      project).interpret (ScalarHandles.replace replacement) =
    (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec maximum) ctx (ctx.roles 1) count state
      (.cons (some replacement) .nil) (round payload ctx (ctx.roles 1)) Occurrence.iterations repeatSite).interpret project := by
  unfold denoteRepeatOn
  split
  · cases count with
    | none => rfl
    | some count =>
      dsimp only
      split
      · simp only [Finite.interpret_execute, callback_natural maximum ctx separate]
      · rfl
  · rfl

private theorem return_natural (ctx : ProtocolContext)
    (state : Values (Component (assignment F G)) repeatState) (handle : Nat) :
    ((returnProcess payload ctx (ctx.roles 1) state).interpret project).interpret (ScalarHandles.replace handle) =
    (returnProcess payload ctx (ctx.roles 1) state).interpret project := by
  unfold returnProcess
  simp only [PIR.Process.interpret_bind, PIR.Process.interpret]
  rw [owned (G := G)]

private theorem reduce_natural (maximum : Nat) (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (original replacement : Nat) (count : Option Nat) (point : Option (List F)) (claim : Option F) :
    ((reduce payload maximum ctx (ctx.roles 1) [] (verifierInputs (G := G) point claim count (some original))).interpret
      project).interpret (ScalarHandles.replace replacement) =
    (reduce payload maximum ctx (ctx.roles 1) [] (verifierInputs point claim count (some replacement))).interpret project := by
  unfold verifierInputs
  rw [reduce_verifier payload Generated.Bindings.TwoSumsSumcheck.helper_bodies _ _ separate,
    reduce_verifier payload Generated.Bindings.TwoSumsSumcheck.helper_bodies _ _ separate]
  simp only [PIR.Process.interpret_bind]
  rw [owned (G := G)]
  congr 1
  funext opened
  rw [repeat_natural maximum ctx separate]
  congr 1
  funext state
  exact return_natural ctx state replacement

/-- Full-return capability naturality of the exact source, including both
captured Reduce calls, absent inputs, every count, all replies and stops. -/
theorem participant_handle (left right : Option (List F)) (leftClaim rightClaim : Option F)
    (count : Option Nat) (original replacement : Nat) :
    (((Generated.Original.TwoSums.imported.program.participant F G 1
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim (.cons count (.cons (some original) .nil))))))).interpret
      CommonAdapter.project).interpret (ScalarHandles.replace replacement)) =
    (Generated.Original.TwoSums.imported.program.participant F G 1
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim (.cons count (.cons (some replacement) .nil))))))).interpret
      CommonAdapter.project := by
  have source (handle : Nat) :
      (Generated.Original.TwoSums.realized (G := G) left right leftClaim rightClaim count (some handle)).interpret project =
      (Generated.Original.TwoSums.imported.program.participant F G 1
        (.cons left (.cons right (.cons leftClaim (.cons rightClaim (.cons count (.cons (some handle) .nil))))))).interpret
          CommonAdapter.project := by
    rw [← Generated.Original.TwoSums.participant_binding]
    rw [← PIR.Process.interpret_comp]
    apply congrArg (PIR.Process.interpret CommonAdapter.project)
    exact (Occurrence.participant_erase (ringModel F G) Generated.Original.TwoSums.imported.program 1
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim (.cons count (.cons (some handle) .nil))))))).trans
      (Program.participant_eq_participantOn _ _ _).symm
  rw [← source original, ← source replacement]
  unfold Generated.Original.TwoSums.realized
  simp only [PIR.Process.interpret_bind]
  apply congrArg₂ PIR.Process.bind
  · exact owned _ _ _ _ replacement
  · funext pendingLeft
    apply congrArg₂ PIR.Process.bind
    · apply congrArg₂ PIR.Process.bind
      · exact reduce_natural Generated.Original.TwoSums.maximum0
          Generated.Original.TwoSums.firstContext (by decide) original replacement count _ _
      · funext result; rfl
    · funext reducedLeft
      apply congrArg₂ PIR.Process.bind
      · exact owned _ _ _ _ replacement
      · funext checkedLeft
        apply congrArg₂ PIR.Process.bind
        · exact owned _ _ _ _ replacement
        · funext pendingRight
          apply congrArg₂ PIR.Process.bind
          · apply congrArg₂ PIR.Process.bind
            · exact reduce_natural Generated.Original.TwoSums.maximum0
                Generated.Original.TwoSums.lastContext (by decide) original replacement count _ _
            · funext result; rfl
          · funext reducedRight
            apply congrArg₂ PIR.Process.bind
            · exact owned _ _ _ _ replacement
            · funext checkedRight
              exact helper_components _ _ replacement

end ZkcExamples.Construction.ComposedSumcheckSourceHandles
