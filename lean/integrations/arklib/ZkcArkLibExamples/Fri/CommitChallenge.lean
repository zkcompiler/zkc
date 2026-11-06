module

public import ZkcArkLibExamples.Fri.CommitPublication
public import ZkcArkLibExamples.Fri.PublishedSampling
public import Zkc.Source.Structured.MarkedPublication

@[expose] public section

/-! The interactive fold challenge on the retained verifier. The sampler
receives the table installed before the draw, and has no opportunity to
change it between choosing a challenge and delivering that challenge. -/
set_option autoImplicit false
namespace ZkcSecurity.ArkLib.Fri.CommitChallenge
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured OracleComp
open FriSource (extension)
open FriCommitRound (drawRequest serviceSite)
open PublishedSampling (Network)
attribute [local implicit_reducible] FriCommitRound.drawRequest FriCommitRound.appendRequest
  OracleOp.arguments OracleOp.results
variable {model : DomainModel} {Aux E : Type} {snapshot : Snapshot}
  {domains : List DomainSpec} {math : OracleMathEnvironment}

/-- Install the verifier's field service at the source-selected Commit frame.
Use the scalar service for the later query phase. Delivery and receive retain
the network's independent state, events and failure behavior. -/
noncomputable def network [SampleableType (model.Field extension)]
    (ordinary : Network model Aux E) (context : ProtocolContext) (service : Nat)
    (fieldAudit : PublishedWords.Table model → model.Field extension → List E)
    (indexAudit : PublishedWords.Table model → Fin 32 → List E) : Network model Aux E :=
  PublishedSampling.withScalar (fun words op state ↦ match op with
    | .query loc (.draw domain) args =>
      if selected : domain = extension then
        if loc = serviceSite context 0 ∧ args.get .here = service then do
          let beta ← $ᵗ (model.Field extension)
          pure ⟨.returned (selected.symm ▸ beta), state, fieldAudit words beta⟩
        else pure ⟨.stopped .refused, state, []⟩
      else pure ⟨.stopped .refused, state, []⟩
    | op => ordinary words op state) service indexAudit

variable [SampleableType (model.Field extension)]
  (oracles : List (CheckedOracle snapshot domains math))
  (ordinary : Network model Aux E) (context : ProtocolContext) (service : Nat)
  (fieldAudit : PublishedWords.Table model → model.Field extension → List E)
  (indexAudit : PublishedWords.Table model → Fin 32 → List E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

noncomputable abbrev handler := PublishedWords.actionM oracles (network ordinary context service fieldAudit indexAudit) choose

/-- At the actual field request, the interactive verifier samples afresh,
and its observer sees exactly the current table. The provider and the source
cursor are unchanged. The equality retains the entire audit trace. -/
theorem draw (state : CommitPublication.State model snapshot domains math Aux) :
    handler oracles ordinary context service fieldAudit indexAudit choose (drawRequest context service) state = (do
      let beta ← $ᵗ (model.Field extension)
      pure ⟨.returned beta, state, (fieldAudit state.oracle.provider.words beta).map OracleProtocol.Event.ordinary⟩) := by
  unfold handler FriCommitRound.drawRequest
  rw [PublishedWords.actionM_ordinary]
  simp [network, PublishedSampling.withScalar, Values.get]

/-- The same experiment supplies the later eight scalar samples. Both
phases share the chooser, table and auxiliary state. -/
noncomputable def freshPositions : RetainedSampling.Fresh
    (handler oracles ordinary context service fieldAudit indexAudit choose) service := by
  unfold handler network
  apply PublishedSampling.fresh

/-- The configured verifier refuses a different handle even at the exact
source-selected field site. The network cannot answer that draw. -/
theorem wrongService (other : Nat) (different : other ≠ service)
    (state : CommitPublication.State model snapshot domains math Aux) :
    handler oracles ordinary context service fieldAudit indexAudit choose (drawRequest context other) state =
      pure ⟨.stopped .refused, state, []⟩ := by
  unfold handler FriCommitRound.drawRequest
  rw [PublishedWords.actionM_ordinary]
  simp [network, PublishedSampling.withScalar, Values.get, different]

variable {A : Type}

/-- Execute the original reply continuation with the sampled field and its recorded events. -/
noncomputable def sampleThen (words : PublishedWords.Table model)
    (current : CommitPublication.State model snapshot domains math Aux)
    (tail : model.Field extension → PIR.Process (OracleProtocol.Interface model) A) := do
  let beta ← $ᵗ (model.Field extension)
  let record := PIR.Execution.mk (.returned beta) current ((fieldAudit words beta).map OracleProtocol.Event.ordinary)
  record.followM fun answer ↦ (tail answer).runM
    (handler oracles ordinary context service fieldAudit indexAudit choose)

/-- A source mark may stop the execution. If it succeeds, the following
field sample observes the pre-mark word table even if the cursor moved. -/
private theorem markedDraw (marks : List (String × String))
    (tail : model.Field extension → PIR.Process (OracleProtocol.Interface model) A)
    (state : CommitPublication.State model snapshot domains math Aux) :
    let actions := handler oracles ordinary context service fieldAudit indexAudit choose
    (OracleProtocol.withMarks marks (.call (drawRequest context service) tail)).runM actions state =
      ((OracleProtocol.withMarks marks (.done ())).runM actions state >>= fun marked ↦
        marked.followM fun _ current ↦ sampleThen oracles ordinary context service fieldAudit indexAudit choose
          state.oracle.provider.words current tail) := by
  dsimp only
  apply OraclePublication.runMarked oracles (PublishedWords.liftM _) PublishedWords.readM (PublishedWords.publishM choose)
    marks (.call (drawRequest context service) tail) state _
  intro current kept
  let actions := handler oracles ordinary context service fieldAudit indexAudit choose
  change (actions (drawRequest context service) current >>= fun record ↦ record.followM fun beta ↦
    (tail beta).runM actions) = _
  refine (congrArg (fun run ↦ run >>= fun record ↦ PIR.Execution.followM record fun beta ↦
    (tail beta).runM actions) (draw oracles ordinary context service fieldAudit indexAudit choose current)).trans ?_
  simp only [sampleThen, bind_assoc, pure_bind, kept]
  rfl

open FriCommitRound (kind registrySite appendRequest iteration State beforeChallenge)
open OracleProtocol (AtMarkedCall withMarks concrete)

set_option maxHeartbeats 800000 in
/-- The source append of the round's returned handle is followed by an
independent field sample against the same installed table. The result is a
full execution equality for every suffix and every audit. Failed source
cursors skip the sample, and a returned sample is the next delivery's argument. -/
theorem installed (st : State model) (atService : st.service = service)
    (receiver : context.roles 1 = 1) (step : Nat) :
    ∃ sendMarks sent, iteration model context step st =
        withMarks sendMarks (.call (FriCommitRound.sendRequest context st.rows) sent) ∧
      ∀ anchor, ∃ appendMarks appended, ∃ (drawMarks : List (String × String))
        (sampled : model.Field extension → PIR.Process (OracleProtocol.Interface model)
          (Values (FriBinding.Value model) FriCommitRound.roundSite.spec.state)),
        sent (.cons (concrete model FriBinding.initialSort.type anchor) .nil) =
          withMarks appendMarks (.call (appendRequest context st.layers anchor) appended) ∧
        (∀ beta, AtMarkedCall (FriCommitRound.delivery context beta) (fun _ ↦ True) (sampled beta)) ∧
        ∀ current : CommitPublication.State model snapshot domains math Aux,
          current.oracle.self = 1 → st.layers.length < 3 →
          st.layers.all (OracleExecution.visibleReference current.oracle kind) = true →
          OracleExecution.visibleReference current.oracle kind anchor = true →
          let actions := handler oracles ordinary context service fieldAudit indexAudit choose
          (PIR.Process.call (appendRequest context st.layers anchor) appended).runM actions current =
            if (registrySite 1).definition = current.frame.definition ∧ (registrySite 1).row = current.frame.row then
              ((withMarks drawMarks (.done ())).runM actions current >>= fun marked ↦ marked.followM fun _ atDraw ↦
                sampleThen oracles ordinary context service fieldAudit indexAudit choose
                  current.oracle.provider.words atDraw sampled)
            else pure ⟨.stopped .refused, current, []⟩ := by
  subst service
  obtain ⟨sendMarks, sent, actual, after⟩ := beforeChallenge context receiver step st
  refine ⟨sendMarks, sent, actual, ?_⟩
  intro anchor
  obtain ⟨appendMarks, appended, app, drawNext⟩ := after anchor
  obtain ⟨drawMarks, sampled, sample, delivered⟩ := drawNext
  refine ⟨appendMarks, appended, drawMarks, sampled, app, delivered, ?_⟩
  intro current self room visible present
  have active : current.oracle.self ∈ ([0, 1] : List Nat).map context.roles := by simp [self, receiver]
  have law := OraclePublication.sequenceAppend oracles (PublishedWords.liftM (network ordinary context st.service
    fieldAudit indexAudit)) PublishedWords.readM (PublishedWords.publishM choose) kind 3 [0, 1] context.roles
    (registrySite 1) current 1 self.symm st.layers anchor active room (by decide) visible present
  dsimp only
  rw [PIR.Process.runM]
  change handler oracles ordinary context st.service fieldAudit indexAudit choose
    (appendRequest context st.layers anchor) current = _ at law
  refine (congrArg (fun run ↦ run >>= fun record ↦ PIR.Execution.followM record fun reply ↦
    (appended reply).runM (handler oracles ordinary context st.service fieldAudit indexAudit choose)) law).trans ?_
  rw [pure_bind]
  unfold OraclePublication.cursorReply
  split
  · simp only [PIR.Execution.followM, List.nil_append, sample]
    have derived := markedDraw oracles ordinary context st.service fieldAudit indexAudit choose drawMarks sampled current
    with_unfolding_all simpa [PIR.Execution.followM] using derived
  · rfl

end ZkcSecurity.ArkLib.Fri.CommitChallenge
