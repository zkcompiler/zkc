module

public import ZkcSecurityExamples.Gkr.OccurrenceVerifier
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import ZkcExamples.Structured.GkrRoundsReading

@[expose] public section

/-! The current validator's layer Sumcheck retains its complete pending point,
actual indexed repeat boundaries, rejected checks, and every challenge reply. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalVerifier
open Zkc Source Structured
open ZkcExamples.Structured Generated.Presentations.Gkr.Root Generated.Presentations.Gkr.Rounds
open SumcheckVerifierHelpers HonestProducerSource HonestProducerOccurrences
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- One actual source round, with no projection of its actions. -/
theorem round_reads (ctx : ProtocolContext) (handle : Nat) (state : List F × F) :
    (Generated.Presentations.Gkr.Rounds.verifierProcess (F := F) (G := G) ctx (some handle) (some state.1)
      (some state.2)).interpret Occurrence.actions =
    (((GkrVerifier.round ctx handle state).interpret CommonAdapter.embed).interpret
      Occurrence.actions).bind (fun next => .done (some next.1, some next.2)) := by
  simp only [Generated.Presentations.Gkr.Rounds.verifierProcess, Evaluation.ComponentTables.toOn, Generated.Presentations.Gkr.payload,
    Generated.Presentations.Gkr.program, GkrSourceViews.program, GkrVerifier.round, GkrVerifier.roundFirst,
    GkrVerifier.roundSecond, GkrVerifier.roundCheck, PIR.Process.interpret,
    CommonAdapter.embed, Occurrence.actions, PIR.Process.bind, GkrRoundsReading.append_plain]
  refine congrArg (PIR.Process.call _) (funext fun c0 => congrArg (PIR.Process.call _) (funext fun c1 =>
    congrArg (PIR.Process.call _) (funext fun c2 => ?_)))
  split
  · simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions,
      PIR.Process.bind, GkrVerifier.roundChallenge]
    rfl
  · rfl

/-- The actual carried seven-tuple, capture, and callback remain inside each
source-selected round frame. -/
theorem rounds_repeat (ctx : ProtocolContext) (separate : ctx.roles 0 ≠ ctx.roles 1)
    (site : String) (handle count : Nat) (bounded : count ≤ 4) (state : List F × F) :
    denoteRepeatOn (carriers := uniformCarriers F G) roundSpec ctx (ctx.roles 1) (some count)
      (verifierState (some state.1) (some state.2)) (.cons (some handle) .nil)
      (fun args => roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
      Occurrence.iterations site =
      (validatorRounds ctx handle (qualifyProtocolSite ctx.applicationPrefix site) 0 count state).bind
        (fun next => .done (verifierState (some next.1) (some next.2))) := by
  have repeated := Zkc.Source.Structured.LoopPresentation.present (carriers := uniformCarriers F G) roundSpec ctx (ctx.roles 1) (by simp)
    (.cons (some handle) .nil)
    (fun args => roundBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers (ctx.roles 1) [] ctx Occurrence.iterations) args.get)
    Occurrence.iterations site
    (fun state : List F × F => verifierState (some state.1) (some state.2))
    (fun state => verifierState_masked ctx _ rfl _ _)
    (fun state _ => (((GkrVerifier.round ctx handle state).interpret CommonAdapter.embed).interpret
      Occurrence.actions)) (by
      intro state index
      erw [Generated.Presentations.Gkr.Rounds.round_occurrence (F := F) (G := G) ctx (ctx.roles 1) []
        (.cons (some index) ((verifierState (some state.1) (some state.2)).append (.cons (some handle) .nil))), Generated.Presentations.Gkr.Rounds.verifier_process ctx _ rfl (.ofSeparate separate (by decide)), PIR.Process.interpret_bind,
        round_reads, PIR.Process.bind_assoc]
      rfl) count bounded _ state (verifierState_masked ctx _ rfl _ _)
  rw [repeated]
  rw [Zkc.Source.Structured.LoopPresentation.foldCounted _
    (validatorRounds (G := G) ctx handle (qualifyProtocolSite ctx.applicationPrefix site))
    (fun _ _ => rfl) (fun _ _ _ => rfl)]

attribute [local irreducible] roundBody

/-- The actual eight-input invocation, including both source masks and the
pending-prefix reconstruction, is the complete observed round loop. -/
theorem rounds_reads (ctx : ProtocolContext) (zero : ctx.roles 0 = 0) (one : ctx.roles 1 = 1)
    (handle count : Nat) (bounded : count ≤ 4) (point : List F) (claim : F) :
    invokeProtocol (beforeRoot (F := F) (G := G)) GkrSourceBodies.roundsSignature ctx 1
      (.cons none (.cons none (.cons none (.cons none (.cons (some point)
        (.cons (some claim) (.cons (some count) (.cons (some handle) .nil)))))))) =
      (validatorRounds ctx handle (qualifyProtocolSite ctx.applicationPrefix "s9") 0 count ([], claim)).bind
        (fun result => .done (GkrRoundsReading.roundsResults (point ++ result.1, result.2))) := by
  have separate : ctx.roles 0 ≠ ctx.roles 1 := by rw [zero, one]; decide
  rw [rounds_body]
  have masked : maskValues 1 (ctx.mapScopes GkrSourceBodies.roundsSignature.inputScopes)
      ((.cons none (.cons none (.cons none (.cons none (.cons (some point)
        (.cons (some claim) (.cons (some count) (.cons (some handle) .nil)))))))) :
          Values (Component (assignment F G)) roundsInputs) =
      (.cons none (.cons none (.cons none (.cons none (.cons (some point)
        (.cons (some claim) (.cons (some count) (.cons (some handle) .nil)))))))) := by
    iterate 9 unfold maskValues
    simp [ProtocolContext.mapScopes, GkrSourceBodies.roundsSignature,
      Participant.restrict, zero, one]
  rw [masked]
  have normalized := verifierRounds_observed (F := F) (G := G) ctx
    (.ofSeparate separate (by decide)) [] (ProtocolPresentation.masked_empty (ringModel F G) _)
    (some point) (some claim) (some count) (some handle)
  dsimp only [NormalForm.runsAtOn, NormalForm.meaningAtOn] at normalized
  repeat rw [one] at normalized
  erw [normalized]
  simp only [verifierRoundsForm, NormalForm.Form.denoteOn, NormalForm.Form.denoteWithOn,
    NormalForm.Comps.eval, NormalForm.Comp.eval, NormalForm.Term.eval, NormalForm.Terms.eval,
    NormalForm.entryAt, NormalForm.firstEntry, NormalForm.laterEntries, Op.evalTotal, Values.get, Participant.owned, RoleFamily.sequence,
    ProtocolContext.roles, zero, one, PIR.Process.bind, PIR.Process.bind_assoc,
    Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program,
    OccurrencePresentation.closed_helper, GkrRoundsReading.tuple40_plain,
    PIR.Process.interpret, Values.present]
  have step := rounds_repeat (F := F) (G := G) ctx separate "s9" handle count bounded (point, claim)
  rw [one] at step
  erw [step, PIR.Process.bind_assoc]
  have pendingPrefix := validatorRounds_prefix (G := G) ctx handle
    (qualifyProtocolSite ctx.applicationPrefix "s9") 0 count point [] claim
  simp only [List.append_nil] at pendingPrefix
  rw [pendingPrefix, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext result
  cases result with | mk nextPoint nextClaim =>
    simp [Region.denote, participantMeaningWithOn, protocolOperationWithOn,
      SiteObservations.silent, Values.get, Operands.eval, Regions.denote,
      Environment.prepend, Environment.push, zero, one, Participant.owned,
      RoleFamily.sequence, PIR.Process.bind, PIR.Process.bind_assoc, PIR.Process.interpret,
      Values.absent, Values.present, Values.split, ProtocolOp.results, OccurrencePresentation.closed_helper,
      GkrRoundsReading.tuple49_plain, verifierState, maskValues, Participant.restrict,
      ProtocolContext.mapScopes, GkrSourceBodies.roundsSignature]
    rfl

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
