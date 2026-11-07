module

public import ZkcArkLibExamples.Fri.CommitProbability
public import ZkcArkLibExamples.Fri.VerifierQueryProbability

@[expose] public section

/-! Proximity soundness of the original scalar FRI receiver with clear
publication and fresh interactive field and index requests. All bounds
are on the experiment's unconditional mass, including adaptive provers
that publish, change their auxiliary state, or abort between challenges. -/
set_option autoImplicit false
noncomputable section
namespace ZkcSecurity.ArkLib.Fri.InteractiveSoundness
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured OracleComp
open FriSource FriSourceBodies FriPhaseCalls
open ZkcSecurity.Domains.KoalaBear (Octic)
open ZkcSecurity.Domains.KoalaBearModel (model)
open CommitLoop (State)
open CommitReturn (Publication)
open CommitProbability (foldError SafeReturn)
open VerifierRoot (FirstWord FirstFar)
open FriLowDegreeCall (caller)
abbrev context := FriSourceCalls.commitment.childContext caller.context
abbrev queryError (δ : ℝ) := ENNReal.ofReal (1 - min (1/4 : ℝ) δ) ^ 8

variable {Aux E : Type} [SampleableType Octic]
  (ordinary : PublishedSampling.Network model Aux E) (service : Nat)
  (fieldAudit : PublishedWords.Table model → Octic → List E)
  (indexAudit : PublishedWords.Table model → Fin 32 → List E)
  (choose : PublishedWords.Chooser ProbComp model Aux E)

local notation "net" => CommitRoundProbability.sourceNetwork ordinary context service fieldAudit indexAudit
local notation "act" => CommitLoop.handler net choose
local notation "app" => SourceReturnBound.application checkedUnit.oracles (PublishedWords.liftM net)
  PublishedWords.readM (PublishedWords.publishM choose)

set_option maxRecDepth 6000 in
private theorem afterCommit (pub : Publication) (shift : Octic) (nz : shift ≠ 0) (δ : ℝ) (before : State Aux)
    (role : before.oracle.self = 1) (live : pub.rounds.Installed before.oracle shift)
    (position : pub.rounds.First [] before.oracle.provider.words)
    (safe : (toTrace 0 (RetainedDomain.domain shift nz) (pub.rounds.transcript pub.coefficients)).Safe (1/4)) :
    ReturnBound ((FriLowDegreeCall.afterCommit model 8 service (pub.output shift)).runM act before)
      (fun _ s ↦ ¬ FirstFar shift nz δ s.oracle) (queryError δ) := by
  by_cases far : Far (RetainedDomain.domain shift nz) 8 δ pub.word
  · refine (prEvent_mono _ _ (fun r ↦ Phases.returned (fun _ ↦ True) r) ?_).trans
      (VerifierQueryProbability.safeFar_le net choose pub shift nz δ service
        (CommitRoundProbability.freshPositions ordinary context service fieldAudit indexAudit choose) before role live safe far)
    intro record _
    cases eq : record.outcome <;> simp_all [violates, Phases.returned]
  · let next := FriLowDegreeCall.afterCommit model 8 service (pub.output shift)
    have frame := PublishedWords.process_frame checkedUnit.oracles net choose next before
    have law : PIR.Process.OnReturn act before next (fun _ s ↦ ¬ FirstFar shift nz δ s.oracle) := by
      apply frame.weaken
      intro record kept _ _ observed
      have first : FirstWord pub record.state.oracle := PublishedWords.PublishedAfter.first (position.transport kept)
      exact far ((first.far_iff shift nz δ).mp observed)
    exact (ReturnBound.ofOnReturn law).trans bot_le

set_option maxRecDepth 6000 in
private theorem program (shift : Octic) (nz : shift ≠ 0) (δ : ℝ) (before : State Aux)
    (role : before.oracle.self = 1) (empty : before.oracle.provider.words = []) :
    ReturnBound ((FriLowDegreeCall.program model shift 3 8 service).runM act before)
      (fun _ s ↦ ¬ FirstFar shift nz δ s.oracle) (foldError + queryError δ) := by
  unfold FriLowDegreeCall.program
  apply ReturnBound.processBind (post := fun out (s : State Aux) ↦ SafeReturn [] shift nz out s.oracle)
  · apply app before _ protocol0Signature FriSourceCalls.commitment.site _ (SafeReturn [] shift nz)
    intro entered same
    have paid := CommitProbability.installed ordinary context service fieldAudit indexAudit choose rfl (by decide)
      shift nz entered (same ▸ role)
    have initiallyEmpty : entered.oracle.provider.words = [] := same ▸ empty
    exact paid.weaken fun _ _ known ↦ by simpa only [initiallyEmpty] using known
  · rintro _ current ⟨pub, ⟨rfl, position, live, who⟩, safe⟩
    exact afterCommit ordinary service fieldAudit indexAudit choose pub shift nz δ current who live position safe

set_option maxRecDepth 6000 in
set_option maxHeartbeats 350000 in
private theorem verifierBound (shift : Octic) (nz : shift ≠ 0) (δ : ℝ) (auxiliary : Aux) :
    ReturnBound (A := Values (FriBinding.Value model) runSignature.outputs) (S := State Aux) (E := OracleProtocol.Event E)
      (FriSource.verifier (model := model) shift 3 8 service auxiliary net choose)
      (fun _ s ↦ ¬ FirstFar shift nz δ s.oracle) (foldError + queryError δ) := by
  let post := fun (_ : Values (FriBinding.Value model) runSignature.outputs) (s : State Aux) ↦ ¬ FirstFar shift nz δ s.oracle
  apply (congrArg (fun run : ProbComp (FriSource.Execution model Aux E) ↦ ReturnBound run post (foldError + queryError δ))
    (FriLowDegreeCall.verifier model shift 3 8 service auxiliary net choose)).mpr
  let initial := (start (model := model) 1 [] shift 3 8 service auxiliary).state
  let low := (FriLowDegreeCall.program model shift 3 8 service).bind fun values ↦
    .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) values)
  let called := (OracleProtocol.withMarks [(rootSite.site, rootSite.site)] (.done ())).bind fun _ ↦
    OracleProtocol.enter model (.application protocol5Signature rootSite.site) low
  have parent := app initial [(rootSite.site, rootSite.site)] protocol5Signature rootSite.site low
    (fun _ store ↦ ¬ FirstFar shift nz δ store) (foldError + queryError δ) (by
      intro entered same
      apply ReturnBound.beforeExact (first := FriLowDegreeCall.program model shift 3 8 service)
        (next := fun values ↦ .done (maskValues 1 (lowDegreeContext.mapScopes protocol5Signature.outputScopes) values))
        (goal := fun _ (s : State Aux) ↦ ¬ FirstFar shift nz δ s.oracle) (head := program ordinary service fieldAudit indexAudit choose shift nz δ entered (same ▸ rfl) (same ▸ rfl))
      intro _ _ valid
      exact PIR.Process.OnReturn.done valid)
  exact ReturnBound.beforeExact (handler := act) (before := initial) (first := called) (goal := post) (next := fun out ↦ .done (maskValues 1 runSignature.outputScopes (.cons (out.get .here) .nil)))
    parent (fun _ _ valid ↦ PIR.Process.OnReturn.done valid)

set_option maxRecDepth 6000 in
/-- The accepting/far event is evaluated on the final record of the original
verifier. The initial word is whichever word the first successful send chose.
The three folding errors and the eight-position term use one execution. -/
theorem soundness (shift : Octic) (nz : shift ≠ 0) (δ : ℝ) (auxiliary : Aux) :
    Pr{let record ← FriSource.verifier shift 3 8 service auxiliary net choose}[RetainedDomain.sourceEvent shift nz δ record] ≤
      (∑ r ∈ Finset.range 3, uniqueDecodingError Octic 5 r) + ENNReal.ofReal (1 - min (1/4 : ℝ) δ) ^ 8 := by
  refine (prEvent_mono (FriSource.verifier (model := model) shift 3 8 service auxiliary net choose) _ (violates (fun _ (s : State Aux) ↦ ¬ FirstFar shift nz δ s.oracle)) ?_).trans
    (verifierBound ordinary service fieldAudit indexAudit choose shift nz δ auxiliary)
  intro record event
  cases eq : record.outcome with
  | stopped => exact (RetainedDomain.sourceEvent_stopped eq event).elim
  | returned => simpa only [violates, eq, not_not] using (show FirstFar shift nz δ record.state.oracle from event.2)

end ZkcSecurity.ArkLib.Fri.InteractiveSoundness
