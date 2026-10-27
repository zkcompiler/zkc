module

public import Zkc.Construction.Uniform.OccurrenceSourceProcess
public import ZkcExamples.Structured.OriginalArtifacts.TwoSumsValidatorRoot

@[expose] public section

/-! Reached-source routing for the exact composed Sumcheck unit. This supplies
only effect and occurrence obligations; the compiled loops and complete ABI
are certified by the independently retained TwoSums validator certificate. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcExamples.Construction.ComposedSumcheckSourceRouting
open Zkc Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open Zkc.Construction.Uniform.OccurrenceSourceProcess
open Zkc.Construction.Uniform.LoopedSourceProcess
open ZkcExamples.Structured.SumcheckArtifacts.ArtifactBinding
namespace Retained
abbrev program := ZkcExamples.Structured.OriginalArtifacts.TwoSums.program
abbrev context := ZkcExamples.Structured.OriginalArtifacts.TwoSums.context
abbrev routing := ZkcExamples.Structured.OriginalArtifacts.TwoSums.routing
abbrev occurrence0 := ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0
abbrev occurrence1 := ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1
end Retained
open Retained
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

def closedTables (payload : UnitPayload) : Evaluation.ComponentTables F G closedInterface :=
  payload.definitions.foldl (Evaluation.ComponentTables.extend (.silent _)) ⟨[], []⟩

theorem closedTables_lift (payload : UnitPayload) :
    Evaluation.ComponentTables.Interprets
      (closedLift (I := Occurrence.signature (uniformCarriers F G))) (closedTables payload)
      (OriginalSumcheckLibrary.helpers payload) :=
  Evaluation.ComponentTables.fold_interpret _ (SiteObservations.silent_interpret _) (.empty _) payload.definitions

def helper_closed (handle : Nat) (frames : Original.Frames) (entry : Helper)
    (arguments : Values (assignment F G) entry.inputs) :
    Routed (routing handle) frames frames
      (invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) program.payload).closed entry arguments) := by
  rw [← (closedTables_lift program.payload).closed]
  exact Routed.closed frames _

def helper_components (handle : Nat) (frames : Original.Frames) (entry : Helper)
    (arguments : Values (Component (assignment F G)) entry.inputs) :
    Routed (routing handle) frames frames
      (invoke (OriginalSumcheckLibrary.helpers (F := F) (G := G) program.payload).components entry arguments) := by
  rw [← (closedTables_lift program.payload).components]
  exact Routed.closed frames _

/-- Four exact key equations, instantiated below at both reached call sites. -/
structure Keys (occurrence : Occurrence) (index : Nat) : Prop where
  low : Origin.withoutCoordinates (occurrence.origins context index).low =
    context.message (SumcheckVerifierLaws.lowSite occurrence.protocol) (occurrence.protocol.roles 0) context.validator
  high : Origin.withoutCoordinates (occurrence.origins context index).high =
    context.message (SumcheckVerifierLaws.highSite occurrence.protocol) (occurrence.protocol.roles 0) context.validator
  draw : Origin.withoutCoordinates (occurrence.origins context index).draw =
    context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr")
  delivery : Origin.withoutCoordinates (occurrence.origins context index).delivery =
    context.message (SumcheckVerifierLaws.deliverySite occurrence.protocol) context.validator (occurrence.protocol.roles 0)

theorem left_keys (index : Nat) : Keys occurrence0 index := by constructor <;> kernel_rfl
theorem right_keys (index : Nat) : Keys occurrence1 index := by constructor <;> kernel_rfl

def round (handle index : Nat) (occurrence : Occurrence)
    (routes : Routes (routing handle) occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩]
      handle (occurrence.origins context index))
    (keys : Keys occurrence index) (point : Option (List F)) (claim : Option F) :
    Routed (routing handle)
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩]
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩]
      ((SumcheckVerifierLaws.roundPlain (G := G) occurrence.protocol (some handle) (point, claim)).interpret
        OriginalSumcheckLibrary.actions) := by
  simp only [SumcheckVerifierLaws.roundPlain, PIR.Process.interpret,
    OriginalSumcheckLibrary.actions, Occurrence.actions, PIR.Process.bind]
  apply Routed.receive _ _ _ _ _ _ routes.low keys.low
  intro low
  apply Routed.receive _ _ _ _ _ _ routes.high keys.high
  intro high
  cases claim with
  | none => exact .halt _ _ _
  | some claim =>
      by_cases valid : claim = low + high
      · simp only [valid, ite_true, PIR.Process.interpret, Occurrence.actions, PIR.Process.bind]
        apply Routed.query _ _ _ _ _ _ routes.draw keys.draw
          (by rfl)
        intro challenge
        apply Routed.send _ _ _ _ _ _ _ routes.delivery keys.delivery
        cases point with
        | none => exact .halt _ _ _
        | some point => exact .done _ _
      · simp only [valid, ite_false, PIR.Process.interpret]
        exact .halt _ _ _

def callback (handle index : Nat) (occurrence : Occurrence)
    (separate : occurrence.protocol.roles 0 ≠ occurrence.protocol.roles 1)
    (routes : Routes (routing handle) occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩]
      handle (occurrence.origins context index))
    (keys : Keys occurrence index)
    (state : Values (Component (assignment F G)) SumcheckVerifierBodies.repeatState) :
    Routed (routing handle) [] []
      (Repeat.stepOn (carriers := uniformCarriers F G) (SumcheckVerifierBodies.repeatSpec 4)
        occurrence.protocol (occurrence.protocol.roles 1) (.cons (some handle) .nil)
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol (occurrence.protocol.roles 1))
        state index Occurrence.iterations SumcheckVerifierBodies.repeatSite) := by
  unfold Repeat.stepOn
  apply Routed.bind
  · apply Routed.within
    cases state with | cons a state => cases state with | cons b state =>
      cases state with | cons c state => cases state with | cons d state =>
        cases state with | cons point state => cases state with | cons claim state =>
          cases state
          have mask : maskValues (occurrence.protocol.roles 1)
              (occurrence.protocol.mapScopes (SumcheckVerifierBodies.repeatSpec 4).stateScopes)
              (.cons a (.cons b (.cons c (.cons d (.cons point (.cons claim .nil)))))) =
              SumcheckVerifierLaws.embedV (G := G) (point, claim) := by
            simp [maskValues, SumcheckVerifierBodies.repeatSpec, ProtocolContext.mapScopes,
              SumcheckVerifierLaws.embedV, SumcheckRoundNormalForms.verifierState,
              Participant.restrict, separate, Ne.symm separate]
          rw [mask, OriginalSumcheckLibrary.round_verifier program.payload
            ZkcExamples.Structured.OriginalArtifacts.TwoSums.verifier_bodies
            occurrence.protocol _ rfl separate]
          exact (round handle index occurrence routes keys point claim).bind fun result => .done _ _
  · intro result
    exact .done _ _

def reduce (handle count : Nat) (occurrence : Occurrence)
    (separate : occurrence.protocol.roles 0 ≠ occurrence.protocol.roles 1)
    (routes : ∀ index, Routes (routing handle) occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix SumcheckVerifierBodies.repeatSite, index⟩]
      handle (occurrence.origins context index))
    (keys : ∀ index, Keys occurrence index) (point : Option (List F)) (claim : Option F) :
    Routed (routing handle) [] []
      (OriginalSumcheckLibrary.reduce program.payload 4 occurrence.protocol
        (occurrence.protocol.roles 1) []
        (OriginalSumcheckLibrary.verifierInputs (G := G) point claim (some count) (some handle))) := by
  unfold OriginalSumcheckLibrary.verifierInputs
  rw [OriginalSumcheckLibrary.reduce_verifier program.payload
    ZkcExamples.Structured.OriginalArtifacts.TwoSums.verifier_bodies _ _ separate]
  apply Routed.bind
  · exact Routed.owned [] _ _ _ (helper_closed handle [] _) _
  · intro opened
    apply Routed.bind
    · have active : ((SumcheckVerifierBodies.repeatSpec 4).roles.map occurrence.protocol.roles).contains
          (occurrence.protocol.roles 1) = true := by simp []
      simp only [denoteRepeatOn, active, ↓reduceIte]
      split
      · exact Routed.finite _ (fun state index => callback handle index occurrence separate
          (routes index) (keys index) state) _ _
      · exact .halt _ _ _
    · intro state
      unfold OriginalSumcheckLibrary.returnProcess
      apply Routed.bind
      · exact Routed.owned [] _ _ _ (helper_closed handle [] _) _
      · intro returned
        exact .done _ _

def participant (left right : List F) (leftClaim rightClaim : F) (count handle : Nat) :
    Routed (routing handle) [] []
      (Occurrence.participant (ringModel F G) program 1
        (.cons (some left) (.cons (some right) (.cons (some leftClaim) (.cons (some rightClaim)
          (.cons (some count) (.cons (some handle) .nil))))))) := by
  rw [Generated.Original.TwoSums.participant_binding]
  unfold Generated.Original.TwoSums.realized Generated.Original.TwoSums.step0
    Generated.Original.TwoSums.step1Realized Generated.Original.TwoSums.step2
    Generated.Original.TwoSums.step3 Generated.Original.TwoSums.step4Realized
    Generated.Original.TwoSums.step5 Generated.Original.TwoSums.step6
    OriginalSumcheckCalls.realizeCall
  apply Routed.bind
  · exact Routed.owned [] _ _ _ (helper_closed handle [] _) _
  · intro pendingLeft
    apply Routed.bind
    · exact (reduce handle count occurrence0 (by decide)
        (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence0_routes handle)
        left_keys (pendingLeft.get .here) (pendingLeft.get (.there .here))).bind fun result => .done _ _
    · intro reducedLeft
      apply Routed.bind
      · exact Routed.owned [] _ _ _ (helper_closed handle [] _) _
      · intro checkedLeft
        apply Routed.bind
        · exact Routed.owned [] _ _ _ (helper_closed handle [] _) _
        · intro pendingRight
          apply Routed.bind
          · exact (reduce handle count occurrence1 (by decide)
              (ZkcExamples.Structured.OriginalArtifacts.TwoSums.occurrence1_routes handle)
              right_keys (pendingRight.get .here) (pendingRight.get (.there .here))).bind fun result => .done _ _
          · intro reducedRight
            apply Routed.bind
            · exact Routed.owned [] _ _ _ (helper_closed handle [] _) _
            · intro checkedRight
              exact helper_components handle [] _ _

end ZkcExamples.Construction.ComposedSumcheckSourceRouting
