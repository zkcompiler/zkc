module

public import ZkcExamples.Structured.OriginalSumcheckLibrary

@[expose] public section

/-! The complete original Reduce body, with its observed repeat boundary. -/
set_option autoImplicit false
set_option maxRecDepth 10000
namespace ZkcExamples.Structured.OriginalSumcheckLibrary
open Zkc.Source Zkc.Source.Structured
open SumcheckVerifierBodies SumcheckVerifierHelpers

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def verifierInputs (claim : Option F) (count service : Option Nat) :
    Values (Component (assignment F G)) reduceInputs :=
  .cons none (.cons none (.cons none (.cons claim (.cons count (.cons service .nil)))))

def reduce (payload : UnitPayload) (maximum : Nat) (context : ProtocolContext) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) :
    RegionFunction (Component (assignment F G)) (signature (F := F) (G := G))
      (reduceInputs, reduceOutputs) :=
  fun args => (reduceBody maximum).denote
    (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
      self protocols context Occurrence.iterations) args.get

theorem width_lift (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (xs : Option (List F)) (dimension width : Option Nat) :
    invoke (helpers (F := F) (G := G) payload).components MapFirstBodies.widthHelper
      (.cons xs (.cons dimension (.cons width .nil))) = .done (.cons width .nil) := by
  rw [← (helpers_lift payload).components, width_optional payload bodies]
  rfl

theorem variables_lift (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (xs : Option (List F)) (dimension width : Option Nat) :
    invoke (helpers (F := F) (G := G) payload).components MapFirstBodies.variablesHelper
      (.cons xs (.cons dimension (.cons width .nil))) = .done (.cons dimension .nil) := by
  rw [← (helpers_lift payload).components, variables_optional payload bodies]
  rfl

theorem empty_lift (payload : UnitPayload) (bodies : Bodies payload.definitions) :
    invoke (helpers (F := F) (G := G) payload).closed SumcheckHelperBodies.emptyHelper .nil =
      .done (.cons [] .nil) := by
  rw [← (helpers_lift payload).closed, empty_plain payload bodies]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The entire verifier body reduces to the admitted repeat and actual return
permutation. Missing counts and services and excessive counts retain their
source behavior; no transcript event is invented for an unreached iteration. -/
theorem reduce_verifier (payload : UnitPayload) (bodies : Bodies payload.definitions)
    (maximum : Nat) (context : ProtocolContext) (separate : context.roles 0 ≠ context.roles 1)
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G)))
    (claim : Option F) (count service : Option Nat) :
    reduce payload maximum context (context.roles 1) protocols
      (.cons none (.cons none (.cons none (.cons claim (.cons count (.cons service .nil)))))) =
      (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec maximum) context
        (context.roles 1) count (SumcheckVerifierLaws.embedV (G := G) (some [], claim))
        (.cons service .nil) (round payload context (context.roles 1)) Occurrence.iterations "s15").bind
          (fun state => .done (reduceReturnValues state)) := by
  change (invoke (helpers (F := F) (G := G) payload).components MapFirstBodies.widthHelper
    (.cons none (.cons none (.cons none .nil)))).bind _ = _
  rw [width_lift payload bodies]
  dsimp only [PIR.Process.bind]
  change (((Participant.guard (services := services) (Value := assignment F G)
    (context.roles 1) (context.roles 0) none).interpret actions).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).bind _ = _
  simp only [Participant.guard, separate, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
  change (invoke (helpers (F := F) (G := G) payload).components MapFirstBodies.variablesHelper
    (.cons none (.cons none (.cons none .nil)))).bind _ = _
  rw [variables_lift payload bodies]
  dsimp only [PIR.Process.bind]
  change (Participant.owned (context.roles 1) (context.roles 0)
    (invoke (helpers (F := F) (G := G) payload).closed MapFirstBodies.lessHelper)
    (.cons none (.cons count .nil))).bind _ = _
  simp only [Participant.owned, separate, ↓reduceIte, PIR.Process.bind]
  change (((Participant.guard (services := services) (Value := assignment F G)
    (context.roles 1) (context.roles 0) none).interpret actions).bind
      (fun _ => .done (Values.nil : Values (Component (assignment F G)) []))).bind _ = _
  simp only [Participant.guard, separate, ↓reduceIte, PIR.Process.interpret, PIR.Process.bind]
  change (Participant.owned (context.roles 1) (context.roles 0)
    (invoke (helpers (F := F) (G := G) payload).closed SumcheckHelperBodies.emptyHelper)
    .nil).bind _ = _
  simp only [Participant.owned, separate, ↓reduceIte, PIR.Process.bind]
  change (Participant.owned (context.roles 1) (context.roles 1)
    (invoke (helpers (F := F) (G := G) payload).closed SumcheckHelperBodies.emptyHelper)
    .nil).bind _ = _
  simp only [Participant.owned, ↓reduceIte, RoleFamily.sequence, empty_lift payload bodies,
    PIR.Process.bind]
  change (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec maximum) context
    (context.roles 1) count (SumcheckVerifierLaws.embedV (G := G) (some [], claim))
    (.cons service .nil) (fun args => roundBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
        (context.roles 1) protocols context Occurrence.iterations) args.get)
    Occurrence.iterations "s15").bind _ = _
  simp only [round_on]
  congr 1
  funext state
  cases state with | cons a state => cases state with | cons b state =>
    cases state with | cons c state => cases state with | cons d state =>
      cases state with | cons e state => cases state with | cons f state =>
        cases state
        rfl

end ZkcExamples.Structured.OriginalSumcheckLibrary
