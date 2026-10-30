module

public import Zkc.Protocols.Sumcheck.Source.Reduce
public import ZkcExamples.Structured.Generated.Original.SmallSumcheck
public import ZkcExamples.Structured.Generated.Original.TwoSums
public import ZkcExamples.Structured.Generated.Bindings.SmallSumcheckSumcheck
public import ZkcExamples.Structured.Generated.Bindings.TwoSumsSumcheck

@[expose] public section

/-! Exact admitted-original instances of the one Reduce library body. Source
declaration identity and complete typed body are checked separately from the
mathematical callback laws. Both TwoSums occurrences use the same declaration. -/
set_option autoImplicit false
set_option maxRecDepth 10000
noncomputable section
namespace ZkcExamples.Structured.OriginalSumcheckInstances
open Zkc.Source Zkc.Source.Structured
open OriginalSumcheckLibrary SumcheckVerifierBodies

namespace Small
abbrev imported := Generated.Original.SmallSumcheck.imported
abbrev payload := imported.program.payload
abbrev reduceDefinition := Generated.Original.SmallSumcheck.reduceDefinition
abbrev rootDefinition := Generated.Original.SmallSumcheck.root
abbrev helpers_bound := Generated.Bindings.SmallSumcheckSumcheck.helper_bodies

theorem reduce_member : reduceDefinition ∈ payload.protocols :=
  Generated.Original.SmallSumcheck.sourceProtocol0_member

theorem reduce_body : reduceDefinition.body = reduceBody Generated.Original.SmallSumcheck.maximum := Generated.Original.SmallSumcheck.sourceProtocol0_body

def context : ProtocolContext := Generated.Original.SmallSumcheck.firstContext

theorem distinct : context.roles 0 ≠ context.roles 1 := by decide

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Exact full-signature lookup in the occurrence-aware original table. The
Reduce closure captures its actual earlier protocol prefix (empty here). -/
theorem reduce_lookup (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) reduceDefinition.inputs) :
    invokeProtocol (Occurrence.table (ringModel F G) payload) reduceDefinition.signature context self args =
      reduceDefinition.denoteWithOn (ringModel F G) (.silent _) actions
        (helpers payload).toOn [] Occurrence.iterations context self args :=
  Generated.Original.SmallSumcheck.reduce_lookup context self args

/-- The whole original body at the actual source call prefix, including its
missing-input and loop-admission behavior and the full returned tuple. -/
theorem verifier (point : Option (List F)) (claim : Option F) (count service : Option Nat)
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) :
    reduceDefinition.body.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
        (context.roles 1) protocols context Occurrence.iterations)
      (verifierInputs (G := G) point claim count service).get =
      (Participant.owned (context.roles 1) (context.roles 1)
        (invoke (helpers payload).closed SumcheckPendingBodies.openClaimHelper)
        (.cons point (.cons claim .nil))).bind fun opened =>
      (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec Generated.Original.SmallSumcheck.maximum) context (context.roles 1)
        count (SumcheckVerifierLaws.embedV (G := G) (opened.get .here, opened.get (.there .here))) (.cons service .nil)
        (round payload context (context.roles 1)) Occurrence.iterations repeatSite).bind
          (returnProcess payload context (context.roles 1)) := by
  rw [reduce_body]
  exact reduce_verifier payload helpers_bound Generated.Original.SmallSumcheck.maximum context distinct protocols point claim count service
end Small

namespace Two
abbrev imported := Generated.Original.TwoSums.imported
abbrev payload := imported.program.payload
abbrev reduceDefinition := Generated.Original.TwoSums.reduceDefinition
abbrev rootDefinition := Generated.Original.TwoSums.root
abbrev helpers_bound := Generated.Bindings.TwoSumsSumcheck.helper_bodies

theorem reduce_member : reduceDefinition ∈ payload.protocols :=
  Generated.Original.TwoSums.sourceProtocol0_member

theorem reduce_body : reduceDefinition.body = reduceBody Generated.Original.TwoSums.maximum := Generated.Original.TwoSums.sourceProtocol0_body

def leftContext : ProtocolContext := Generated.Original.TwoSums.firstContext
def rightContext : ProtocolContext := Generated.Original.TwoSums.lastContext

theorem left_distinct : leftContext.roles 0 ≠ leftContext.roles 1 := by decide
theorem right_distinct : rightContext.roles 0 ≠ rightContext.roles 1 := by decide
theorem contexts_differ : leftContext.applicationPrefix ≠ rightContext.applicationPrefix := by decide

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

/-- Exact full-signature lookup in the occurrence-aware original table. The
Reduce closure captures its actual earlier protocol prefix (empty here). -/
theorem reduce_lookup (context : ProtocolContext) (self : Nat)
    (args : Values (Component (assignment F G)) reduceDefinition.inputs) :
    invokeProtocol (Occurrence.table (ringModel F G) payload) reduceDefinition.signature context self args =
      reduceDefinition.denoteWithOn (ringModel F G) (.silent _) actions
        (helpers payload).toOn [] Occurrence.iterations context self args :=
  Generated.Original.TwoSums.reduce_lookup context self args

theorem verifier (context : ProtocolContext) (distinct : context.roles 0 ≠ context.roles 1)
    (point : Option (List F)) (claim : Option F) (count service : Option Nat)
    (protocols : ProtocolTable (assignment F G) (signature (F := F) (G := G))) :
    reduceDefinition.body.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) actions (helpers payload).toOn
        (context.roles 1) protocols context Occurrence.iterations)
      (verifierInputs (G := G) point claim count service).get =
      (Participant.owned (context.roles 1) (context.roles 1)
        (invoke (helpers payload).closed SumcheckPendingBodies.openClaimHelper)
        (.cons point (.cons claim .nil))).bind fun opened =>
      (denoteRepeatOn (carriers := uniformCarriers F G) (repeatSpec Generated.Original.TwoSums.maximum) context (context.roles 1)
        count (SumcheckVerifierLaws.embedV (G := G) (opened.get .here, opened.get (.there .here))) (.cons service .nil)
        (round payload context (context.roles 1)) Occurrence.iterations repeatSite).bind
          (returnProcess payload context (context.roles 1)) := by
  rw [reduce_body]
  exact reduce_verifier payload helpers_bound Generated.Original.TwoSums.maximum context distinct protocols point claim count service

abbrev left_verifier := @verifier F G _ _ _ _ _ leftContext left_distinct
abbrev right_verifier := @verifier F G _ _ _ _ _ rightContext right_distinct
end Two

end ZkcExamples.Structured.OriginalSumcheckInstances
