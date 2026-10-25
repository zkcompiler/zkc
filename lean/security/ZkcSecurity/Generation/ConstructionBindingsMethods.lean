module

@[expose] public section

namespace ZkcSecurity.Generation.ConstructionBindings

/-- Explicit proof construction, independent of source semantics or admission.
Shared templates cover their installed layout; checked derivation constructs a
full simulation for the selected actual body without a template fallback. -/
inductive ProofMethod where
  | sharedTemplate
  | checkedDerivation
  deriving DecidableEq, Inhabited

end ZkcSecurity.Generation.ConstructionBindings

/-! Generic callback proof emission using the existing checked derivation tactic.
Only proof bodies live here. The fixed statements and instance assembly are shared
with the template method. New layouts must still elaborate and kernel-check. -/
namespace ZkcSecurity.Generation.ConstructionBindingsMethods

def validatorProof : String :=
  r###"  rw [original_round program.payload verifier_bodies
    (routing handle) occurrence.protocol (by decide +kernel) index handle
    (occurrence.origins context index) point scalar _ (routes handle index)]
  unfold_component_bodies [$BODY]
  derive_artifact_binding
    normalizing (
      try simp (disch := omega) only [List.append_assoc, List.getElem?_append_right, size]
      try normalize_artifact_operations
        [ZkcSecurity.Realizations.Sumcheck.DomainHelpers.append program helper_bodies.sumcheck,
          $ORIGINS.low, $ORIGINS.high, $ORIGINS.draw, $ORIGINS.delivery]
        unfolding [verifier, Original.queryField, Occurrence.origins,
          OccurrenceResolution.atCoordinates_request, Context.message, Origin.message,
          Context.query, Origin.query, Request.draw]
      try simp (disch := omega) only [PIR.Process.bind, List.append_assoc,
        List.cons_append, List.nil_append, List.getElem?_append_right, size,
        List.getElem?_cons_zero, List.getElem?_cons_succ])
    solving (first
      | solve | simp [Zkc.Construction.ArtifactBinding.Captures, List.append_assoc]
      | (unfold VerifierReturns
         refine ⟨_, _, rfl, ?_⟩
         simp (disch := omega) [outputs, Original.ValuesHolds,
      Original.ComponentHolds, SumcheckVerifierBodies.repeatState, Values.get, Option.bind,
      List.getElem?_cons_zero, List.getElem?_cons_succ,
      Domain.Value.decode, Domain.Payload.value,
      SumcheckVerifierLaws.embedV, SumcheckRoundNormalForms.verifierState,
      Zkc.Construction.ArtifactBinding.Captures, List.append_assoc,
      List.getElem?_append_right, size, occurrence, Occurrence.origins,
      $ORIGIN_DEFINITIONS]))
"###

def producerProof : String :=
  r###"  rw [original_round program.payload helper_bodies.sumcheck
    (routing handle) occurrence.protocol (by decide +kernel) index none
    (occurrence.origins context index) raw dimension width point shape bounded positive _
    (routes handle index)]
  have sumsEq := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.sums (F := F) (G := G) program helper_bodies.sumcheck
    raw dimension width (lt_trans shape.2.1 (by decide +kernel)) positive
    (shape.split_valid positive)
  have firstEq (challenge : F) := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.first (F := F) (G := G)
    program helper_bodies.sumcheck raw dimension width challenge shape bounded positive
  have appendEq := ZkcSecurity.Realizations.Sumcheck.DomainHelpers.append (F := F) (G := G) program helper_bodies.sumcheck
  unfold_component_bodies [$BODY]
  derive_artifact_binding
    normalizing (
      try simp (disch := omega) only [List.append_assoc, List.getElem?_append_right, size]
      try normalize_artifact_operations
        [sumsEq, firstEq, appendEq]
        unfolding [producer, Occurrence.origins, routing,
          occurrence, Occurrence.protocol,
          context, Original.queryField,
          OccurrenceResolution.atCoordinates_request,
          Context.message, Origin.message, Context.query, Origin.query,
          Domain.queryOrigin, Domain.templateOrigin,
          Template.origin, Template.repeats, Template.qualify, Template.applicationPrefix,
          ProtocolContext.enter, roleSubstitution, Context.role,
          SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite,
          SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite]
      try simp (disch := omega) only [List.append_assoc, List.getElem?_append_right, size,
        List.getElem?_cons_zero, List.getElem?_cons_succ]
      try dsimp only
      change Original.Simulation _ _ _ _)
    solving (first
      | solve | simp [Zkc.Construction.ArtifactBinding.Captures, List.append_assoc]
      | (unfold RoundReturns
         constructor
         · unfold ZkcSecurity.Realizations.Sumcheck.OriginalProducer.Returns
           refine ⟨_, _, _, _, rfl, ?_⟩
           simp (disch := omega) [outputs, SumcheckProverLaws.embedP,
             Zkc.Construction.ArtifactBinding.Captures, List.append_assoc,
             List.getElem?_append_right, size,
             List.getElem?_cons_zero, List.getElem?_cons_succ]
         · exact ⟨_, rfl⟩))
"###

end ZkcSecurity.Generation.ConstructionBindingsMethods
