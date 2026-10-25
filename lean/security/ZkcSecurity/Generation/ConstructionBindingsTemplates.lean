module

@[expose] public section

/-! Installed Reduce callback proof templates. Adapted from the checked original
callback certificates. One schema per role is instantiated at source-derived
occurrences and SSA-derived captures; each emitted proof constructs a structural
simulation against the actual exported callback. No whole-root script is stored. -/
namespace ZkcSecurity.Generation.ConstructionBindingsTemplates

def validator : String :=
  r###"noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = $OFFSET) (index handle : Nat) (point : List F) (scalar : F)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (VerifierReturns (F := F) (G := G) context outputs
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩])
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle)
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol
          (occurrence.protocol.roles 1)
          (.cons (some index) ((SumcheckVerifierLaws.embedV (some point, some scalar)).append
            (.cons (some handle) .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      ($BODY (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" point),
          .data (.field "bls12-381.fr" scalar), .transcript context.suite history])) := by
  rw [original_round program.payload verifier_bodies
    (routing handle) occurrence.protocol (by decide +kernel) index handle
    (occurrence.origins context index) point scalar _ (routes handle index)]
  unfold_component_bodies [$BODY]
  derive_artifact_binding
    normalizing (
      try simp (disch := omega) only [List.append_assoc, List.getElem?_append_right, size]
      try normalize_artifact_operations
        [ZkcSecurity.Realizations.Sumcheck.DomainHelpers.append program helper_bodies.sumcheck]
        unfolding [verifier, Occurrence.origins, routing, occurrence, Occurrence.protocol,
          context, Original.queryField, OccurrenceResolution.atCoordinates_request,
          Context.message, Origin.message, Context.query, Origin.query, Domain.queryOrigin, Domain.templateOrigin,
          Template.origin, Template.repeats, Template.qualify, Template.applicationPrefix,
          ProtocolContext.enter, roleSubstitution, Context.role,
          SumcheckVerifierLaws.lowSite, SumcheckVerifierLaws.highSite,
          SumcheckVerifierLaws.challengeSite, SumcheckVerifierLaws.deliverySite]
      try simp (disch := omega) only [List.append_assoc, List.getElem?_append_right, size,
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
      List.getElem?_append_right, size]))
"###

def producer : String :=
  r###"noncomputable def round (captured : Domain.Environment (uniformCarriers F G))
    (size : captured.length = $OFFSET) (index handle : Nat)
    (raw : List F) (dimension width : Nat) (point : List F)
    (shape : PrimitiveLibrary.HasShape raw dimension width)
    (bounded : raw.length < indexLimit) (positive : 0 < dimension)
    (history : Domain.History (uniformCarriers F G)) :
    Original.Simulation
      (RoundReturns (F := F) (G := G) context outputs
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        raw dimension width point)
      (fun _ frame => Zkc.Construction.ArtifactBinding.Captures captured frame)
      (Original.fold (routing handle)
        (OriginalSumcheckLibrary.round program.payload occurrence.protocol
          (occurrence.protocol.roles 0)
          (.cons (some index) ((SumcheckProverLaws.embedP (raw, dimension, width, point)).append
            (.cons none .nil))))
        ⟨[⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩], history⟩)
      ($BODY (ringModel F G) program context
        (captured ++ [.data (.index index), .data (.vector "bls12-381.fr" raw),
          .data (.index dimension), .data (.index width),
          .data (.vector "bls12-381.fr" point), .transcript context.suite history])) := by
  rw [original_round program.payload helper_bodies.sumcheck
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

def producerRoutes : String :=
  r###"theorem routes (handle index : Nat) :
    Routes (routing handle) occurrence.protocol
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
      (occurrence.origins context index) := by
  constructor
  · rfl
  · exact ($VALIDATOR_ROUTES handle index).low
  · exact ($VALIDATOR_ROUTES handle index).high
  · have policy :
        (!(context.draws.map Prod.fst).Nodup || !(context.draws.map Prod.snd).Nodup) = false := by
      decide +kernel
    have candidates : (($DELIVERIES : List Original.Delivery).filter fun candidate =>
        Original.deliveryValid program.snapshot context
          candidate.draw candidate.message &&
        candidate.message.qualify (candidate.message.event[2]?.getD "") ==
          SumcheckVerifierLaws.deliverySite occurrence.protocol &&
        (context.draws.contains
          (candidate.draw.qualify (candidate.draw.event[2]?.getD ""),
            SumcheckVerifierLaws.deliverySite occurrence.protocol))) =
        [⟨occurrence.draw, occurrence.delivery⟩] := by
      decide +kernel
    have deliverySite : occurrence.delivery.qualify
        (occurrence.delivery.event[2]?.getD "") =
        SumcheckVerifierLaws.deliverySite occurrence.protocol := by decide +kernel
    have drawSite : occurrence.draw.qualify (occurrence.draw.event[2]?.getD "") =
        SumcheckVerifierLaws.challengeSite occurrence.protocol := by decide +kernel
    simp only [Original.Routing.delivery, show (routing handle).context = context from rfl,
      policy, Bool.false_eq_true, ↓reduceIte, candidates, deliverySite, drawSite]
    change ((OccurrenceResolution.resolve program.snapshot context
      (context.message (SumcheckVerifierLaws.deliverySite occurrence.protocol) 1 0)
      [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
      [occurrence.delivery]).bind fun message =>
      (OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol)
          (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw]).bind fun draw => some (draw, message)) = _
    have messageSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.message (SumcheckVerifierLaws.deliverySite occurrence.protocol) 1 0)
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.delivery] = some (occurrence.origins context index).delivery := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence,
        $VALID_DELIVERY]
      simp [occurrence, context, $OCCURRENCES,
        Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite, roleSubstitution,
        SumcheckVerifierLaws.deliverySite, Occurrence.origins, Context.message,
        Context.role, Origin.message, Domain.atCoordinates, decimal, decimalDigit]
    have drawSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw] = some (occurrence.origins context index).draw := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence, $VALID_DRAW]
      simp [occurrence, context, $OCCURRENCES,
        Occurrence.draw, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        SourceOccurrences.repeatSites, Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite, roleSubstitution,
        SumcheckVerifierLaws.challengeSite, Occurrence.origins, Context.query,
        Context.role, Origin.query, Domain.atCoordinates, decimal, decimalDigit]
    rw [messageSingleton, Option.bind_some, drawSingleton]
    rfl
  · exact Original.Routing.draw_request ($VALIDATOR_ROUTES handle index).draw
"###

end ZkcSecurity.Generation.ConstructionBindingsTemplates
