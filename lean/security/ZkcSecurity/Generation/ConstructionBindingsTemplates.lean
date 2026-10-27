module

public import ZkcSecurity.Generation.ConstructionBindingsMethods

@[expose] public section

/-! Fixed full callback statements and shared proof applications. Explicit checked
derivation supplies only an alternative proof body. Both methods bind the same
actual View, source process, captures and complete output interface. -/
namespace ZkcSecurity.Generation.ConstructionBindingsTemplates

def validatorStatement : String :=
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
"###

def sharedValidatorProof : String :=
  r###"  rw [body_instance, output_instance]
  exact ZkcExamples.Structured.SumcheckArtifacts.ArtifactBindingTemplates.validatorRound
    program helper_bodies.sumcheck verifier_bodies (routing handle) context rfl occurrence
    (by decide +kernel) $ORIGINS $OFFSET captured size index handle point scalar history
    (routes handle index)
"###

def validator (method : ConstructionBindings.ProofMethod := .sharedTemplate) : String :=
  validatorStatement ++ match method with
  | .sharedTemplate => sharedValidatorProof
  | .checkedDerivation => ConstructionBindingsMethods.validatorProof

def producerStatement : String :=
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
"###

def sharedProducerProof : String :=
  r###"  rw [body_instance, output_instance]
  exact ZkcExamples.Structured.SumcheckArtifacts.OriginalProducerTemplates.producerRound
    program helper_bodies.sumcheck (routing handle) context rfl occurrence
    (by decide +kernel) $ORIGINS $OFFSET captured size index raw dimension width point
    shape bounded positive history (routes handle index)
"###

def producer (method : ConstructionBindings.ProofMethod := .sharedTemplate) : String :=
  producerStatement ++ match method with
  | .sharedTemplate => sharedProducerProof
  | .checkedDerivation => ConstructionBindingsMethods.producerProof

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
    have drawSite : occurrence.draw.qualify (occurrence.draw.event[2]?.getD "") =
        SumcheckVerifierLaws.challengeSite occurrence.protocol := by decide +kernel
    simp only [Original.Routing.delivery,
      policy, Bool.false_eq_true, ↓reduceIte, candidates, drawSite]
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
      simp [$OCCURRENCE_DECIMAL,
        Occurrence.delivery, Occurrence.message, Occurrence.steps, Occurrence.protocol,
        Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite,
        SumcheckVerifierLaws.deliverySite, Occurrence.origins, Context.message,
        Context.role, Origin.message, Domain.atCoordinates]
      kernel_rfl
    have drawSingleton : OccurrenceResolution.resolve program.snapshot context
        (context.query (SumcheckVerifierLaws.challengeSite occurrence.protocol) (.draw "bls12-381.fr"))
        [⟨qualifyProtocolSite occurrence.protocol.applicationPrefix "s15", index⟩]
        [occurrence.draw] = some (occurrence.origins context index).draw := by
      simp only [OccurrenceResolution.resolve, List.filter_cons, List.filter_nil,
        OccurrenceResolution.matchesOccurrence, $VALID_DRAW]
      simp [$OCCURRENCE_DECIMAL,
        Occurrence.draw, Occurrence.steps, Occurrence.protocol,
        Template.origin, Domain.templateOrigin,
        Template.repeats, Template.qualify, Template.applicationPrefix,
        ProtocolContext.enter, qualifyProtocolSite,
        SumcheckVerifierLaws.challengeSite, Occurrence.origins, Context.query,
        Context.role, Origin.query, Domain.atCoordinates, decimal, decimalDigit, Request.draw]
      kernel_rfl
    rw [messageSingleton, Option.bind_some, drawSingleton]
    rfl
  · exact Original.Routing.draw_request ($VALIDATOR_ROUTES handle index).draw
"###

end ZkcSecurity.Generation.ConstructionBindingsTemplates
