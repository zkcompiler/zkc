module

public import ZkcSecurityExamples.Gkr.CanonicalVerifierLayer
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import ZkcSecurityExamples.Gkr.CanonicalVerifierOutput
public import Zkc.Source.Structured.OccurrenceYields

@[expose] public section

/-! The actual current validator equals the full observed mathematical verifier.
Admission concerns only the independently specified circuit shape and bounds.
The equation retains every source-selected frame, action, reply and refusal. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalVerifier
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured Generated.Presentations.Gkr.Root SumcheckVerifierHelpers
open HonestProducerSource HonestProducerOccurrences HonestProducerObserved
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev captures (encoding : CircuitEncoding F) (handle : Nat) :
    Values (Component (assignment F G)) layerSpec.captures :=
  (SourceRows.LayerCaptures.pack {
      «inputs» := some encoding.inputs,
      add := some encoding.add,
      mul := some encoding.mul,
      layers := some encoding.layers,
      selector := some encoding.selector,
      width := some encoding.width,
      service := some handle
    })

abbrev callback : RegionFunction (Component (assignment F G))
    (Occurrence.signature (uniformCarriers F G))
    (.index :: (layerSpec.state ++ layerSpec.captures), layerSpec.state) :=
  fun args => layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
    Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem layer_yields (encoding : CircuitEncoding F) (handle : Nat) (state : Nat × List F × F) :
    PIR.Yields (fun next : Nat × List F × F =>
      next.1 = state.1 + 1 ∧ next.2.1.length = encoding.width)
      (HonestProducerObservedLayers.validatorLayer (G := G) {} handle encoding.width currentLayerSites
        encoding.circuit.add encoding.circuit.mul state) := by
  apply erased_yields
  rw [HonestProducerObservedLayers.validatorLayer_erase]
  exact (GkrLayerReading.layerStep_yields (G := G) handle encoding.width
    encoding.circuit.add encoding.circuit.mul state).interpret CommonAdapter.embed

theorem layers_fold (encoding : CircuitEncoding F) («outputs» : List F)
    (admitted : encoding.Admitted 4 4 «outputs») (handle index count : Nat)
    (inside : index + count ≤ encoding.layers) (point : List F) (claim : F)
    (pointSize : point.length = encoding.width) :
    Finite.fold (fun state index => Repeat.stepOn layerSpec {} 1 (captures encoding handle)
      (callback (F := F) (G := G)) state index Occurrence.iterations (layerSite.site))
      (List.range' index count) (verifierLayerState (some point) (some claim)) =
    (validatorLayers {} handle currentSites encoding index count (index, point, claim)).bind
      (fun result => .done (verifierLayerState (some result.2.1) (some result.2.2))) := by
  have translated := Zkc.Source.Structured.LoopPresentation.foldInvariant
    (fun state index => Repeat.stepOn layerSpec {} 1 (captures encoding handle)
      (callback (F := F) (G := G)) state index Occurrence.iterations (layerSite.site))
    (fun state index => Occurrence.iterations.within (layerSite.site) index
      (HonestProducerObservedLayers.validatorLayer (G := G) {} handle encoding.width
        currentLayerSites encoding.circuit.add encoding.circuit.mul state))
    (fun (_ : Nat) (state : Nat × List F × F) => verifierLayerState (some state.2.1) (some state.2.2))
    (fun index state => state.1 = index ∧ state.2.1.length = encoding.width) encoding.layers
    (by
      rintro index ⟨offset, point, claim⟩ inside ⟨same, sized⟩
      dsimp only at same
      subst offset
      simp only [Repeat.stepOn, verifierLayerState_masked {} 1 rfl, callback]
      have equation := layer_reads (G := G) encoding «outputs» admitted handle index inside point claim sized
      dsimp only [SourceRows.LayerArguments.pack] at equation
      simp only [captures, SourceRows.LayerCaptures.pack, verifierLayerState, Values.append]
      rw [equation]
      simp only [IterationObservations.within_eq, PIR.Process.bind_assoc, PIR.Process.bind,
        qualifyProtocolSite, verifierLayerState_masked {} 1 rfl]
      rfl)
    (by
      intro index state _ valid
      apply Zkc.Source.Structured.OccurrenceYields.within
      exact (layer_yields encoding handle state).mono fun next related =>
        ⟨by omega, related.2⟩)
    index count inside (index, point, claim) ⟨rfl, pointSize⟩
  rw [translated]
  rfl

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem output_yields (handle count : Nat) :
    PIR.Yields (fun point : List F => point.length = count)
      (validatorOutput (G := G) {} handle (outputSite.site) 0 count []) := by
  apply erased_yields
  rw [validatorOutput_erase]
  have yields := PIR.Yields.repeatN
    (invariant := fun index (point : List F) => point.length = index)
    (step := GkrVerifier.outputRound (G := G) {} handle)
    (fun index point size => (GkrLayerReading.outputRound_yields {} handle point).mono
      fun next advanced => by omega) count 0 [] rfl
  simpa only [Nat.zero_add] using yields.interpret CommonAdapter.embed

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem layers_yields (encoding : CircuitEncoding F) (handle count : Nat)
    (point : List F) (claim : F) (pointSize : point.length = encoding.width) :
    PIR.Yields (fun next : Nat × List F × F => next.2.1.length = encoding.width)
      (validatorLayers (G := G) {} handle currentSites encoding 0 count (0, point, claim)) := by
  apply erased_yields
  rw [validatorLayers_erase]
  exact (PIR.Yields.repeatN
    (invariant := fun _ (state : Nat × List F × F) => state.2.1.length = encoding.width)
    (step := GkrVerifier.layerStep {} handle encoding.width encoding.circuit.add encoding.circuit.mul)
    (fun _ state _ => (GkrLayerReading.layerStep_yields (G := G) handle encoding.width
      encoding.circuit.add encoding.circuit.mul state).mono fun _ related => related.2)
    count 0 (0, point, claim) pointSize).interpret CommonAdapter.embed

/-- Full current-source validator reading, without a helper, transcript or
representation premise and without erasing nominal occurrence boundaries. -/
theorem reads (encoding : CircuitEncoding F) («outputs» : List F)
    (admitted : encoding.Admitted 4 4 «outputs») (handle : Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 1
      (SourceRows.Inputs.pack {
          «inputs» := some encoding.inputs,
          «outputs» := some «outputs»,
          add := some encoding.add,
          mul := some encoding.mul,
          layers := some encoding.layers,
          selector := some encoding.selector,
          width := some encoding.width,
          service := some handle
        }) =
    (validator {} handle currentSites encoding «outputs»).bind
      (fun accepted => .done ((SourceRows.Decision.pack { accepted := accepted }))) := by
  have shape := admitted.1
  have widthBound := admitted.2.2.1
  have layersBound := admitted.2.2.2.1
  have dimensions := admitted.2.2.2.2
  have widthDimension : encoding.width < 64 := by omega
  have selectorSmall : encoding.selector < 64 := by omega
  have indexBound (value : Nat) (small : value < 64) : value < indexLimit :=
    lt_trans small (by decide)
  have powerBound (exponent : Nat) (small : exponent < 64) : 2 ^ exponent < indexLimit :=
    Nat.pow_lt_pow_right (by decide) small
  have addShape : encoding.add.length = 2 ^ (encoding.selector + encoding.width + encoding.width + encoding.width) := by
    simpa only [← Nat.pow_add, Nat.add_assoc] using shape.2.1
  have mulShape : encoding.mul.length = 2 ^ (encoding.selector + encoding.width + encoding.width + encoding.width) := by
    simpa only [← Nat.pow_add, Nat.add_assoc] using shape.2.2.1
  rw [participant_body]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.gkrDefinition.body_eq_of_raw _ gkrBody_raw]
  change (gkrBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
    Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations)
    (SourceRows.Inputs.pack {
        «inputs» := some encoding.inputs,
        «outputs» := some «outputs»,
        add := some encoding.add,
        mul := some encoding.mul,
        layers := some encoding.layers,
        selector := some encoding.selector,
        width := some encoding.width,
        service := some handle
      }).get).bind
      (fun result => .done (maskValues 1 [[1]] result)) = _
  have masked (result : Values (Component (assignment F G)) [.boolean]) :
      maskValues 1 [[1]] result = result := by
    cases result with | cons value rest => cases rest; rfl
  simp only [masked, PIR.Process.bind_done]
  have normalized := rootPresentation_equation (F := F) (G := G) {} (.root _ _)
    beforeRoot beforeRoot_masked (some encoding.inputs) (some «outputs») (some encoding.add)
    (some encoding.mul) (some encoding.layers) (some encoding.selector) (some encoding.width) (some handle)
  erw [normalized]
  dsimp only [rootPresentation, rootPresentation_certificate, NormalForm.runsAtOn, NormalForm.meaningAtOn]
  unfold validator
  simp only [Generated.Presentations.Gkr.payload, Generated.Presentations.Gkr.program, GkrSourceViews.program]
  simp [OccurrencePresentation.closed_helper, GkrSourceAdmission.comparison_plain,
    GkrSourceAdmission.shape_plain_values, GkrSourceAdmission.index_add_plain,
    GkrSourceAdmission.power_plain, PrimitiveLibrary.boolResult,
    show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    widthDimension, selectorSmall, dimensions, shape.1, admitted.2.1, addShape, mulShape,
    indexBound encoding.width widthDimension, indexBound encoding.layers (by omega),
    indexBound encoding.selector selectorSmall,
    indexBound (encoding.selector + encoding.width) (by omega),
    indexBound (encoding.selector + encoding.width + encoding.width) (by omega),
    indexBound (encoding.selector + encoding.width + encoding.width + encoding.width) dimensions,
    powerBound encoding.width widthDimension, powerBound encoding.selector selectorSmall,
    powerBound (encoding.selector + encoding.width + encoding.width + encoding.width) dimensions,
    show ¬ 4 < encoding.width by omega, show ¬ 4 < encoding.layers by omega,
    Nat.not_lt.mpr shape.2.2.2,
    PIR.Process.interpret, PIR.Process.bind, Values.get]
  erw [GkrRoundsReading.empty_plain]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  erw [output_protocols]
  erw [output_repeat (F := F) (G := G) ({} : ProtocolContext) (by decide) (outputSite.site)
    handle encoding.width admitted.2.2.1 [], PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, verifierOutputState, Values.get]
  rw [PIR.Process.bind_assoc]
  apply (output_yields (G := G) handle encoding.width).bind_congr
  intro point pointSize
  have small : encoding.width < 64 := by have := admitted.2.2.1; omega
  have outputBound : «outputs».length < indexLimit := by
    rw [admitted.2.1]; exact Nat.pow_lt_pow_right (by decide) small
  erw [GkrLayerReading.evaluate_plain encoding.width «outputs» point
    ((ofList? encoding.width «outputs»).getD 0) (CircuitEncoding.decode_getD «outputs» admitted.2.1)
    pointSize small outputBound]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get, OccurrencePresentation.closed_helper, GkrLayerReading.tuple19_plain]
  simp only [PIR.Process.bind, Values.get, denoteRepeatOn,
    show ([0, 1].map ({} : ProtocolContext).roles).contains 1 = true from rfl,
    show encoding.layers ≤ layerSpec.maximum from admitted.2.2.2.1,
    ite_true, Finite.execute, Finite.Domain.admit, Finite.admitThen, List.range_eq_range',
    verifierLayerState_masked {} 1 rfl]
  erw [layers_fold encoding «outputs» admitted handle 0 encoding.layers (by omega) point _ pointSize,
    PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, verifierLayerState, Values.get]
  simp only [TypedABI.get_cons_here, TypedABI.get_cons_there]
  conv_rhs => rw [PIR.Process.bind_assoc]
  apply (layers_yields (G := G) encoding handle encoding.layers point _ pointSize).bind_congr
  intro final finalSize
  erw [input_reads encoding «outputs» admitted final.2.1 final.2.2 finalSize]
  rfl

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
