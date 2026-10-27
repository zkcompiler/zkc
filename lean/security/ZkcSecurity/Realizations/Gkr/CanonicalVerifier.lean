module

public import ZkcSecurity.Realizations.Gkr.CanonicalVerifierLayer
public import ZkcSecurity.Realizations.Gkr.CanonicalVerifierOutput

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
open ZkcExamples.Structured GkrSourceCallbacks SumcheckVerifierHelpers
open HonestProducerSource HonestProducerOccurrences HonestProducerObserved
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

abbrev captures (encoding : CircuitEncoding F) (handle : Nat) :
    Values (Component (assignment F G)) layerSpec.captures :=
  .cons (some encoding.inputs) (.cons (some encoding.add) (.cons (some encoding.mul)
    (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
      (.cons (some handle) .nil))))))

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

theorem layers_fold (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (handle index count : Nat)
    (inside : index + count ≤ encoding.layers) (point : List F) (claim : F)
    (pointSize : point.length = encoding.width) :
    Finite.fold (fun state index => Repeat.stepOn layerSpec {} 1 (captures encoding handle)
      (callback (F := F) (G := G)) state index Occurrence.iterations "s57")
      (List.range' index count) (verifierLayerState (some point) (some claim)) =
    (validatorLayers {} handle currentSites encoding index count (index, point, claim)).bind
      (fun result => .done (verifierLayerState (some result.2.1) (some result.2.2))) := by
  induction count generalizing index point claim with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold]
    simp only [Repeat.stepOn, verifierLayerState_masked {} 1 rfl, callback, captures,
      layer_reads encoding outputs admitted handle index (by omega) point claim pointSize,
      IterationObservations.within_eq, PIR.Process.bind_assoc, PIR.Process.bind, validatorLayers]
    apply congrArg (PIR.Process.bind _)
    funext entered
    apply (layer_yields (G := G) encoding handle (index, point, claim)).bind_congr
    intro next valid
    apply congrArg (PIR.Process.bind _)
    funext left
    have rest := ih (index + 1) (by omega) next.2.1 next.2.2 valid.2
    have same : (index + 1, next.2.1, next.2.2) = next := by rw [← valid.1]
    rw [same] at rest
    simpa only [Repeat.stepOn, IterationObservations.within_eq, PIR.Process.bind_assoc,
      verifierLayerState_masked {} 1 rfl, PIR.Process.bind, ProtocolContext.mapScopes,
      ProtocolContext.roles, List.map, List.map_nil, layerSpec, callback, captures] using rest

omit [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem output_yields (handle count : Nat) :
    PIR.Yields (fun point : List F => point.length = count)
      (validatorOutput (G := G) {} handle "s37" 0 count []) := by
  apply erased_yields
  rw [HonestProducerCurrentVerifier.output_erase]
  have yields := PIR.Yields.repeatN
    (invariant := fun index (point : List F) => point.length = index)
    (step := GkrVerifier.outputRound (G := G) {} handle)
    (fun index point length => (GkrLayerReading.outputRound_yields {} handle point).mono
      fun next advanced => by omega) count 0 [] rfl
  simpa only [Nat.zero_add] using yields.interpret CommonAdapter.embed

omit [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem layers_yields (encoding : CircuitEncoding F) (handle count : Nat)
    (point : List F) (claim : F) (pointSize : point.length = encoding.width) :
    PIR.Yields (fun next : Nat × List F × F => next.2.1.length = encoding.width)
      (validatorLayers (G := G) {} handle currentSites encoding 0 count (0, point, claim)) := by
  apply erased_yields
  rw [HonestProducerCurrentVerifier.layers_erase]
  have yields := PIR.Yields.repeatN
    (invariant := fun _ (state : Nat × List F × F) => state.2.1.length = encoding.width)
    (step := GkrVerifier.layerStep (G := G) {} handle encoding.width
      encoding.circuit.add encoding.circuit.mul)
    (fun _ state _ => (GkrLayerReading.layerStep_yields handle encoding.width
      encoding.circuit.add encoding.circuit.mul state).mono fun _ valid => valid.2)
    count 0 (0, point, claim) pointSize
  exact yields.interpret CommonAdapter.embed

/-- Full current-source validator reading, without a helper, transcript or
representation premise and without erasing nominal occurrence boundaries. -/
theorem reads (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (handle : Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 1
      (currentInputs encoding outputs (some handle)) =
    (validator {} handle currentSites encoding outputs).bind
      (fun accepted => .done (.cons accepted .nil)) := by
  have shape := admitted.1
  erw [OccurrenceVerifier.admitted (G := G) encoding.inputs outputs encoding.add encoding.mul
    encoding.layers encoding.selector encoding.width handle admitted.2.2.1 admitted.2.2.2.1
    shape.1 admitted.2.1 (by simpa only [← Nat.pow_add, Nat.add_assoc] using shape.2.1)
    (by simpa only [← Nat.pow_add, Nat.add_assoc] using shape.2.2.1)
    admitted.2.2.2.2 shape.2.2.2]
  unfold OccurrenceVerifier.process validator
  rw [observed_helper, GkrRoundsReading.empty_plain]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  rw [output_protocols]
  erw [output_repeat (F := F) (G := G) ({} : ProtocolContext) (by decide) "s37"
    handle encoding.width admitted.2.2.1 [], PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, verifierOutputState, Values.get]
  rw [PIR.Process.bind_assoc]
  apply (output_yields (G := G) handle encoding.width).bind_congr
  intro point pointSize
  have small : encoding.width < 64 := by have := admitted.2.2.1; omega
  have outputBound : outputs.length < indexLimit := by
    rw [admitted.2.1]; exact Nat.pow_lt_pow_right (by decide) small
  rw [observed_helper, GkrLayerReading.evaluate_plain encoding.width outputs point
    ((ofList? encoding.width outputs).getD 0) (CircuitEncoding.decode_getD outputs admitted.2.1)
    pointSize small outputBound]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get, observed_helper, GkrLayerReading.tuple19_plain]
  simp only [PIR.Process.bind, Values.get, denoteRepeatOn,
    show ([0, 1].map ({} : ProtocolContext).roles).contains 1 = true from rfl,
    show encoding.layers ≤ layerSpec.maximum from admitted.2.2.2.1,
    ite_true, Finite.execute, Finite.Domain.admit, Finite.admitThen, List.range_eq_range',
    verifierLayerState_masked {} 1 rfl]
  erw [layers_fold encoding outputs admitted handle 0 encoding.layers (by omega) point _ pointSize,
    PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, verifierLayerState, Values.get]
  simp only [TypedABI.get_cons_here, TypedABI.get_cons_there]
  conv_rhs => rw [PIR.Process.bind_assoc]
  apply (layers_yields (G := G) encoding handle encoding.layers point _ pointSize).bind_congr
  intro final finalSize
  rw [input_reads encoding outputs admitted final.2.1 final.2.2 finalSize]
  rfl

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
