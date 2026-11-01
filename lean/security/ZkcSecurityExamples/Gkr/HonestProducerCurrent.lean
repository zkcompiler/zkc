module
public import ZkcSecurityExamples.Gkr.HonestProducerCurrentLayer
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Source.Structured.OccurrenceYields

@[expose] public section

/-! Current GKR root occurrence binding and invariant-preserving source loop.
The callback equation is discharged by the actual producer source theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource
open Zkc Source Structured ZkcExamples.Structured Generated.Presentations.Gkr.Root SumcheckVerifierHelpers
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

omit [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G] in
theorem observed_layer_yields (sites : HonestProducerObservedLayers.Sites) (encoding : CircuitEncoding F)
    (index : Nat) (point : List F) :
    PIR.Yields (fun result => result.length = encoding.width)
      (HonestProducerObservedLayers.producerLayer (G := G) {} sites encoding.circuit
        (encoding.layers - index - 1) index point) := by
  apply HonestProducerOccurrences.erased_yields
  rw [HonestProducerObservedLayers.producerLayer_erase]
  exact layer_yields {} encoding.circuit (encoding.layers - index - 1) index point

abbrev layerCapturesValues (encoding : CircuitEncoding F) :
    Values (Component (assignment F G)) layerSpec.captures :=
  (SourceRows.LayerCaptures.pack {
      «inputs» := some encoding.inputs,
      add := some encoding.add,
      mul := some encoding.mul,
      layers := some encoding.layers,
      selector := some encoding.selector,
      width := some encoding.width,
      service := none
    })

abbrev observedLayerBody : RegionFunction (Component (assignment F G))
    (Occurrence.signature (uniformCarriers F G)) (.index :: (layerSpec.state ++ layerSpec.captures), layerSpec.state) :=
  fun args => layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get

theorem observed_layers_fold (encoding : CircuitEncoding F) (sites : HonestProducerObserved.Sites)
    (equation : ∀ index point, index < encoding.layers → point.length = encoding.width →
      observedLayerBody (F := F) (G := G)
        (SourceRows.LayerArguments.pack {
            index := some index,
            proverPoint := some point,
            point := none,
            claim := none,
            «inputs» := some encoding.inputs,
            add := some encoding.add,
            mul := some encoding.mul,
            layers := some encoding.layers,
            selector := some encoding.selector,
            width := some encoding.width,
            service := none
          }) =
      (HonestProducerObservedLayers.producerLayer {} sites.layer encoding.circuit
        (encoding.layers - index - 1) index point).bind fun result => .done (proverLayerState (some result)))
    (index count : Nat) (inside : index + count ≤ encoding.layers)
    (point : List F) (pointSize : point.length = encoding.width) :
    Finite.fold (fun state index => Repeat.stepOn layerSpec {} 0 (layerCapturesValues encoding)
      (observedLayerBody (F := F) (G := G)) state index Occurrence.iterations sites.layers)
      (List.range' index count) (proverLayerState (some point)) =
      (HonestProducerObserved.producerLayers {} sites encoding index count point).bind
        (fun result => .done (proverLayerState (some result))) := by
  have translated := Zkc.Source.Structured.LoopPresentation.foldInvariant
    (fun state index => Repeat.stepOn layerSpec {} 0 (layerCapturesValues encoding)
      (observedLayerBody (F := F) (G := G)) state index Occurrence.iterations sites.layers)
    (fun point index => Occurrence.iterations.within sites.layers index
      (HonestProducerObservedLayers.producerLayer {} sites.layer encoding.circuit
        (encoding.layers - index - 1) index point))
    (fun _ point => proverLayerState (some point))
    (fun _ point => point.length = encoding.width) encoding.layers
    (by
      intro index point inside sized
      simp only [Repeat.stepOn, proverLayerState_masked {} 0 rfl]
      have callback := equation index point inside sized
      dsimp only [SourceRows.LayerArguments.pack] at callback
      simp only [layerCapturesValues, SourceRows.LayerCaptures.pack, proverLayerState, Values.append]
      rw [callback]
      simp only [IterationObservations.within_eq, PIR.Process.bind_assoc, PIR.Process.bind,
        qualifyProtocolSite, proverLayerState_masked {} 0 rfl]
      rfl)
    (fun index point _ _ => Zkc.Source.Structured.OccurrenceYields.within _ _ _
      (observed_layer_yields (G := G) sites.layer encoding index point))
    index count inside point pointSize
  rw [translated]
  rfl

theorem output_protocols (ctx : ProtocolContext) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G))) :
    outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      observedHelpers self protocols ctx Occurrence.iterations) =
    outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      observedHelpers self [] ctx Occurrence.iterations) := by rfl

theorem root_body (encoding : CircuitEncoding F) («outputs» : Option (List F)) (service : Option Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0
      ((SourceRows.Inputs.pack {
          «inputs» := some encoding.inputs,
          «outputs» := «outputs»,
          add := some encoding.add,
          mul := some encoding.mul,
          layers := some encoding.layers,
          selector := some encoding.selector,
          width := some encoding.width,
          service := service
        })) =
    rootPresentation {} beforeRoot (some encoding.inputs) (some encoding.add) (some encoding.mul)
      (some encoding.layers) (some encoding.selector) (some encoding.width) := by
  rw [participant_body]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.gkrDefinition.body_eq_of_raw _ gkrBody_raw]
  erw [rootPresentation_equation (F := F) (G := G) {} (.root _ _)
    beforeRoot beforeRoot_masked (some encoding.inputs) (some encoding.add) (some encoding.mul)
    (some encoding.layers) (some encoding.selector) (some encoding.width)]
  dsimp only [rootPresentation, rootPresentation_certificate]
  have resultMask : maskValues 0 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.outputScopes)
      ((SourceRows.Decision.pack { accepted := none }) : Values (Component (assignment F G)) [.boolean]) = (SourceRows.Decision.pack { accepted := none }) := rfl
  dsimp only [SourceRows.Decision.pack] at resultMask
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, resultMask]

theorem observed_from_layer (encoding : CircuitEncoding F) («outputs» : List F)
    (admitted : encoding.Admitted 4 4 «outputs») (service : Option Nat)
    (layerSites : HonestProducerObservedLayers.Sites)
    (equation : ∀ index point, index < encoding.layers → point.length = encoding.width →
      observedLayerBody (F := F) (G := G)
        (SourceRows.LayerArguments.pack {
            index := some index,
            proverPoint := some point,
            point := none,
            claim := none,
            «inputs» := some encoding.inputs,
            add := some encoding.add,
            mul := some encoding.mul,
            layers := some encoding.layers,
            selector := some encoding.selector,
            width := some encoding.width,
            service := none
          }) =
      (HonestProducerObservedLayers.producerLayer {} layerSites encoding.circuit
        (encoding.layers - index - 1) index point).bind fun result => .done (proverLayerState (some result))) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0
      ((SourceRows.Inputs.pack {
          «inputs» := some encoding.inputs,
          «outputs» := some «outputs»,
          add := some encoding.add,
          mul := some encoding.mul,
          layers := some encoding.layers,
          selector := some encoding.selector,
          width := some encoding.width,
          service := service
        })) =
    HonestProducerObserved.producer {} ⟨(outputSite.site), (layerSite.site), layerSites⟩ encoding := by
  rw [root_body]
  dsimp only [rootPresentation, rootPresentation_certificate, NormalForm.runsAtOn, NormalForm.meaningAtOn]
  erw [OccurrencePresentation.closed_helper, HonestProducerRounds.empty_plain]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get, TypedABI.get_cons_here]
  erw [output_protocols]
  erw [output_repeat (F := F) (G := G) ({} : ProtocolContext) (by decide) (outputSite.site)
    encoding.width admitted.2.2.1 []]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, proverOutputState,
    TypedABI.get_cons_here, TypedABI.get_cons_there]
  unfold HonestProducerObserved.producer
  apply (show PIR.Yields (fun point : List F => point.length = encoding.width)
      (HonestProducerObserved.producerOutput (G := G) {} (outputSite.site) 0 encoding.width []) from by
    apply HonestProducerOccurrences.erased_yields
    rw [HonestProducerObserved.producerOutput_erase]
    simpa only [List.length_nil, Nat.zero_add] using output_yields (F := F) (G := G) {} encoding.width []).bind_congr
  intro point pointSize
  simp only [denoteRepeatOn, show ([0, 1].map ({} : ProtocolContext).roles).contains 0 = true from rfl,
    show encoding.layers ≤ layerSpec.maximum from admitted.2.2.2.1,
    ite_true, Finite.execute, Finite.Domain.admit, Finite.admitThen, List.range_eq_range',
    proverLayerState_masked {} 0 rfl]
  erw [observed_layers_fold encoding ⟨(outputSite.site), (layerSite.site), layerSites⟩ equation 0 encoding.layers
    (by omega) point pointSize]
  simp [PIR.Process.bind_assoc, PIR.Process.bind]

/-- The current root sites and nested iteration sites come from its checked callbacks. -/
abbrev currentSites : HonestProducerObserved.Sites := ⟨(outputSite.site), (layerSite.site), currentLayerSites⟩

/-- Universal association with the actual current source. Circuit admission is
independent of the producer, all helper results and every challenge reply. -/
theorem observed (encoding : CircuitEncoding F) («outputs» : List F)
    (admitted : encoding.Admitted 4 4 «outputs») (service : Option Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0 (SourceRows.Inputs.pack {
        «inputs» := some encoding.inputs,
        «outputs» := some «outputs»,
        add := some encoding.add,
        mul := some encoding.mul,
        layers := some encoding.layers,
        selector := some encoding.selector,
        width := some encoding.width,
        service := service
      }) =
      HonestProducerObserved.producer {} currentSites encoding := by
  have shape := admitted.1
  have widthBound := admitted.2.2.1
  have layersBound := admitted.2.2.2.1
  have dimension := admitted.2.2.2.2
  have layersSmall : encoding.layers < indexLimit := lt_of_le_of_lt layersBound (by decide)
  have addBound : encoding.add.length < indexLimit := by
    rw [shape.2.1, ← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have mulBound : encoding.mul.length < indexLimit := by
    rw [shape.2.2.1, ← Nat.pow_add]
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have roundsCapacity : 2 ^ (encoding.width + encoding.width) < indexLimit := by
    apply Nat.pow_lt_pow_right (by decide)
    omega
  have lineCapacity : 2 ^ encoding.width * (encoding.width + 1) < indexLimit := by
    have : 2 ^ encoding.width ≤ 2 ^ 4 := Nat.pow_le_pow_right (by decide) widthBound
    calc
      _ ≤ 16 * 5 := Nat.mul_le_mul this (by omega)
      _ < indexLimit := by decide
  exact observed_from_layer encoding «outputs» admitted service currentLayerSites (by
    intro index point inside pointSize
    exact layer_actual encoding shape index inside point pointSize widthBound layersSmall
      (by omega) addBound mulBound roundsCapacity lineCapacity)

/-- Erasing the actual source occurrence boundaries recovers the same producer
association on the ordinary participant interface, including arbitrary private slots. -/
theorem original (encoding : CircuitEncoding F) («outputs» : List F)
    (admitted : encoding.Admitted 4 4 «outputs») (service : Option Nat) :
    GkrSourceViews.program.participant F G 0 (SourceRows.Inputs.pack {
        «inputs» := some encoding.inputs,
        «outputs» := some «outputs»,
        add := some encoding.add,
        mul := some encoding.mul,
        layers := some encoding.layers,
        selector := some encoding.selector,
        width := some encoding.width,
        service := service
      }) =
      producer {} encoding := by
  calc
    _ = GkrSourceViews.program.participantOn (ringModel F G) 0
        (SourceRows.Inputs.pack {
            «inputs» := some encoding.inputs,
            «outputs» := some «outputs»,
            add := some encoding.add,
            mul := some encoding.mul,
            layers := some encoding.layers,
            selector := some encoding.selector,
            width := some encoding.width,
            service := service
          }) :=
      Program.participant_eq_participantOn _ _ _
    _ = (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
        (SourceRows.Inputs.pack {
            «inputs» := some encoding.inputs,
            «outputs» := some «outputs»,
            add := some encoding.add,
            mul := some encoding.mul,
            layers := some encoding.layers,
            selector := some encoding.selector,
            width := some encoding.width,
            service := service
          })).interpret Occurrence.erase :=
      (Occurrence.participant_erase _ _ _ _).symm
    _ = (HonestProducerObserved.producer (G := G) {} currentSites encoding).interpret Occurrence.erase :=
      congrArg (fun process => process.interpret Occurrence.erase)
        (observed (G := G) encoding «outputs» admitted service)
    _ = _ := HonestProducerObserved.producer_erase {} currentSites encoding
end ZkcSecurity.Realizations.Gkr.HonestProducerSource
