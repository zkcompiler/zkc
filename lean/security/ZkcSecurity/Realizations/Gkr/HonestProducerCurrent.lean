module
public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrentLayer
@[expose] public section

/-! Current GKR root occurrence binding and invariant-preserving source loop.
The callback equation is discharged by the actual producer source theorem. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource
open Zkc Source Structured ZkcExamples.Structured GkrSourceCallbacks SumcheckVerifierHelpers
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
  .cons (some encoding.inputs) (.cons (some encoding.add) (.cons (some encoding.mul)
    (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
      (.cons none .nil))))))

abbrev observedLayerBody : RegionFunction (Component (assignment F G))
    (Occurrence.signature (uniformCarriers F G)) (.index :: (layerSpec.state ++ layerSpec.captures), layerSpec.state) :=
  fun args => layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
    observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get

theorem observed_layers_fold (encoding : CircuitEncoding F) (sites : HonestProducerObserved.Sites)
    (equation : ∀ index point, index < encoding.layers → point.length = encoding.width →
      observedLayerBody (F := F) (G := G)
        (.cons (some index) ((proverLayerState (some point)).append (layerCapturesValues encoding))) =
      (HonestProducerObservedLayers.producerLayer {} sites.layer encoding.circuit
        (encoding.layers - index - 1) index point).bind fun result => .done (proverLayerState (some result)))
    (index count : Nat) (inside : index + count ≤ encoding.layers)
    (point : List F) (pointSize : point.length = encoding.width) :
    Finite.fold (fun state index => Repeat.stepOn layerSpec {} 0 (layerCapturesValues encoding)
      (observedLayerBody (F := F) (G := G)) state index Occurrence.iterations sites.layers)
      (List.range' index count) (proverLayerState (some point)) =
      (HonestProducerObserved.producerLayers {} sites encoding index count point).bind
        (fun result => .done (proverLayerState (some result))) := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [List.range'_succ, Finite.fold]
    simp only [Repeat.stepOn, proverLayerState_masked {} 0 rfl, equation index point (by omega) pointSize,
      IterationObservations.within_eq, PIR.Process.bind_assoc, PIR.Process.bind,
      HonestProducerObserved.producerLayers]
    apply congrArg (PIR.Process.bind _)
    funext entered
    apply (observed_layer_yields (G := G) sites.layer encoding index point).bind_congr
    intro next nextSize
    apply congrArg (PIR.Process.bind _)
    funext left
    simpa only [Repeat.stepOn, IterationObservations.within_eq, PIR.Process.bind_assoc,
      proverLayerState_masked {} 0 rfl, PIR.Process.bind, ProtocolContext.mapScopes,
      ProtocolContext.roles, List.map, List.map_nil, layerSpec] using
      ih (index + 1) (by omega) next nextSize
def rootPresentation (tables : Evaluation.ComponentTablesOn (uniformCarriers F G) (Occurrence.signature (uniformCarriers F G))) (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G))) (initial add mul : List F) (layers selector width : Nat) :
    PIR.Process (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) [.boolean]) :=
  (invoke tables.closed GkrSourceBodies.emptyHelper .nil).bind fun empty =>
  (denoteRepeatOn (carriers := uniformCarriers F G) outputSpec {} 0 (some width)
    (proverOutputState (some (empty.get .here))) (.cons none .nil)
    (fun args => outputBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions tables 0 protocols {} Occurrence.iterations) args.get)
    Occurrence.iterations "s37").bind fun output =>
  (denoteRepeatOn (carriers := uniformCarriers F G) layerSpec {} 0 (some layers)
    (proverLayerState (output.get (.there .here)))
    (.cons (some initial) (.cons (some add) (.cons (some mul) (.cons (some layers)
      (.cons (some selector) (.cons (some width) (.cons none .nil)))))))
    (fun args => layerBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions tables 0 protocols {} Occurrence.iterations) args.get)
    Occurrence.iterations "s57").bind fun _ => .done (.cons none .nil)


set_option maxHeartbeats 2000000 in
theorem root_occurrence (initial add mul : List F) (layers selector width : Nat) :
 gkrBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 (beforeRoot (F := F) (G := G)) {} Occurrence.iterations)
 ((.cons (some initial) (.cons none (.cons (some add) (.cons (some mul) (.cons (some layers) (.cons (some selector) (.cons (some width) (.cons none .nil)))))))) : Values (Component (assignment F G)) gkrInputs).get =
 rootPresentation observedHelpers beforeRoot initial add mul layers selector width := by
  unfold gkrBody rootPresentation
  repeat' (rw [Region.denote]; simp [participantMeaningWithOn, protocolOperationWithOn,
    Operands.eval, Regions.denote, Values.get, Values.get_cons, Values.split,
    TypedABI.get_cons_here, TypedABI.get_cons_there,
    Environment.prepend, Environment.push, SiteObservations.silent,
    Participant.owned, Participant.restrict, Participant.guard,
    RoleFamily.sequence, Values.absent, ProtocolOp.results,
    PIR.Process.bind, PIR.Process.bind_assoc, PIR.Process.bind_done, PIR.Process.interpret,
    Values.present, participantActions, ProtocolContext.roles,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_two, SumcheckHelperLaws.prepend_three,
    Evaluation.componentOperationOn, Evaluation.operationOn, strictComponent, Evaluation.meaningOn,
    Evaluation.operation, Op.calculationRegions, Primitive.evaluate, primitiveOutcome,
    show 4 < indexLimit by decide, show 1 < indexLimit by decide,
    Op.results, HonestProducerRounds.empty_plain, plainHelpers])
  congr 1
  funext output
  simp [Region.denote, participantMeaningWithOn, protocolOperationWithOn,
    Operands.eval, Regions.denote, Values.get, Values.get_cons, Values.split,
    TypedABI.get_cons_here, TypedABI.get_cons_there,
    Environment.prepend, Environment.push, SiteObservations.silent,
    Participant.owned, Participant.restrict, Participant.guard,
    RoleFamily.sequence, Values.absent, ProtocolOp.results,
    PIR.Process.bind, PIR.Process.bind_assoc, PIR.Process.bind_done, PIR.Process.interpret,
    Values.present, participantActions, ProtocolContext.roles,
    SumcheckHelperLaws.prepend_empty, SumcheckHelperLaws.prepend_one,
    SumcheckHelperLaws.prepend_two, SumcheckHelperLaws.prepend_three,
    Evaluation.componentOperationOn, Evaluation.operationOn, strictComponent, Evaluation.meaningOn,
    Evaluation.operation, Op.calculationRegions, ProtocolContext.contains,
    ProtocolContext.enter, roleSubstitution, GkrSourceBodies.sourceProtocol80Signature,
    SumcheckHelperLaws.singleton_eta, plainHelpers, maskValues]
  all_goals rfl


theorem output_protocols (ctx : ProtocolContext) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G))) :
    outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      observedHelpers self protocols ctx Occurrence.iterations) =
    outputBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      observedHelpers self [] ctx Occurrence.iterations) := by rfl

theorem root_body (encoding : CircuitEncoding F) (outputs : Option (List F)) (service : Option Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0
      (.cons (some encoding.inputs) (.cons outputs (.cons (some encoding.add) (.cons (some encoding.mul)
        (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
          (.cons service .nil)))))))) =
    rootPresentation observedHelpers beforeRoot encoding.inputs encoding.add encoding.mul
      encoding.layers encoding.selector encoding.width := by
  rw [participant_body]
  unfold CheckedProtocol.denoteWithOn
  erw [GkrSourceViews.gkrDefinition.body_eq_of_raw _ gkrBody_raw]
  have masked : maskValues 0 (({} : ProtocolContext).mapScopes GkrSourceViews.gkrDefinition.inputScopes)
      (.cons (some encoding.inputs) (.cons outputs (.cons (some encoding.add) (.cons (some encoding.mul)
        (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
          (.cons service .nil)))))))) =
      GkrProverContinuation.inputs (G := G) encoding.inputs encoding.add encoding.mul
        encoding.layers encoding.selector encoding.width := by
    simp [maskValues, Participant.restrict, ProtocolContext.mapScopes, ProtocolContext.roles,
      GkrSourceViews.gkrDefinition, GkrSourceBodies.gkrSignature, GkrProverContinuation.inputs]
    rfl
  rw [masked]
  erw [root_occurrence (F := F) (G := G) encoding.inputs encoding.add encoding.mul
    encoding.layers encoding.selector encoding.width]
  unfold rootPresentation
  simp only [PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.bind _)
  funext empty
  apply congrArg (PIR.Process.bind _)
  funext output
  apply congrArg (PIR.Process.bind _)
  funext layers
  rfl

theorem observed_from_layer (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (service : Option Nat)
    (layerSites : HonestProducerObservedLayers.Sites)
    (equation : ∀ index point, index < encoding.layers → point.length = encoding.width →
      observedLayerBody (F := F) (G := G)
        (.cons (some index) ((proverLayerState (some point)).append (layerCapturesValues encoding))) =
      (HonestProducerObservedLayers.producerLayer {} layerSites encoding.circuit
        (encoding.layers - index - 1) index point).bind fun result => .done (proverLayerState (some result))) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0
      (.cons (some encoding.inputs) (.cons (some outputs) (.cons (some encoding.add) (.cons (some encoding.mul)
        (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
          (.cons service .nil)))))))) =
    HonestProducerObserved.producer {} ⟨"s37", "s57", layerSites⟩ encoding := by
  rw [root_body]
  unfold rootPresentation
  rw [observed_helper, HonestProducerRounds.empty_plain]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get, TypedABI.get_cons_here]
  rw [output_protocols]
  erw [output_repeat (F := F) (G := G) ({} : ProtocolContext) (by decide) "s37"
    encoding.width admitted.2.2.1 []]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind, proverOutputState,
    TypedABI.get_cons_here, TypedABI.get_cons_there]
  unfold HonestProducerObserved.producer
  apply (show PIR.Yields (fun point : List F => point.length = encoding.width)
      (HonestProducerObserved.producerOutput (G := G) {} "s37" 0 encoding.width []) from by
    apply HonestProducerOccurrences.erased_yields
    rw [HonestProducerObserved.producerOutput_erase]
    simpa only [List.length_nil, Nat.zero_add] using output_yields (F := F) (G := G) {} encoding.width []).bind_congr
  intro point pointSize
  simp only [denoteRepeatOn, show ([0, 1].map ({} : ProtocolContext).roles).contains 0 = true from rfl,
    show encoding.layers ≤ layerSpec.maximum from admitted.2.2.2.1,
    ite_true, Finite.execute, Finite.Domain.admit, Finite.admitThen, List.range_eq_range',
    proverLayerState_masked {} 0 rfl]
  erw [observed_layers_fold encoding ⟨"s37", "s57", layerSites⟩ equation 0 encoding.layers
    (by omega) point pointSize]
  simp only [PIR.Process.bind_assoc, PIR.Process.bind]

/-- The current root sites and nested iteration sites come from its checked callbacks. -/
abbrev currentSites : HonestProducerObserved.Sites := ⟨"s37", "s57", currentLayerSites⟩

/-- Ordered public circuit inputs, independent output claim and verifier capability. -/
abbrev currentInputs (encoding : CircuitEncoding F) (outputs : List F) (service : Option Nat) :
    Values (Component (assignment F G)) GkrSourceBodies.gkrSignature.inputs :=
  .cons (some encoding.inputs) (.cons (some outputs) (.cons (some encoding.add) (.cons (some encoding.mul)
    (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
      (.cons service .nil)))))))

/-- Universal association with the actual current source. Circuit admission is
independent of the producer, all helper results and every challenge reply. -/
theorem observed (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (service : Option Nat) :
    Occurrence.participant (ringModel F G) GkrSourceViews.program 0 (currentInputs encoding outputs service) =
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
  exact observed_from_layer encoding outputs admitted service currentLayerSites (by
    intro index point inside pointSize
    exact layer_actual encoding shape index inside point pointSize widthBound layersSmall
      (by omega) addBound mulBound roundsCapacity lineCapacity)

/-- Erasing the actual source occurrence boundaries recovers the same producer
association on the ordinary participant interface, including arbitrary private slots. -/
theorem original (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (service : Option Nat) :
    GkrSourceViews.program.participant F G 0 (currentInputs encoding outputs service) =
      producer {} encoding := by
  calc
    _ = GkrSourceViews.program.participantOn (ringModel F G) 0
        (currentInputs encoding outputs service) :=
      Program.participant_eq_participantOn _ _ _
    _ = (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
        (currentInputs encoding outputs service)).interpret Occurrence.erase :=
      (Occurrence.participant_erase _ _ _ _).symm
    _ = (HonestProducerObserved.producer (G := G) {} currentSites encoding).interpret Occurrence.erase :=
      congrArg (fun process => process.interpret Occurrence.erase)
        (observed (G := G) encoding outputs admitted service)
    _ = _ := HonestProducerObserved.producer_erase {} currentSites encoding
end ZkcSecurity.Realizations.Gkr.HonestProducerSource
