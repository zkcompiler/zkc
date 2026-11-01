module

public import ZkcSecurityExamples.Gkr.CanonicalVerifierRounds
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import ZkcSecurityExamples.Gkr.CanonicalVerifierCoefficients
public import ZkcSecurityExamples.Gkr.HonestProducerCurrentLayer
public import ZkcExamples.Structured.GkrLayerReading

@[expose] public section

/-! Exact source mathematics for the observed validator layer. Both independent
round points and every coefficient retain their actual source coordinates. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalVerifier
open Zkc Source Structured
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcExamples.Structured Generated.Presentations.Gkr.Root GkrSourceLaws
open SumcheckVerifierHelpers HonestProducerSource HonestProducerOccurrences
open GkrLayerReading
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]


omit [AddCommGroup G] [Module F G] [DecidableEq G] in
/-- All-return lengths are used only to justify subsequent actual helper
bounds. No stopped or rejected path is removed by this invariant. -/
theorem rounds_yields (ctx : ProtocolContext) (handle : Nat) (site : String)
    (count : Nat) (claim : F) :
    PIR.Yields (fun result : List F × F => result.1.length = count)
      (validatorRounds (G := G) ctx handle site 0 count ([], claim)) := by
  apply erased_yields
  rw [validatorRounds_erase]
  exact (GkrLayerReading.rounds_yields (G := G) ctx handle count claim).interpret CommonAdapter.embed

/-- The actual current callback is the observed mathematical layer for all
adversarial field replies, including failed round and line checks. -/
theorem layer_reads (encoding : CircuitEncoding F) («outputs» : List F)
    (admitted : encoding.Admitted 4 4 «outputs») (handle index : Nat)
    (inside : index < encoding.layers) (point : List F) (claim : F)
    (pointSize : point.length = encoding.width) :
    layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations)
      (((SourceRows.LayerArguments.pack {
          index := some index,
          proverPoint := none,
          point := some point,
          claim := some claim,
          «inputs» := some encoding.inputs,
          add := some encoding.add,
          mul := some encoding.mul,
          layers := some encoding.layers,
          selector := some encoding.selector,
          width := some encoding.width,
          service := some handle
        })) : Values (Component (assignment F G))
          (.index :: (layerSpec.state ++ layerSpec.captures))).get =
      (HonestProducerObservedLayers.validatorLayer {} handle encoding.width currentLayerSites
        encoding.circuit.add encoding.circuit.mul (index, point, claim)).bind
          (fun result => .done (verifierLayerState (some result.2.1) (some result.2.2))) := by
  have widthBound := admitted.2.2.1
  have small : encoding.width + encoding.width + encoding.width < 64 := by omega
  have position : index < 2 ^ encoding.selector := lt_of_lt_of_le inside admitted.1.2.2.2
  have positive : 0 < 2 ^ (encoding.width + encoding.width + encoding.width) := by positivity
  have addBound : encoding.add.length < indexLimit := by
    rw [admitted.1.2.1, ← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by have := admitted.2.2.2.2; omega)
  have mulBound : encoding.mul.length < indexLimit := by
    rw [admitted.1.2.2.1, ← Nat.pow_add]
    exact Nat.pow_lt_pow_right (by decide) (by have := admitted.2.2.2.2; omega)
  have addBlock : (GkrSourceLaws.block encoding.add index
      (2 ^ (encoding.width + encoding.width + encoding.width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [GkrSourceLaws.block]) addBound
  have mulBlock : (GkrSourceLaws.block encoding.mul index
      (2 ^ (encoding.width + encoding.width + encoding.width))).length < indexLimit :=
    Nat.lt_of_le_of_lt (by simp [GkrSourceLaws.block]) mulBound
  have normalized := layerPresentation_equation (F := F) (G := G) {} (.root _ _)
    beforeRoot beforeRoot_masked index (some point) (some claim) (some encoding.inputs)
    (some encoding.add) (some encoding.mul) (some encoding.layers)
    (some encoding.selector) (some encoding.width) (some handle)
  refine normalized.trans ?_
  dsimp only [layerPresentation, layerPresentation_certificate]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.sourceHelper20Helper ((SourceRows.PointClaimInputs.pack { point := point, claim := claim })),
      tuple20_plain (F := F) (G := G) point claim]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.sourceHelper37Helper ((SourceRows.PendingInputs.pack { claim := claim })),
      pending_plain (F := F) (G := G) claim]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (GkrVerifier.leftContext {}) 1
    ((SourceRows.RoundsInputs.pack {
        add := none,
        mul := none,
        left := none,
        right := none,
        pending := some [],
        claim := some claim,
        count := some encoding.width,
        service := some handle
      }))).bind _ = _
  erw [rounds_reads (GkrVerifier.leftContext {}) rfl rfl handle encoding.width widthBound [] claim,
    PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Values.append,
    Values.present, List.nil_append]
  unfold HonestProducerObservedLayers.validatorLayer
  rw [PIR.Process.bind_assoc]
  apply (rounds_yields (G := G) (GkrVerifier.leftContext {}) handle currentLayerSites.left
    encoding.width claim).bind_congr
  intro left leftSize
  change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (GkrVerifier.rightContext {}) 1
    ((SourceRows.RoundsInputs.pack {
        add := none,
        mul := none,
        left := none,
        right := none,
        pending := some left.1,
        claim := some left.2,
        count := some encoding.width,
        service := some handle
      }))).bind _ = _
  erw [rounds_reads (GkrVerifier.rightContext {}) rfl rfl handle encoding.width widthBound left.1 left.2,
    PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Values.append,
    Values.present]
  conv_rhs => rw [PIR.Process.bind_assoc]
  apply (rounds_yields (G := G) (GkrVerifier.rightContext {}) handle currentLayerSites.right
    encoding.width left.2).bind_congr
  intro right rightSize
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.sourceHelper40Helper ((SourceRows.RepackPendingInputs.pack { point := left.1 ++ right.1, claim := right.2 })),
      GkrRoundsReading.tuple40_plain (F := F) (G := G) (left.1 ++ right.1) right.2]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.sourceHelper50Helper
      ((SourceRows.SplitPendingInputs.pack { point := left.1 ++ right.1 })),
      split_pending_plain (F := F) (G := G) left.1 right.1
      (by rw [leftSize, rightSize]) (by rw [List.length_append, leftSize, rightSize]; unfold indexLimit; omega)]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
    (Values (Component (assignment F G)) layerSpec.state)
    (.action (.receive (.field scalarDomain) (GkrVerifier.lineConstantSite {}) 0)) _ = _
  simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
  apply congrArg (PIR.Process.call _)
  funext first
  change F at first
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.emptyHelper (SourceRows.EmptyInputs.pack {  }),
      GkrRoundsReading.empty_plain (F := F) (G := G)]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.appendHelper
      ((SourceRows.AppendInputs.pack { vector := [], element := first })),
      GkrRoundsReading.append_plain]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  change (denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec {} 1
    (some encoding.width) (verifierCoefficientState (some [first])) ((SourceRows.CoefficientCaptures.pack { line := none }))
    (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get)
    Occurrence.iterations (coefficientSite.site)).bind _ = _
  rw [coefficient_protocols]
  erw [coefficients_repeat (F := F) (G := G) ({} : ProtocolContext) (by decide) (coefficientSite.site)
    encoding.width widthBound [first], PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, verifierCoefficientState, Values.get]
  have coefficientsYield : PIR.Yields (fun coefficients : List F =>
      coefficients.length = encoding.width + 1)
      (HonestProducerObservedLayers.validatorCoefficients (G := G) {} (coefficientSite.site) 0 encoding.width [first]) := by
    apply erased_yields
    rw [HonestProducerObservedLayers.validatorCoefficients_erase]
    have yields := PIR.Yields.repeatN
      (invariant := fun index (coefficients : List F) => coefficients.length = index + 1)
      (step := GkrVerifier.lineCoefficient (G := G) {})
      (fun index coefficients length => (lineCoefficient_yields {} coefficients).mono
        fun next advanced => by omega) encoding.width 0 [first] rfl
    simpa only [Nat.zero_add] using yields.interpret CommonAdapter.embed
  conv_rhs => rw [PIR.Process.bind_assoc]
  apply coefficientsYield.bind_congr
  intro coefficients coefficientsLength
  have coefficientsBound : coefficients.length < indexLimit := by
    rw [coefficientsLength]; unfold indexLimit; omega
  have pointsBound : left.1.length < indexLimit := by rw [leftSize]; unfold indexLimit; omega
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.sumHelper
      ((SourceRows.SumInputs.pack { coefficients := coefficients })),
      sum_plain]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.selectBlockHelper
      ((SourceRows.SelectBlockInputs.pack {
          table := encoding.add,
          position := index,
          bits := encoding.selector
        })),
      GkrLayerReading.selectBlock_plain encoding.add index encoding.selector _
      admitted.1.2.1 positive position addBound]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.evaluateWiringHelper
      ((SourceRows.EvaluateWiringInputs.pack {
          table := block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width)),
          point := point,
          left := left.1,
          right := right.1
        })),
      evaluateWiring_plain encoding.width
      (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width))) point left.1 right.1
      (encoding.circuit.add index) (encoding.add_decode admitted.1 index inside)
      pointSize leftSize rightSize small addBlock]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.selectBlockHelper
      ((SourceRows.SelectBlockInputs.pack {
          table := encoding.mul,
          position := index,
          bits := encoding.selector
        })),
      GkrLayerReading.selectBlock_plain encoding.mul index encoding.selector _
      admitted.1.2.2.1 positive position mulBound]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.evaluateWiringHelper
      ((SourceRows.EvaluateWiringInputs.pack {
          table := block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width)),
          point := point,
          left := left.1,
          right := right.1
        })),
      evaluateWiring_plain encoding.width
      (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width))) point left.1 right.1
      (encoding.circuit.mul index) (encoding.mul_decode admitted.1 index inside)
      pointSize leftSize rightSize small mulBlock]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  let addValue := extension (encoding.width + encoding.width + encoding.width)
    (encoding.circuit.add index) (coordinates (encoding.width + encoding.width + encoding.width)
      (point ++ left.1 ++ right.1))
  let mulValue := extension (encoding.width + encoding.width + encoding.width)
    (encoding.circuit.mul index) (coordinates (encoding.width + encoding.width + encoding.width)
      (point ++ left.1 ++ right.1))
  dsimp +instances only [TypedABI.get_cons_here, TypedABI.get_cons_there]
  simp only [protocolOperationWithOn, Participant.guard, ProtocolContext.roles,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get,
    PIR.Process.interpret, PIR.Process.bind, id_eq, Bool.decide_eq_true]
  conv_lhs =>
    change (if right.2 = GkrVerifier.wiringValue addValue mulValue first coefficients.sum then _ else _)
  by_cases check : right.2 = GkrVerifier.wiringValue addValue mulValue first coefficients.sum
  · rw [lineCheck_pos {} handle encoding.width (encoding.circuit.add index) (encoding.circuit.mul index)
      (index, point, claim) left.1 right.1 right.2 first coefficients check]
    rw [ite_eq_left check]
    change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) layerSpec.state)
      (.action (.query (GkrVerifier.lineChallengeSite {}) scalarDomain ((SourceRows.RoundCaptures.pack { service := handle })))) _ = _
    simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
    apply congrArg (PIR.Process.call _)
    funext challenge
    change F at challenge
    change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) layerSpec.state)
      (.action (.send (ty := .field scalarDomain) (GkrVerifier.lineDeliverySite {}) 0 challenge)) _ = _
    simp only [GkrVerifier.lineDelivery, PIR.Process.interpret, CommonAdapter.embed,
      Occurrence.actions, PIR.Process.bind]
    apply congrArg (PIR.Process.call _)
    funext delivered
    conv_lhs =>
      arg 1
      erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
        GkrSourceBodies.linePointHelper
        ((SourceRows.LinePointInputs.pack { start := left.1, finish := right.1, challenge := challenge })),
        GkrLayerReading.linePoint_plain left.1 right.1 challenge
        (by rw [leftSize, rightSize]) pointsBound]
    dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
    conv_lhs =>
      arg 1
      erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
        GkrSourceBodies.evaluateCoefficientsHelper
        ((SourceRows.EvaluateCoefficientsInputs.pack {
            coefficients := coefficients,
            challenge := challenge
          })),
        GkrLayerReading.evaluateCoefficients_plain coefficients challenge coefficientsBound]
    dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
    conv_lhs =>
      arg 1
      erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
        GkrSourceBodies.sourceHelper19Helper
        ((SourceRows.NextPointClaimInputs.pack {
            point := linePoints left.1 right.1 challenge,
            claim := powerSum coefficients challenge
          })),
        tuple19_plain]
    rfl
  · rw [lineCheck_neg {} handle encoding.width (encoding.circuit.add index) (encoding.circuit.mul index)
      (index, point, claim) left.1 right.1 right.2 first coefficients check]
    rw [ite_eq_right check]
    rfl

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
