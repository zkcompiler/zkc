module

public import ZkcSecurityExamples.Gkr.HonestProducerSource
public import Zkc.Protocols.Gkr.Source.VerifierProcess
public import Zkc.Protocols.Sumcheck.Source.VerifierHelpers

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource
open Zkc Source Structured ZkcExamples.Structured
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]


open Generated.Presentations.Gkr.Root
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcSecurity.Examples.Components
open ZkcSecurity.Examples.Components.GkrRoundsRealization
open GkrSourceLaws SumcheckVerifierHelpers HonestProducerRounds HonestProducerPackets

noncomputable abbrev currentLayerSites : HonestProducerObservedLayers.Sites :=
  ⟨qualifyProtocolSite (GkrVerifier.leftContext {}).applicationPrefix (Generated.Presentations.Gkr.Rounds.roundSite.site),
    qualifyProtocolSite (GkrVerifier.rightContext {}).applicationPrefix (Generated.Presentations.Gkr.Rounds.roundSite.site), (coefficientSite.site)⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem observed_rounds_yields (ctx : ProtocolContext) (site : String) (count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : RawState F) (point : List F)
    (decoded : Decodes raw reference) (allowed : GkrRoundsReference.admissible reference) :
    PIR.Yields (fun result => Decodes result.raw result.reference ∧
      GkrRoundsReference.admissible result.reference ∧ ∃ suffix : List F,
      result.point = point ++ suffix ∧ suffix.length = count ∧
      ∀ tail : List F, Rounds.value result.reference (coordinates n tail) =
        Rounds.value reference (coordinates (n + count) (suffix ++ tail)))
      (HonestProducerOccurrences.producerRounds (G := G) ctx site 0 count reference raw point) := by
  apply HonestProducerOccurrences.erased_yields
  rw [HonestProducerOccurrences.producerRounds_erase]
  exact execute_yields ctx count reference raw point decoded allowed

theorem coefficient_protocols (ctx : ProtocolContext) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G))) :
    coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      observedHelpers self protocols ctx Occurrence.iterations) =
    coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
      observedHelpers self [] ctx Occurrence.iterations) := by
  rfl


set_option maxHeartbeats 2000000 in
/-- The actual current layer callback computes the observed honest layer,
including its two nested Rounds calls and coefficient occurrence boundaries. -/
theorem layer_actual
    (encoding : CircuitEncoding F) (shape : encoding.Shape) (index : Nat)
    (inside : index < encoding.layers) (point : List F) (pointSize : point.length = encoding.width)
    (widthBound : encoding.width ≤ 4) (layersBound : encoding.layers < indexLimit)
    (small : encoding.width + encoding.width + encoding.width + encoding.selector < 64)
    (addBound : encoding.add.length < indexLimit) (mulBound : encoding.mul.length < indexLimit)
    (roundCapacity : 2 ^ (encoding.width + encoding.width) < indexLimit)
    (lineCapacity : 2 ^ encoding.width * (encoding.width + 1) < indexLimit) :
    layerBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers 0 beforeRoot {} Occurrence.iterations)
      (((SourceRows.LayerArguments.pack {
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
        })) : Values (Component (assignment F G))
          (.index :: (layerSpec.state ++ layerSpec.captures))).get =
      (HonestProducerObservedLayers.producerLayer {} currentLayerSites encoding.circuit
        (encoding.layers - index - 1) index point).bind
          (fun result => .done (proverLayerState (some result))) := by
  have belowDecoded := GkrRoundsLayout.decode_encode
    (encoding.circuit.wires (encoding.layers - index - 1) (index + 1))
  have position : index < 2 ^ encoding.selector := lt_of_lt_of_le inside shape.2.2.2
  have widthSmall : encoding.width + encoding.width + encoding.width < 64 := by omega
  have leftSeparate : (GkrVerifier.leftContext ({} : ProtocolContext)).roles 1 ≠ (GkrVerifier.leftContext ({} : ProtocolContext)).roles 0 := by
    simp [GkrVerifier.leftContext, ProtocolContext.enter, roleSubstitution]
  have rightSeparate : (GkrVerifier.rightContext ({} : ProtocolContext)).roles 1 ≠ (GkrVerifier.rightContext ({} : ProtocolContext)).roles 0 := by
    simp [GkrVerifier.rightContext, ProtocolContext.enter, roleSubstitution]
  have pointBound : encoding.width < indexLimit := by simp only [indexLimit]; omega
  have lineBound : encoding.width + 1 < indexLimit := by simp only [indexLimit]; omega
  have smaller : 2 ^ encoding.width < indexLimit :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)).trans_lt roundCapacity
  have normalized := layerPresentation_equation (F := F) (G := G) {} (.root _ _)
    beforeRoot beforeRoot_masked index (some point) (some encoding.inputs)
    (some encoding.add) (some encoding.mul) (some encoding.layers)
    (some encoding.selector) (some encoding.width) none
  refine normalized.trans ?_
  dsimp only [layerPresentation, layerPresentation_certificate]
  simp only [NormalForm.runsAtOn, NormalForm.meaningAtOn,
    Participant.owned, RoleFamily.sequence, ProtocolContext.roles,
    PIR.Process.bind, PIR.Process.bind_assoc]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, HonestCircuit.values_below_plain encoding.add encoding.mul encoding.inputs
      encoding.layers encoding.selector index encoding.circuit (add_stack encoding shape)
      (mul_stack encoding shape) (encoding.inputs_decode shape) shape.2.2.2 small layersBound inside]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, selectBlock_plain encoding.add index encoding.selector _ shape.2.1
      (by positivity) position addBound]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, selectBlock_plain encoding.mul index encoding.selector _ shape.2.2.1
      (by positivity) position mulBound]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, HonestHelpers.layout_plain _ _ _ point (encoding.circuit.add index)
      (encoding.circuit.mul index) _ (encoding.add_decode shape index inside)
      (encoding.mul_decode shape index inside) belowDecoded pointSize widthSmall]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  let reference := Circuit.factors encoding.circuit (encoding.layers - index - 1) index
    (coordinates encoding.width point)
  change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (GkrVerifier.leftContext {}) 0
    ((SourceRows.RoundsInputs.pack {
        add := some (encode reference).add,
        mul := some (encode reference).mul,
        left := some (encode reference).left,
        right := some (encode reference).right,
        pending := none,
        claim := none,
        count := some encoding.width,
        service := none
      }))).bind _ = _
  erw [rounds_observed (GkrVerifier.leftContext {}) rfl rfl encoding.width widthBound reference
    (encode reference) (encode_decodes reference) roundCapacity, PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, SourceRows.roundsResult, values, Values.append, Values.present]
  unfold HonestProducerObservedLayers.producerLayer
  dsimp only
  rw [PIR.Process.bind_assoc]
  apply (observed_rounds_yields (G := G) (GkrVerifier.leftContext {}) currentLayerSites.left encoding.width reference
    (encode reference) [] (encode_decodes reference) (Circuit.factors_admissible _ _ _ _)).bind_congr
  rintro left ⟨leftDecoded, leftAllowed, leftSuffix, leftPoint, leftSize, _⟩
  have leftLength : left.point.length = encoding.width := by simp_all
  let rightReference : GkrRoundsReference.State F (0 + encoding.width) :=
    (Nat.zero_add encoding.width).symm ▸ left.reference
  have rightDecoded := cast_decodes (Nat.zero_add encoding.width).symm left.reference left.raw leftDecoded
  have rightAllowed := cast_admissible (Nat.zero_add encoding.width).symm left.reference leftAllowed
  change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (GkrVerifier.rightContext {}) 0
    ((SourceRows.RoundsInputs.pack {
        add := some left.raw.add,
        mul := some left.raw.mul,
        left := some left.raw.left,
        right := some left.raw.right,
        pending := none,
        claim := none,
        count := some encoding.width,
        service := none
      }))).bind _ = _
  erw [rounds_observed (GkrVerifier.rightContext {}) rfl rfl encoding.width widthBound rightReference
    left.raw rightDecoded (by simpa only [Nat.zero_add] using smaller), PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, SourceRows.roundsResult, values, Values.append, Values.present]
  rw [PIR.Process.bind_assoc]
  apply (observed_rounds_yields (G := G) (GkrVerifier.rightContext {}) currentLayerSites.right encoding.width
    rightReference left.raw [] rightDecoded rightAllowed).bind_congr
  rintro right ⟨_, _, rightSuffix, rightPoint, rightSize, _⟩
  have rightLength : right.point.length = encoding.width := by simp_all
  simp only [Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, HonestLine.coefficients_plain encoding.width _ left.point right.point _
      belowDecoded leftLength rightLength lineCapacity]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, HonestHelpers.element_plain _ 0 (by simpa only [Values.get, line, row_length] using lineBound) (by decide)]
  dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.get]
  change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
    (Values (Component (assignment F G)) layerSpec.state)
    (.action (.send (ty := .field scalarDomain) (GkrVerifier.lineConstantSite {}) 1 _)) _ = _
  simp only [PIR.Process.interpret, PIR.Process.bind, Occurrence.actions, PIR.Process.bind_assoc]
  apply congrArg (PIR.Process.call _)
  funext result
  cases result
  set_option backward.isDefEq.respectTransparency true in
  change (denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec {} 0
    (some encoding.width) proverCoefficientState
    ((SourceRows.CoefficientCaptures.pack {
        line := some (line (encoding.circuit.wires (encoding.layers - index - 1) (index + 1)) left.point right.point)
      }))
    (fun args => coefficientBody.denote
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get)
    Occurrence.iterations (coefficientSite.site)).bind _ = _
  rw [coefficient_protocols]
  erw [coefficients_observed (F := F) (G := G) ({} : ProtocolContext) (by decide) (coefficientSite.site) _
    encoding.width widthBound (by simpa only [line, row_length] using lineBound), PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, currentLayerSites]
  apply congrArg (PIR.Process.bind _)
  funext coefficientResult
  change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
    (Values (Component (assignment F G)) layerSpec.state)
    (.action (.receive (.field scalarDomain) (GkrVerifier.lineDeliverySite {}) 1)) _ = _
  apply congrArg (PIR.Process.call _)
  funext challenge
  conv_lhs =>
    arg 1
    erw [OccurrencePresentation.closed_helper, linePoint_plain left.point right.point challenge
      (by rw [leftLength, rightLength]) (by rw [leftLength]; exact pointBound)]
  rfl
end ZkcSecurity.Realizations.Gkr.HonestProducerSource
