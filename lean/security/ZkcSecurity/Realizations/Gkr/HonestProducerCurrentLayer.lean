module

public import ZkcSecurity.Realizations.Gkr.HonestProducerSource
public import Zkc.Source.DeriveRegion

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
namespace ZkcSecurity.Realizations.Gkr.HonestProducerSource
open Zkc Source Structured ZkcExamples.Structured
variable {F G : Type} [Field F] [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G]


open GkrSourceCallbacks
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcSecurity.Examples.Components
open GkrSourceLaws SumcheckVerifierHelpers HonestProducerRounds HonestProducerPackets

abbrev currentLayerSites : HonestProducerObservedLayers.Sites :=
  ⟨qualifyProtocolSite (leftContext {}).applicationPrefix "s9",
    qualifyProtocolSite (rightContext {}).applicationPrefix "s9", "s91"⟩

omit [AddCommGroup G] [Module F G] [DecidableEq F] [DecidableEq G] in
theorem observed_rounds_yields (ctx : ProtocolContext) (site : String) (count : Nat) {n : Nat}
    (reference : GkrRoundsReference.State F (n + count)) (raw : Raw F) (point : List F)
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


theorem coefficient_derivation (ctx : ProtocolContext) (self : Nat)
    (protocols : ProtocolTable (assignment F G) (Occurrence.signature (uniformCarriers F G)))
    (args : Values (Component (assignment F G))
      (.index :: (coefficientSpec.state ++ coefficientSpec.captures))) :
    Region.Derivation
      (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
        observedHelpers self protocols ctx Occurrence.iterations)
      (fun op => .call op .done) coefficientBody args.get
      (coefficientBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions
          observedHelpers self protocols ctx Occurrence.iterations) args.get) := by
  exact Region.Derivation.identity _ _ _

attribute [local irreducible] coefficientBody

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
      ((.cons (some index) ((proverLayerState (G := G) (some point)).append
        (.cons (some encoding.inputs) (.cons (some encoding.add) (.cons (some encoding.mul)
          (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
            (.cons none .nil))))))))) : Values (Component (assignment F G))
          (.index :: (layerSpec.state ++ layerSpec.captures))).get =
      (HonestProducerObservedLayers.producerLayer {} currentLayerSites encoding.circuit
        (encoding.layers - index - 1) index point).bind
          (fun result => .done (proverLayerState (some result))) := by
  have belowDecoded := GkrRoundsLayout.decode_encode
    (encoding.circuit.wires (encoding.layers - index - 1) (index + 1))
  have position : index < 2 ^ encoding.selector := lt_of_lt_of_le inside shape.2.2.2
  have widthSmall : encoding.width + encoding.width + encoding.width < 64 := by omega
  have leftSeparate : (leftContext ({} : ProtocolContext)).roles 1 ≠ (leftContext ({} : ProtocolContext)).roles 0 := by
    simp [leftContext, ProtocolContext.enter, roleSubstitution]
  have rightSeparate : (rightContext ({} : ProtocolContext)).roles 1 ≠ (rightContext ({} : ProtocolContext)).roles 0 := by
    simp [rightContext, ProtocolContext.enter, roleSubstitution]
  have pointBound : encoding.width < indexLimit := by simp only [indexLimit]; omega
  have lineBound : encoding.width + 1 < indexLimit := by simp only [indexLimit]; omega
  have smaller : 2 ^ encoding.width < indexLimit :=
    (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)).trans_lt roundCapacity
  trans ?_
  · derive_process
    exact coefficient_derivation {} 0 beforeRoot _
  ·
    change ((invoke observedHelpers.closed GkrSourceBodies.helper34Helper
      (.cons encoding.add (.cons encoding.mul (.cons encoding.inputs (.cons encoding.layers
        (.cons encoding.selector (.cons encoding.width (.cons index .nil)))))))).bind
          (fun result => .done result.present)).bind _ = _
    erw [observed_helper, HonestCircuit.values_below_plain encoding.add encoding.mul encoding.inputs
      encoding.layers encoding.selector index encoding.circuit (add_stack encoding shape)
      (mul_stack encoding shape) (encoding.inputs_decode shape) shape.2.2.2 small layersBound inside]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append, ProtocolOp.results]
    change ((invoke observedHelpers.closed GkrSourceBodies.selectBlockHelper
      (.cons encoding.add (.cons index (.cons encoding.selector .nil)))).bind
        (fun result => .done result.present)).bind _ = _
    erw [observed_helper, selectBlock_plain encoding.add index encoding.selector _ shape.2.1
      (by positivity) position addBound]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append, ProtocolOp.results]
    change ((invoke observedHelpers.closed GkrSourceBodies.selectBlockHelper
      (.cons encoding.mul (.cons index (.cons encoding.selector .nil)))).bind
        (fun result => .done result.present)).bind _ = _
    erw [observed_helper, selectBlock_plain encoding.mul index encoding.selector _ shape.2.2.1
      (by positivity) position mulBound]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append, ProtocolOp.results]
    change ((invoke observedHelpers.closed GkrSourceBodies.helper36Helper
      (.cons (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width)))
        (.cons (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width)))
          (.cons point (.cons (GkrRoundsLayout.encode
            (encoding.circuit.wires (encoding.layers - index - 1) (index + 1)))
            (.cons encoding.width .nil)))))).bind (fun result => .done result.present)).bind _ = _
    erw [observed_helper, HonestHelpers.layout_plain _ _ _ point (encoding.circuit.add index)
      (encoding.circuit.mul index) _ (encoding.add_decode shape index inside)
      (encoding.mul_decode shape index inside) belowDecoded pointSize widthSmall]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append, ProtocolOp.results]
    let reference := Circuit.factors encoding.circuit (encoding.layers - index - 1) index
      (coordinates encoding.width point)
    change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (leftContext {}) 0
      (.cons (some (encode reference).add) (.cons (some (encode reference).mul)
        (.cons (some (encode reference).left) (.cons (some (encode reference).right)
          (.cons none (.cons none (.cons (some encoding.width) (.cons none .nil))))))))).bind _ = _
    erw [rounds_observed (leftContext {}) rfl rfl encoding.width widthBound reference
      (encode reference) (encode_decodes reference) roundCapacity, PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, returned, values, Values.append, Values.present]
    unfold HonestProducerObservedLayers.producerLayer
    dsimp only
    rw [PIR.Process.bind_assoc]
    apply (observed_rounds_yields (G := G) (leftContext {}) currentLayerSites.left encoding.width reference
      (encode reference) [] (encode_decodes reference) (Circuit.factors_admissible _ _ _ _)).bind_congr
    rintro left ⟨leftDecoded, leftAllowed, leftSuffix, leftPoint, leftSize, _⟩
    have leftLength : left.point.length = encoding.width := by simp_all
    let rightReference : GkrRoundsReference.State F (0 + encoding.width) :=
      (Nat.zero_add encoding.width).symm ▸ left.reference
    have rightDecoded := cast_decodes (Nat.zero_add encoding.width).symm left.reference left.raw leftDecoded
    have rightAllowed := cast_admissible (Nat.zero_add encoding.width).symm left.reference leftAllowed
    change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (rightContext {}) 0
      (.cons (some left.raw.add) (.cons (some left.raw.mul)
        (.cons (some left.raw.left) (.cons (some left.raw.right)
          (.cons none (.cons none (.cons (some encoding.width) (.cons none .nil))))))))).bind _ = _
    erw [rounds_observed (rightContext {}) rfl rfl encoding.width widthBound rightReference
      left.raw rightDecoded (by simpa only [Nat.zero_add] using smaller), PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, returned, values, Values.append, Values.present]
    rw [PIR.Process.bind_assoc]
    apply (observed_rounds_yields (G := G) (rightContext {}) currentLayerSites.right encoding.width
      rightReference left.raw [] rightDecoded rightAllowed).bind_congr
    rintro right ⟨_, _, rightSuffix, rightPoint, rightSize, _⟩
    have rightLength : right.point.length = encoding.width := by simp_all
    change ((invoke observedHelpers.closed GkrSourceBodies.helper69Helper
      (.cons (GkrRoundsLayout.encode (encoding.circuit.wires (encoding.layers - index - 1) (index + 1)))
        (.cons left.point (.cons right.point (.cons encoding.width .nil))))).bind
          (fun result => .done result.present)).bind _ = _
    erw [observed_helper, HonestLine.coefficients_plain encoding.width _ left.point right.point _
      belowDecoded leftLength rightLength lineCapacity]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append, ProtocolOp.results]
    change ((invoke observedHelpers.closed GkrSourceBodies.helper57Helper
      (.cons (line (encoding.circuit.wires (encoding.layers - index - 1) (index + 1)) left.point right.point)
        (.cons 0 .nil))).bind (fun result => .done result.present)).bind _ = _
    erw [observed_helper, HonestHelpers.element_plain _ 0 (by simpa only [line, row_length] using lineBound) (by decide)]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append, ProtocolOp.results]
    change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) layerSpec.state)
      (.action (.send (ty := .field scalarDomain) (lineConstantSite {}) 1 _)) _ = _
    simp only [PIR.Process.interpret, PIR.Process.bind, Occurrence.actions, PIR.Process.bind_assoc]
    apply congrArg (PIR.Process.call _)
    funext result
    cases result
    set_option backward.isDefEq.respectTransparency true in
    change (denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec {} 0
      (some encoding.width) proverCoefficientState
      (.cons (some (line (encoding.circuit.wires (encoding.layers - index - 1) (index + 1)) left.point right.point)) .nil)
      (fun args => coefficientBody.denote
        (participantMeaningWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 0 beforeRoot {} Occurrence.iterations) args.get)
      Occurrence.iterations "s91").bind _ = _
    rw [coefficient_protocols]
    erw [coefficients_observed (F := F) (G := G) ({} : ProtocolContext) (by decide) "s91" _
      encoding.width widthBound (by simpa only [line, row_length] using lineBound), PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, currentLayerSites]
    apply congrArg (PIR.Process.bind _)
    funext coefficientResult
    try dsimp only [Values.present, Values.append, Values.absent, ProtocolOp.results, PIR.Process.bind, PIR.Process.interpret]
    change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) layerSpec.state)
      (.action (.receive (.field scalarDomain) (lineDeliverySite {}) 1)) _ = _
    apply congrArg (PIR.Process.call _)
    funext challenge
    try dsimp only [PIR.Process.bind, PIR.Process.interpret, Values.append, Values.present]
    change ((invoke observedHelpers.closed GkrSourceBodies.linePointHelper
      (.cons left.point (.cons right.point (.cons challenge .nil)))).bind
      (fun result => .done result.present)).bind _ = _
    erw [observed_helper, linePoint_plain left.point right.point challenge
      (by rw [leftLength, rightLength]) (by rw [leftLength]; exact pointBound)]
    rfl
end ZkcSecurity.Realizations.Gkr.HonestProducerSource
