module

public import ZkcSecurity.Realizations.Gkr.CanonicalVerifierRounds
public import ZkcSecurity.Realizations.Gkr.CanonicalVerifierCoefficients
public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrentLayer
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
open ZkcExamples.Structured GkrSourceCallbacks GkrSourceLaws
open SumcheckVerifierHelpers HonestProducerSource HonestProducerOccurrences
open GkrLayerReading
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

attribute [local irreducible] coefficientBody

private theorem add_calculation (a b : F) :
    protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldAdd scalarDomain) rfl) (.cons (some a) (.cons (some b) .nil))
      .nil beforeRoot {} Occurrence.iterations = .done (.cons (some (a + b)) .nil) := by rfl

private theorem multiply_calculation (a b : F) :
    protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldMultiply scalarDomain) rfl) (.cons (some a) (.cons (some b) .nil))
      .nil beforeRoot {} Occurrence.iterations = .done (.cons (some (a * b)) .nil) := by rfl

private theorem equal_calculation (a b : F) :
    protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldEqual scalarDomain) rfl) (.cons (some a) (.cons (some b) .nil))
      .nil beforeRoot {} Occurrence.iterations = .done (.cons (some (decide (a = b))) .nil) := by rfl

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
theorem layer_reads (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (handle index : Nat)
    (inside : index < encoding.layers) (point : List F) (claim : F)
    (pointSize : point.length = encoding.width) :
    layerBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
      Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations)
      ((.cons (some index) ((verifierLayerState (G := G) (some point) (some claim)).append
        (.cons (some encoding.inputs) (.cons (some encoding.add) (.cons (some encoding.mul)
          (.cons (some encoding.layers) (.cons (some encoding.selector) (.cons (some encoding.width)
            (.cons (some handle) .nil))))))))) : Values (Component (assignment F G))
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
  trans ?_
  · derive_process
    exact coefficient_derivation {} 1 beforeRoot _
  ·
    change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (leftContext {}) 1
      (.cons none (.cons none (.cons none (.cons none (.cons (some [])
        (.cons (some claim) (.cons (some encoding.width) (.cons (some handle) .nil))))))))).bind _ = _
    erw [rounds_reads (leftContext {}) rfl rfl handle encoding.width widthBound [] claim,
      PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, Values.get, Values.append,
      Values.present, List.nil_append]
    unfold HonestProducerObservedLayers.validatorLayer
    rw [PIR.Process.bind_assoc]
    apply (rounds_yields (G := G) (leftContext {}) handle currentLayerSites.left
      encoding.width claim).bind_congr
    intro left leftSize
    change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (rightContext {}) 1
      (.cons none (.cons none (.cons none (.cons none (.cons (some left.1)
        (.cons (some left.2) (.cons (some encoding.width) (.cons (some handle) .nil))))))))).bind _ = _
    erw [rounds_reads (rightContext {}) rfl rfl handle encoding.width widthBound left.1 left.2,
      PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, Values.get, Values.append,
      Values.present]
    conv_rhs => rw [PIR.Process.bind_assoc]
    apply (rounds_yields (G := G) (rightContext {}) handle currentLayerSites.right
      encoding.width left.2).bind_congr
    intro right rightSize
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.sourceHelper50Helper
      (.cons (left.1 ++ right.1) .nil)).bind (fun result => .done result.present)).bind _ = _
    erw [observed_helper, split_pending_plain left.1 right.1
      (by rw [leftSize, rightSize]) (by rw [List.length_append, leftSize, rightSize]; unfold indexLimit; omega)]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) layerSpec.state)
      (.action (.receive (.field scalarDomain) (lineConstantSite {}) 0)) _ = _
    simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
    apply congrArg (PIR.Process.call _)
    funext first
    change F at first
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.appendHelper
      (.cons [] (.cons first .nil))).bind (fun result => .done result.present)).bind _ = _
    erw [observed_helper, GkrRoundsReading.append_plain]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change (denoteRepeatOn (carriers := uniformCarriers F G) coefficientSpec {} 1
      (some encoding.width) (verifierCoefficientState (some [first])) (.cons none .nil)
      (fun args => coefficientBody.denote (participantMeaningWithOn (ringModel F G) (.silent _)
        Occurrence.actions observedHelpers 1 beforeRoot {} Occurrence.iterations) args.get)
      Occurrence.iterations "s91").bind _ = _
    rw [coefficient_protocols]
    erw [coefficients_repeat (F := F) (G := G) ({} : ProtocolContext) (by decide) "s91"
      encoding.width widthBound [first], PIR.Process.bind_assoc]
    simp only [PIR.Process.bind, verifierCoefficientState, Values.get]
    have coefficientsYield : PIR.Yields (fun coefficients : List F =>
        coefficients.length = encoding.width + 1)
        (HonestProducerObservedLayers.validatorCoefficients (G := G) {} "s91" 0 encoding.width [first]) := by
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
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.sumHelper
      (.cons coefficients .nil)).bind (fun result => .done result.present)).bind _ = _
    erw [observed_helper, sum_plain]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.selectBlockHelper
      (.cons encoding.add (.cons index (.cons encoding.selector .nil)))).bind
        (fun result => .done result.present)).bind _ = _
    erw [observed_helper, GkrLayerReading.selectBlock_plain encoding.add index encoding.selector _
      admitted.1.2.1 positive position addBound]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.evaluateWiringHelper
      (.cons (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width)))
        (.cons point (.cons left.1 (.cons right.1 .nil))))).bind
        (fun result => .done result.present)).bind _ = _
    erw [observed_helper, evaluateWiring_plain encoding.width _ point left.1 right.1
      (encoding.circuit.add index) (encoding.add_decode admitted.1 index inside)
      pointSize leftSize rightSize small addBlock]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.selectBlockHelper
      (.cons encoding.mul (.cons index (.cons encoding.selector .nil)))).bind
        (fun result => .done result.present)).bind _ = _
    erw [observed_helper, GkrLayerReading.selectBlock_plain encoding.mul index encoding.selector _
      admitted.1.2.2.1 positive position mulBound]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.evaluateWiringHelper
      (.cons (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width)))
        (.cons point (.cons left.1 (.cons right.1 .nil))))).bind
        (fun result => .done result.present)).bind _ = _
    erw [observed_helper, evaluateWiring_plain encoding.width _ point left.1 right.1
      (encoding.circuit.mul index) (encoding.mul_decode admitted.1 index inside)
      pointSize leftSize rightSize small mulBlock]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    let addValue := extension (encoding.width + encoding.width + encoding.width)
      (encoding.circuit.add index) (coordinates (encoding.width + encoding.width + encoding.width)
        (point ++ left.1 ++ right.1))
    let mulValue := extension (encoding.width + encoding.width + encoding.width)
      (encoding.circuit.mul index) (coordinates (encoding.width + encoding.width + encoding.width)
        (point ++ left.1 ++ right.1))
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldAdd scalarDomain) rfl)
      (.cons (some first) (.cons (some coefficients.sum) .nil)) .nil beforeRoot {} Occurrence.iterations).bind _ = _
    erw [add_calculation]
    dsimp only [PIR.Process.bind]
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldMultiply scalarDomain) rfl)
      (.cons (some addValue) (.cons (some (first + coefficients.sum)) .nil)) .nil
      beforeRoot {} Occurrence.iterations).bind _ = _
    erw [multiply_calculation]
    dsimp only [PIR.Process.bind]
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldMultiply scalarDomain) rfl)
      (.cons (some mulValue) (.cons (some first) .nil)) .nil
      beforeRoot {} Occurrence.iterations).bind _ = _
    erw [multiply_calculation]
    dsimp only [PIR.Process.bind]
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldMultiply scalarDomain) rfl)
      (.cons (some (mulValue * first)) (.cons (some coefficients.sum) .nil)) .nil
      beforeRoot {} Occurrence.iterations).bind _ = _
    erw [multiply_calculation]
    dsimp only [PIR.Process.bind]
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldAdd scalarDomain) rfl)
      (.cons (some (addValue * (first + coefficients.sum)))
        (.cons (some (mulValue * first * coefficients.sum)) .nil)) .nil
      beforeRoot {} Occurrence.iterations).bind _ = _
    erw [add_calculation]
    dsimp only [PIR.Process.bind]
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.calculate (.fieldEqual scalarDomain) rfl)
      (.cons (some right.2) (.cons (some (GkrVerifier.wiringValue addValue mulValue first coefficients.sum)) .nil))
      .nil beforeRoot {} Occurrence.iterations).bind _ = _
    erw [equal_calculation]
    dsimp only [PIR.Process.bind]
    change (protocolOperationWithOn (ringModel F G) (.silent _) Occurrence.actions observedHelpers 1
      (.guard 1 "s120")
      (.cons (some (decide (right.2 = GkrVerifier.wiringValue addValue mulValue first coefficients.sum))) .nil)
      .nil beforeRoot {} Occurrence.iterations).bind _ = _
    by_cases check : right.2 = GkrVerifier.wiringValue addValue mulValue first coefficients.sum
    · rw [lineCheck_pos {} handle encoding.width (encoding.circuit.add index) (encoding.circuit.mul index)
        (index, point, claim) left.1 right.1 right.2 first coefficients check]
      simp only [protocolOperationWithOn, Participant.guard, ProtocolContext.roles,
        check, decide_true, ite_true, PIR.Process.interpret, PIR.Process.bind, id_eq]
      change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
        (Values (Component (assignment F G)) layerSpec.state)
        (.action (.query (lineChallengeSite {}) scalarDomain (.cons handle .nil))) _ = _
      simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
      apply congrArg (PIR.Process.call _)
      funext challenge
      change F at challenge
      change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
        (Values (Component (assignment F G)) layerSpec.state)
        (.action (.send (ty := .field scalarDomain) (lineDeliverySite {}) 0 challenge)) _ = _
      simp only [GkrVerifier.lineDelivery, PIR.Process.interpret, CommonAdapter.embed,
        Occurrence.actions, PIR.Process.bind]
      apply congrArg (PIR.Process.call _)
      funext delivered
      change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.linePointHelper
        (.cons left.1 (.cons right.1 (.cons challenge .nil)))).bind
          (fun result => .done result.present)).bind _ = _
      erw [observed_helper, GkrLayerReading.linePoint_plain left.1 right.1 challenge
        (by rw [leftSize, rightSize]) pointsBound]
      try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
        Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
      change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.evaluateCoefficientsHelper
        (.cons coefficients (.cons challenge .nil))).bind
          (fun result => .done result.present)).bind _ = _
      erw [observed_helper, GkrLayerReading.evaluateCoefficients_plain coefficients challenge coefficientsBound]
      try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
        Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
      change ((invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.sourceHelper19Helper
        (.cons (linePoints left.1 right.1 challenge) (.cons (powerSum coefficients challenge) .nil))).bind
          (fun result => .done result.present)).bind _ = _
      erw [observed_helper, tuple19_plain]
      rfl
    · rw [lineCheck_neg {} handle encoding.width (encoding.circuit.add index) (encoding.circuit.mul index)
        (index, point, claim) left.1 right.1 right.2 first coefficients check]
      simp only [protocolOperationWithOn, Participant.guard, ProtocolContext.roles,
        check, decide_false, ite_true, Bool.false_eq_true, ite_false,
        PIR.Process.interpret, PIR.Process.bind, id_eq]

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
