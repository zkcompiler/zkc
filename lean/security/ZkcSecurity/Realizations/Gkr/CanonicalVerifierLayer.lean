module

public import ZkcSecurity.Realizations.Gkr.CanonicalVerifierRounds
public import ZkcExamples.Structured.SumcheckVerifierHelpers
public import ZkcExamples.Structured.GkrVerifierProcess
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
  have normalized := verifierLayer_observed (F := F) (G := G) {} (.root _ _)
    beforeRoot beforeRoot_masked index (some point) (some claim) (some encoding.inputs)
    (some encoding.add) (some encoding.mul) (some encoding.layers)
    (some encoding.selector) (some encoding.width) (some handle)
  refine normalized.trans ?_
  simp only [verifierLayerForm, NormalForm.Form.denoteOn, NormalForm.Form.denoteWithOn,
    NormalForm.Comps.eval, NormalForm.Comp.eval, NormalForm.Term.eval, NormalForm.Terms.eval,
    NormalForm.Arguments.eval, NormalForm.Argument.eval, NormalForm.entryAt, NormalForm.firstEntry, NormalForm.laterEntries, Op.evalTotal,
    NormalForm.runsAtOn, NormalForm.meaningAtOn, ProtocolPresentation.callees,
    NormalForm.calleeAt, NormalForm.InputPattern.environment, Bindings.optionalPattern,
    Generated.Presentations.Gkr.calleeKeys, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Participant.owned, RoleFamily.sequence,
    ProtocolContext.roles, PIR.Process.bind, PIR.Process.bind_assoc]
  erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.sourceHelper20Helper (.cons point (.cons claim .nil))]
  rw [tuple20_plain (F := F) (G := G) point claim]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.present,
    NormalForm.firstEntry, NormalForm.laterEntries, Values.get]
  erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.sourceHelper37Helper (.cons claim .nil)]
  rw [pending_plain (F := F) (G := G) claim]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.present,
    NormalForm.firstEntry, NormalForm.laterEntries, Values.get]
  change (invokeProtocol beforeRoot GkrSourceBodies.roundsSignature (GkrVerifier.leftContext {}) 1
    (.cons none (.cons none (.cons none (.cons none (.cons (some [])
      (.cons (some claim) (.cons (some encoding.width) (.cons (some handle) .nil))))))))).bind _ = _
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
    (.cons none (.cons none (.cons none (.cons none (.cons (some left.1)
      (.cons (some left.2) (.cons (some encoding.width) (.cons (some handle) .nil))))))))).bind _ = _
  erw [rounds_reads (GkrVerifier.rightContext {}) rfl rfl handle encoding.width widthBound left.1 left.2,
    PIR.Process.bind_assoc]
  simp only [PIR.Process.bind, GkrRoundsReading.roundsResults, TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Values.append,
    Values.present]
  conv_rhs => rw [PIR.Process.bind_assoc]
  apply (rounds_yields (G := G) (GkrVerifier.rightContext {}) handle currentLayerSites.right
    encoding.width left.2).bind_congr
  intro right rightSize
  erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.sourceHelper40Helper (.cons (left.1 ++ right.1) (.cons right.2 .nil))]
  rw [GkrRoundsReading.tuple40_plain (F := F) (G := G) (left.1 ++ right.1) right.2]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.present,
    NormalForm.firstEntry, NormalForm.laterEntries, Values.get]
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.sourceHelper50Helper
    (.cons (left.1 ++ right.1) .nil)).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.sourceHelper50Helper
    (.cons (left.1 ++ right.1) .nil)]
  rw [split_pending_plain (F := F) (G := G) left.1 right.1
    (by rw [leftSize, rightSize]) (by rw [List.length_append, leftSize, rightSize]; unfold indexLimit; omega)]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
  change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
    (Values (Component (assignment F G)) layerSpec.state)
    (.action (.receive (.field scalarDomain) (GkrVerifier.lineConstantSite {}) 0)) _ = _
  simp only [PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
  apply congrArg (PIR.Process.call _)
  funext first
  change F at first
  erw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.emptyHelper .nil]
  rw [GkrRoundsReading.empty_plain (F := F) (G := G)]
  simp only [PIR.Process.interpret, PIR.Process.bind, Values.present,
    NormalForm.firstEntry, NormalForm.laterEntries, Values.get]
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.appendHelper
    (.cons [] (.cons first .nil))).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.appendHelper
    (.cons [] (.cons first .nil))]
  rw [GkrRoundsReading.append_plain]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
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
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.sumHelper
    (.cons coefficients .nil)).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.sumHelper
    (.cons coefficients .nil)]
  rw [sum_plain]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.selectBlockHelper
    (.cons encoding.add (.cons index (.cons encoding.selector .nil)))).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.selectBlockHelper
    (.cons encoding.add (.cons index (.cons encoding.selector .nil)))]
  rw [GkrLayerReading.selectBlock_plain encoding.add index encoding.selector _
    admitted.1.2.1 positive position addBound]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.evaluateWiringHelper
    (.cons (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width)))
      (.cons point (.cons left.1 (.cons right.1 .nil))))).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.evaluateWiringHelper
    (.cons (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width)))
      (.cons point (.cons left.1 (.cons right.1 .nil))))]
  rw [evaluateWiring_plain encoding.width
    (block encoding.add index (2 ^ (encoding.width + encoding.width + encoding.width))) point left.1 right.1
    (encoding.circuit.add index) (encoding.add_decode admitted.1 index inside)
    pointSize leftSize rightSize small addBlock]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.selectBlockHelper
    (.cons encoding.mul (.cons index (.cons encoding.selector .nil)))).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.selectBlockHelper
    (.cons encoding.mul (.cons index (.cons encoding.selector .nil)))]
  rw [GkrLayerReading.selectBlock_plain encoding.mul index encoding.selector _
    admitted.1.2.2.1 positive position mulBound]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
  change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.evaluateWiringHelper
    (.cons (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width)))
      (.cons point (.cons left.1 (.cons right.1 .nil))))).bind _ = _
  rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
    GkrSourceBodies.evaluateWiringHelper
    (.cons (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width)))
      (.cons point (.cons left.1 (.cons right.1 .nil))))]
  rw [evaluateWiring_plain encoding.width
    (block encoding.mul index (2 ^ (encoding.width + encoding.width + encoding.width))) point left.1 right.1
    (encoding.circuit.mul index) (encoding.mul_decode admitted.1 index inside)
    pointSize leftSize rightSize small mulBlock]
  try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
    TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
  let addValue := extension (encoding.width + encoding.width + encoding.width)
    (encoding.circuit.add index) (coordinates (encoding.width + encoding.width + encoding.width)
      (point ++ left.1 ++ right.1))
  let mulValue := extension (encoding.width + encoding.width + encoding.width)
    (encoding.circuit.mul index) (coordinates (encoding.width + encoding.width + encoding.width)
      (point ++ left.1 ++ right.1))
  dsimp +instances only [TypedABI.get_cons_here, TypedABI.get_cons_there]
  by_cases check : right.2 = GkrVerifier.wiringValue addValue mulValue first coefficients.sum
  · rw [lineCheck_pos {} handle encoding.width (encoding.circuit.add index) (encoding.circuit.mul index)
      (index, point, claim) left.1 right.1 right.2 first coefficients check]
    simp only [GkrVerifier.wiringValue, addValue, mulValue] at check
    try dsimp +instances only [TypedABI.get_cons_here, TypedABI.get_cons_there]
    simp only [protocolOperationWithOn, Participant.guard, ProtocolContext.roles,
      TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, GkrVerifier.wiringValue, addValue, mulValue,
      check, decide_true, ite_true, PIR.Process.interpret, PIR.Process.bind, id_eq]
    change @PIR.Process.call (Occurrence.signature (uniformCarriers F G))
      (Values (Component (assignment F G)) layerSpec.state)
      (.action (.query (GkrVerifier.lineChallengeSite {}) scalarDomain (.cons handle .nil))) _ = _
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
    change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.linePointHelper
      (.cons left.1 (.cons right.1 (.cons challenge .nil)))).bind _ = _
    rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.linePointHelper
      (.cons left.1 (.cons right.1 (.cons challenge .nil)))]
    rw [GkrLayerReading.linePoint_plain left.1 right.1 challenge
      (by rw [leftSize, rightSize]) pointsBound]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.evaluateCoefficientsHelper
      (.cons coefficients (.cons challenge .nil))).bind _ = _
    rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.evaluateCoefficientsHelper
      (.cons coefficients (.cons challenge .nil))]
    rw [GkrLayerReading.evaluateCoefficients_plain coefficients challenge coefficientsBound]
    try dsimp only [PIR.Process.interpret, PIR.Process.bind, Values.present, Values.append,
      TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, Environment.prepend, Environment.push, ProtocolOp.results]
    change (invoke (observedHelpers (F := F) (G := G)).closed GkrSourceBodies.sourceHelper19Helper
      (.cons (linePoints left.1 right.1 challenge) (.cons (powerSum coefficients challenge) .nil))).bind _ = _
    rw [OccurrencePresentation.closed_helper (F := F) (G := G) GkrSourceViews.unit
      GkrSourceBodies.sourceHelper19Helper
      (.cons (linePoints left.1 right.1 challenge) (.cons (powerSum coefficients challenge) .nil))]
    rw [tuple19_plain]
    rfl
  · rw [lineCheck_neg {} handle encoding.width (encoding.circuit.add index) (encoding.circuit.mul index)
      (index, point, claim) left.1 right.1 right.2 first coefficients check]
    simp only [GkrVerifier.wiringValue, addValue, mulValue] at check
    simp only [protocolOperationWithOn, Participant.guard, ProtocolContext.roles,
      TypedABI.get_cons_here, TypedABI.get_cons_there, Values.get, GkrVerifier.wiringValue, addValue, mulValue,
      check, decide_false, ite_true, Bool.false_eq_true, ite_false,
      PIR.Process.interpret, PIR.Process.bind, id_eq]

end ZkcSecurity.Realizations.Gkr.CanonicalVerifier
