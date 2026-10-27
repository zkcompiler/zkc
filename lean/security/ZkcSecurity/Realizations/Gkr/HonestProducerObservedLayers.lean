module

public import ZkcSecurity.Realizations.Gkr.HonestProducerOccurrences
public import ZkcSecurity.Realizations.Gkr.HonestProducerLayers

@[expose] public section

/-! Honest GKR layer composition with the original construction's actual
nested occurrence frames, complete reached histories and all typed replies. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerObservedLayers
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerRounds
open HonestProducerPackets HonestProducerSource HonestProducerLayers HonestProducerOccurrences

variable {F G : Type} [Field F] [DecidableEq F]

/-- Sites are supplied by the checked current-source body association. They
are neither inferred from old helper numbers nor erased during construction. -/
structure Sites where
  left : String
  right : String
  coefficients : String

structure Routes (routing : Original.Routing) (ctx : ProtocolContext)
    (frames : Original.Frames) (handle : Nat) (sites : Sites)
    extends LineChallengeRoutes routing ctx frames handle where
  left : ∀ index, HonestProducerPair.RoundRoutes routing (GkrSourceCallbacks.leftContext ctx)
    (frames ++ [⟨sites.left, index⟩]) handle
  right : ∀ index, HonestProducerPair.RoundRoutes routing (GkrSourceCallbacks.rightContext ctx)
    (frames ++ [⟨sites.right, index⟩]) handle
  packetOrigin : Nat → Origin
  coefficient : ∀ index, routing.message (frames ++ [⟨sites.coefficients, index⟩])
    (GkrSourceCallbacks.lineCoefficientSite ctx) routing.context.producer routing.context.validator =
      some (packetOrigin index)

def producerCoefficients (ctx : ProtocolContext) (site : String) : Nat → List F →
    PIR.Process (Signature F G) Unit
  | _, [] => .done ()
  | index, value :: rest =>
    (Occurrence.iterations.within site index
      ((@PIR.Process.call (participantInterface F G) Unit (.send (ty := .field "bls12-381.fr")
        (GkrSourceCallbacks.lineCoefficientSite ctx) (ctx.roles 1) value) .done).interpret
          Occurrence.actions)).bind fun _ => producerCoefficients ctx site (index + 1) rest

def validatorCoefficients (ctx : ProtocolContext) (site : String) : Nat → Nat → List F →
    PIR.Process (Signature F G) (List F)
  | _, 0, values => .done values
  | index, count + 1, values =>
    (Occurrence.iterations.within site index
      (((GkrVerifier.lineCoefficient ctx values).interpret CommonAdapter.embed).interpret
        Occurrence.actions)).bind fun next => validatorCoefficients ctx site (index + 1) count next

omit [Field F] [DecidableEq F] in
theorem producerCoefficients_erase (ctx : ProtocolContext) (site : String) (index : Nat) (values : List F) :
    (producerCoefficients (G := G) ctx site index values).interpret Occurrence.erase = sendTail ctx values := by
  induction values generalizing index with
  | nil => rfl
  | cons value rest ih =>
    rw [producerCoefficients, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase]
    simp only [PIR.Process.bind, sendTail]
    congr 1
    funext _
    exact ih (index + 1)

omit [Field F] [DecidableEq F] in
theorem coefficient_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (producer : ctx.roles 0 = routing.context.producer)
    (validatorRole : ctx.roles 1 = routing.context.validator)
    (site : String) (index : Nat) (state : State (F := F) (G := G)) (origins : Nat → Origin)
    (route : ∀ i, routing.message (state.frames ++ [⟨site, i⟩])
      (GkrSourceCallbacks.lineCoefficientSite ctx)
      routing.context.producer routing.context.validator = some (origins i))
    (values coefficients : List F) :
    Readback (fun left right => ∃ history,
      left = ((), { state with history := history }) ∧
      right = (coefficients ++ values, { state with history := history }))
      (Original.fold { routing with mode := .producer } (producerCoefficients ctx site index values) state)
      (Original.fold { routing with mode := .validator }
        (validatorCoefficients ctx site index values.length coefficients) state) := by
  induction values generalizing index coefficients state with
  | nil => exact .done ⟨state.history, rfl, by simp⟩
  | cons value rest ih =>
    rw [producerCoefficients, List.length_cons, validatorCoefficients, Original.fold_bind, Original.fold_bind]
    let entered : State (F := F) (G := G) := { state with frames := state.frames ++ [⟨site, index⟩] }
    have one := HonestProducerLayers.coefficient_pair routing replacement profile ctx producer validatorRole
      entered (origins index) (route index) [value] coefficients
    simp only [sendTail, PIR.repeatN, List.length_cons, List.length_nil, PIR.Process.bind_done,
      HonestProducerPair.validator] at one
    have wrapped := within routing site index state _ _
      (fun left right => ∃ history,
        left = ((), { state with history := history }) ∧
        right = (coefficients ++ [value], { state with history := history }))
      (one.mono (by
        rintro left right ⟨history, rfl, rfl⟩
        exact ⟨rfl, rfl, history, rfl, rfl⟩))
    apply wrapped.bind
    rintro left right ⟨history, rfl, rfl⟩
    apply (ih (index + 1) { state with history := history } route (coefficients ++ [value])).mono
    rintro left right ⟨history, rfl, rfl⟩
    exact ⟨history, rfl, by simp only [List.append_assoc, List.singleton_append]⟩

omit [Field F] [DecidableEq F] in
theorem validatorCoefficients_erase (ctx : ProtocolContext) (site : String)
    (index count : Nat) (coefficients : List F) :
    (validatorCoefficients (G := G) ctx site index count coefficients).interpret Occurrence.erase =
      (PIR.repeatN count (GkrVerifier.lineCoefficient ctx) coefficients).interpret CommonAdapter.embed := by
  induction count generalizing index coefficients with
  | zero => rfl
  | succ count ih =>
    rw [validatorCoefficients, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase, PIR.repeatN, PIR.Process.interpret_bind]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (index + 1) next

noncomputable def producerLayer (ctx : ProtocolContext) (sites : Sites) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat) (point : List F) :
    PIR.Process (Signature F G) (List F) :=
  let reference := Circuit.factors circuit remaining index (coordinates width point)
  (producerRounds (GkrSourceCallbacks.leftContext ctx) sites.left 0 width (n := width)
    reference (encode reference) []).bind fun left =>
  (producerRounds (GkrSourceCallbacks.rightContext ctx) sites.right 0 width (n := 0)
    ((Nat.zero_add width).symm ▸ left.reference) left.raw []).bind fun right =>
  let coefficients := line (circuit.wires remaining (index + 1)) left.point right.point
  ((@PIR.Process.call (participantInterface F G) Unit (.send (ty := .field "bls12-381.fr")
    (GkrSourceCallbacks.lineConstantSite ctx) (ctx.roles 1) ((coefficients)[0]?.getD 0)) .done).interpret
      Occurrence.actions).bind fun _ =>
  (producerCoefficients ctx sites.coefficients 0 (tail coefficients 0 width)).bind fun _ =>
  ((@PIR.Process.call (participantInterface F G) F (.receive (.field "bls12-381.fr")
    (GkrSourceCallbacks.lineDeliverySite ctx) (ctx.roles 1)) .done).interpret Occurrence.actions).bind fun r =>
  .done (linePoints left.point right.point r)

def validatorLayer (ctx : ProtocolContext) (handle width : Nat) (sites : Sites)
    (add mul : Nat → Table F (width + width + width)) (value : Nat × List F × F) :
    PIR.Process (Signature F G) (Nat × List F × F) :=
  (validatorRounds (GkrSourceCallbacks.leftContext ctx) handle sites.left 0 width ([], value.2.2)).bind fun left =>
  (validatorRounds (GkrSourceCallbacks.rightContext ctx) handle sites.right 0 width ([], left.2)).bind fun right =>
  (((@PIR.Process.call (Actions F G) F (.receive (.field "bls12-381.fr")
    (GkrSourceCallbacks.lineConstantSite ctx) (ctx.roles 0)) .done).interpret
      CommonAdapter.embed).interpret Occurrence.actions).bind fun constant =>
  (validatorCoefficients ctx sites.coefficients 0 width [constant]).bind fun coefficients =>
  (((GkrVerifier.lineCheck ctx handle width (add value.1) (mul value.1) value left.1 right.1 right.2 constant coefficients).interpret
    CommonAdapter.embed).interpret Occurrence.actions)

omit [DecidableEq F] in
theorem producerLayer_erase (ctx : ProtocolContext) (sites : Sites) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat) (point : List F) :
    (producerLayer (G := G) ctx sites circuit remaining index point).interpret Occurrence.erase =
      layer ctx circuit remaining index point := by
  unfold producerLayer layer
  simp only [PIR.Process.interpret_bind, producerRounds_erase, actions_erase, producerCoefficients_erase]
  rfl

theorem validatorLayer_erase (ctx : ProtocolContext) (handle width : Nat) (sites : Sites)
    (add mul : Nat → Table F (width + width + width)) (value : Nat × List F × F) :
    (validatorLayer (G := G) ctx handle width sites add mul value).interpret Occurrence.erase =
      (GkrVerifier.layerStep ctx handle width add mul value).interpret CommonAdapter.embed := by
  unfold validatorLayer GkrVerifier.layerStep GkrVerifier.rounds GkrVerifier.layerAfterLeft
    GkrVerifier.layerAfterRight GkrVerifier.layerAfterConstant
  simp only [PIR.Process.interpret_bind, validatorRounds_erase, validatorCoefficients_erase, actions_erase]
  simp only [PIR.Process.interpret, PIR.Process.bind, CommonAdapter.embed, GkrVerifier.rounds,
    PIR.Process.interpret_bind]

theorem layer_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (sites : Sites) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat)
    (point : List F) (pointSize : point.length = width)
    (state : State (F := F) (G := G)) (routes : Routes routing ctx state.frames handle sites) :
    Readback (fun left right => ∃ next history,
      left = (next, { state with history := history }) ∧
      right = ((index + 1, next, extension width (circuit.wires remaining (index + 1))
        (coordinates width next)), { state with history := history }) ∧ next.length = width)
      (Original.fold { routing with mode := .producer }
        (producerLayer ctx sites circuit remaining index point) state)
      (Original.fold { routing with mode := .validator }
        (validatorLayer ctx handle width sites circuit.add circuit.mul
          (index, point, extension width (circuit.wires (remaining + 1) index) (coordinates width point))) state) := by
  let reference := Circuit.factors circuit remaining index (coordinates width point)
  have allowed := Circuit.factors_admissible circuit remaining index (coordinates width point)
  unfold producerLayer validatorLayer
  dsimp only
  rw [Original.fold_bind, Original.fold_bind]
  rw [Circuit.layer_identity]
  apply (frame_left (HonestProducerOccurrences.rounds routing replacement profile (GkrSourceCallbacks.leftContext ctx) handle sites.left 0 width
    reference (encode reference) [] allowed state routes.left)
    (fold_yields _ _ _ (erased_yields _ _ (by
      rw [producerRounds_erase]
      exact execute_yields _ width reference (encode reference) [] (encode_decodes reference) allowed)) state)).bind
  rintro l v ⟨⟨left, leftHistory, rfl, rfl⟩, leftDecoded, leftAllowed,
    leftSuffix, leftPoint, leftSize, leftAnchor⟩
  have leftLength : left.point.length = width := by simp_all
  have leftPointEq : left.point = leftSuffix := by simpa only [List.nil_append] using leftPoint
  let afterLeft : State (F := F) (G := G) := { state with history := leftHistory }
  let rightReference : GkrRoundsReference.State F (0 + width) := (Nat.zero_add width).symm ▸ left.reference
  have rightDecoded := cast_decodes (Nat.zero_add width).symm left.reference left.raw leftDecoded
  have rightAllowed := cast_admissible (Nat.zero_add width).symm left.reference leftAllowed
  simp only [Original.fold_bind]
  have pairedRight := HonestProducerOccurrences.rounds (F := F) (G := G) routing replacement profile
    (GkrSourceCallbacks.rightContext ctx) handle sites.right 0 width rightReference left.raw [] rightAllowed afterLeft routes.right
  rw [cast_total] at pairedRight
  apply (frame_left pairedRight (fold_yields _ _ _ (erased_yields _ _ (by
      rw [producerRounds_erase]
      exact execute_yields _ width rightReference left.raw [] rightDecoded rightAllowed)) afterLeft)).bind
  rintro l v ⟨⟨right, rightHistory, rfl, rfl⟩, _, _, rightSuffix, rightPoint, rightSize, rightAnchor⟩
  have rightLength : right.point.length = width := by simp_all
  have rightPointEq : right.point = rightSuffix := by simpa only [List.nil_append] using rightPoint
  let coefficients := line (circuit.wires remaining (index + 1)) left.point right.point
  have coefficientSize : coefficients.length = width + 1 := row_length _ _
  have polynomial : coefficientPolynomial coefficients = linePolynomial width
      (circuit.wires remaining (index + 1)) (coordinates width left.point) (coordinates width right.point) :=
    coefficientPolynomial_row _ _ (Nat.lt_succ_of_le (linePolynomial_natDegree _ _ _))
  have endpoints := Families.Gkr.Combination.honest_endpoints _ _ _ coefficients polynomial
  have terminal : GkrRoundsReference.total right.reference =
      Rounds.value reference (coordinates (width + width) (left.point ++ right.point)) := by
    change Rounds.value right.reference (coordinates 0 []) = _
    rw [rightAnchor, cast_value, leftAnchor]
    simp only [List.append_nil, ← leftPointEq, ← rightPointEq]
  have gate := gate_terminal circuit remaining index point left.point right.point pointSize leftLength rightLength
  have checked : GkrRoundsReference.total right.reference = GkrVerifier.wiringValue
      (extension (width + width + width) (circuit.add index)
        (coordinates (width + width + width) (point ++ left.point ++ right.point)))
      (extension (width + width + width) (circuit.mul index)
        (coordinates (width + width + width) (point ++ left.point ++ right.point)))
      ((coefficients)[0]?.getD 0) coefficients.sum := by
    rw [show (coefficients)[0]?.getD 0 = coefficients.headD 0 from by cases coefficients <;> rfl,
      endpoints.1, endpoints.2]
    exact terminal.trans gate
  let afterRight : State (F := F) (G := G) := { state with history := rightHistory }
  have constant := message (F := F) (G := G) routing replacement profile afterRight
    (GkrSourceCallbacks.lineConstantSite ctx) "bls12-381.fr" ((coefficients)[0]?.getD 0)
    routes.constantOrigin routes.constantRoute
  rw [← routes.validator, ← routes.producer] at constant
  apply constant.bind
  rintro l v ⟨rfl, rfl⟩
  let afterConstant : State (F := F) (G := G) := { afterRight with history := afterRight.history ++
    [.message routes.constantOrigin (.field "bls12-381.fr" ((coefficients)[0]?.getD 0))] }
  have packets := coefficient_pair (F := F) (G := G) routing replacement profile ctx routes.producer routes.validator
    sites.coefficients 0 afterConstant routes.packetOrigin routes.coefficient (tail coefficients 0 width) [((coefficients)[0]?.getD 0)]
  have tailSize : (tail coefficients 0 width).length = width := by simp [tail]
  rw [tailSize] at packets
  apply packets.bind
  rintro l v ⟨history, rfl, rfl⟩
  rw [show [((coefficients)[0]?.getD 0)] ++ tail coefficients 0 width = coefficients from
    reconstruct coefficients width coefficientSize]
  let beforeDraw : State (F := F) (G := G) := { state with history := history }
  change Readback _
    ((constructed { routing with mode := .producer }
      (.call (.receive (.field "bls12-381.fr") (GkrSourceCallbacks.lineDeliverySite ctx) (ctx.roles 1)) .done)
        beforeDraw).bind fun result =>
      constructed { routing with mode := .producer } (.done (linePoints left.point right.point result.1)) result.2)
    (HonestProducerPair.validator routing
      (GkrVerifier.lineCheck ctx handle width (circuit.add index) (circuit.mul index)
        (index, point, GkrRoundsReference.total reference) left.point right.point
        (GkrRoundsReference.total right.reference) ((coefficients)[0]?.getD 0) coefficients) beforeDraw)
  rw [← constructed_bind (F := F) (G := G) { routing with mode := .producer }
    (.call (.receive (.field "bls12-381.fr") (GkrSourceCallbacks.lineDeliverySite ctx) (ctx.roles 1)) .done)
    (fun r => .done (linePoints left.point right.point r)) beforeDraw]
  simp only [GkrVerifier.lineCheck, PIR.Process.bind]
  rw [ite_eq_left checked]
  simp only [GkrVerifier.lineDelivery, HonestProducerPair.validator,
    PIR.Process.interpret, CommonAdapter.embed, PIR.Process.bind]
  rw [routes.validator, routes.producer]
  apply challenge_step routing replacement profile beforeDraw _ _ "bls12-381.fr" handle routes.drawOrigin
    routes.deliveryOrigin routes.deliveryRoute routes.queryRoute routes.sentRoute routes.request
  intro r
  apply Readback.done
  refine ⟨linePoints left.point right.point r, _, rfl, ?_, ?_⟩
  · congr 2
    rw [Families.Gkr.Combination.honest_evaluation _ _ _ _ polynomial,
      coordinates_linePoints _ _ _ leftLength rightLength]
  · simp only [linePoints_length, leftLength, rightLength, min_self]

end ZkcSecurity.Realizations.Gkr.HonestProducerObservedLayers
