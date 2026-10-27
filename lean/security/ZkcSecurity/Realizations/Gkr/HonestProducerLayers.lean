module

public import ZkcSecurity.Realizations.Gkr.HonestProducerAlgorithm
public import ZkcSecurity.Realizations.Gkr.HonestProducerPair
public import ZkcSecurity.Families.Gkr.Combination

@[expose] public section

/-! Honest composition of both Sumcheck calls and the actual computed line
polynomial. Every seam carries the actual construction history and return. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerLayers
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear CoefficientRows
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerRounds HonestProducerPair
open HonestProducerPackets HonestProducerSource

variable {F G : Type} [Field F] [DecidableEq F]

/-- The line challenge and constant message share the layer frame. Coefficient
messages have their own schedule, supplied separately by each caller. -/
structure LineChallengeRoutes (routing : Original.Routing) (ctx : ProtocolContext)
    (frames : Original.Frames) (handle : Nat) where
  producer : ctx.roles 0 = routing.context.producer
  validator : ctx.roles 1 = routing.context.validator
  constantOrigin : Origin
  drawOrigin : Origin
  deliveryOrigin : Origin
  constantRoute : routing.message frames (GkrSourceCallbacks.lineConstantSite ctx)
    routing.context.producer routing.context.validator = some constantOrigin
  queryRoute : routing.draw frames (GkrSourceCallbacks.lineChallengeSite ctx)
    "bls12-381.fr" handle = some drawOrigin
  deliveryRoute : routing.delivery frames (GkrSourceCallbacks.lineDeliverySite ctx)
    "bls12-381.fr" routing.context.validator = some (drawOrigin, deliveryOrigin)
  sentRoute : routing.message frames (GkrSourceCallbacks.lineDeliverySite ctx)
    routing.context.validator routing.context.producer = some deliveryOrigin
  request : drawOrigin.request = some (.draw "bls12-381.fr")

/-- The unobserved coefficient sequence uses one unchanged frame. -/
structure LineRoutes (routing : Original.Routing) (ctx : ProtocolContext)
    (frames : Original.Frames) (handle : Nat) extends LineChallengeRoutes routing ctx frames handle where
  coefficientOrigin : Origin
  coefficientRoute : routing.message frames (GkrSourceCallbacks.lineCoefficientSite ctx)
    routing.context.producer routing.context.validator = some coefficientOrigin

structure Routes (routing : Original.Routing) (ctx : ProtocolContext)
    (frames : Original.Frames) (handle : Nat) extends LineRoutes routing ctx frames handle where
  left : RoundRoutes routing (GkrSourceCallbacks.leftContext ctx) frames handle
  right : RoundRoutes routing (GkrSourceCallbacks.rightContext ctx) frames handle

omit [Field F] [DecidableEq F] in
theorem coefficient_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (producer : ctx.roles 0 = routing.context.producer)
    (validatorRole : ctx.roles 1 = routing.context.validator)
    (state : State (F := F) (G := G)) (origin : Origin)
    (route : routing.message state.frames (GkrSourceCallbacks.lineCoefficientSite ctx)
      routing.context.producer routing.context.validator = some origin)
    (values coefficients : List F) :
    Readback (fun left right => ∃ history,
      left = ((), { state with history := history }) ∧
      right = (coefficients ++ values, { state with history := history }))
      (constructed { routing with mode := .producer } (sendTail ctx values) state)
      (HonestProducerPair.validator routing
        (PIR.repeatN values.length (GkrVerifier.lineCoefficient ctx) coefficients) state) := by
  induction values generalizing coefficients state with
  | nil => exact .done ⟨state.history, rfl, by simp⟩
  | cons value rest ih =>
    simp only [sendTail, List.length_cons, PIR.repeatN, GkrVerifier.lineCoefficient,
      HonestProducerPair.validator, PIR.Process.bind, PIR.Process.interpret, CommonAdapter.embed]
    rw [producer, validatorRole]
    apply message_step routing replacement profile state _ "bls12-381.fr" value origin route
    let reached : State (F := F) (G := G) := { state with history := state.history ++
      [.message origin (.field "bls12-381.fr" value)] }
    apply (ih reached route (coefficients ++ [value])).mono
    rintro left right ⟨history, rfl, rfl⟩
    exact ⟨history, rfl, by simp only [List.append_assoc, List.singleton_append]; rfl⟩

omit [DecidableEq F] in
theorem gate_terminal {width : Nat} (circuit : Families.Gkr.Circuit F width)
    (remaining index : Nat) (point left right : List F)
    (pointSize : point.length = width) (leftSize : left.length = width) (rightSize : right.length = width) :
    Rounds.value (Circuit.factors circuit remaining index (coordinates width point))
      (coordinates (width + width) (left ++ right)) =
      GkrVerifier.wiringValue
        (extension (width + width + width) (circuit.add index)
          (coordinates (width + width + width) (point ++ left ++ right)))
        (extension (width + width + width) (circuit.mul index)
          (coordinates (width + width + width) (point ++ left ++ right)))
        (extension width (circuit.wires remaining (index + 1)) (coordinates width left))
        (extension width (circuit.wires remaining (index + 1)) (coordinates width right)) := by
  have law := Circuit.factors_evaluation circuit remaining index (coordinates width point)
    (coordinates width left) (coordinates width right)
  dsimp only at law
  rw [← coordinates_three _ _ _ pointSize leftSize rightSize,
    point_coordinates width _ _ leftSize rightSize] at law
  exact law

/-- A true independent circuit claim passes both computed round streams and
the computed line check, for every challenge and every initial history. -/
theorem layer_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat)
    (point : List F) (pointSize : point.length = width)
    (state : State (F := F) (G := G)) (routes : Routes routing ctx state.frames handle) :
    Readback (fun left right => ∃ next history,
      left = (next, { state with history := history }) ∧
      right = ((index + 1, next, extension width (circuit.wires remaining (index + 1))
        (coordinates width next)), { state with history := history }) ∧ next.length = width)
      (constructed { routing with mode := .producer }
        (layer ctx circuit remaining index point) state)
      (HonestProducerPair.validator routing
        (GkrVerifier.layerStep ctx handle width circuit.add circuit.mul
          (index, point, extension width (circuit.wires (remaining + 1) index) (coordinates width point))) state) := by
  let reference := Circuit.factors circuit remaining index (coordinates width point)
  have allowed := Circuit.factors_admissible circuit remaining index (coordinates width point)
  unfold layer GkrVerifier.layerStep HonestProducerPair.validator
  dsimp only
  rw [PIR.Process.interpret_bind, constructed_bind, constructed_bind]
  rw [Circuit.layer_identity]
  apply (frame_left (rounds routing replacement profile (GkrSourceCallbacks.leftContext ctx) handle width
    reference (encode reference) [] allowed state routes.left)
    (constructed_yields _ _ _ (execute_yields _ width reference (encode reference) []
      (encode_decodes reference) allowed) state)).bind
  rintro l v ⟨⟨left, leftHistory, rfl, rfl⟩, leftDecoded, leftAllowed,
    leftSuffix, leftPoint, leftSize, leftAnchor⟩
  have leftLength : left.point.length = width := by simp_all
  have leftPointEq : left.point = leftSuffix := by simpa only [List.nil_append] using leftPoint
  let afterLeft : State (F := F) (G := G) := { state with history := leftHistory }
  let rightReference : GkrRoundsReference.State F (0 + width) := (Nat.zero_add width).symm ▸ left.reference
  have rightDecoded := cast_decodes (Nat.zero_add width).symm left.reference left.raw leftDecoded
  have rightAllowed := cast_admissible (Nat.zero_add width).symm left.reference leftAllowed
  simp only [GkrVerifier.layerAfterLeft, PIR.Process.interpret_bind, constructed_bind]
  have pairedRight := rounds (F := F) (G := G) routing replacement profile
    (GkrSourceCallbacks.rightContext ctx) handle width rightReference left.raw [] rightAllowed afterLeft routes.right
  rw [cast_total] at pairedRight
  apply (frame_left pairedRight (constructed_yields _ _ _
    (execute_yields _ width rightReference left.raw [] rightDecoded rightAllowed) afterLeft)).bind
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
  simp only [GkrVerifier.layerAfterRight, PIR.Process.interpret, CommonAdapter.embed, PIR.Process.bind]
  rw [routes.validator, routes.producer]
  apply message_step routing replacement profile afterRight _ "bls12-381.fr" _
    routes.constantOrigin routes.constantRoute
  let afterConstant : State (F := F) (G := G) := { afterRight with history := afterRight.history ++
    [.message routes.constantOrigin (.field "bls12-381.fr" ((coefficients)[0]?.getD 0))] }
  simp only [GkrVerifier.layerAfterConstant, PIR.Process.interpret_bind, constructed_bind]
  have packets := coefficient_pair (F := F) (G := G) routing replacement profile ctx routes.producer routes.validator
    afterConstant routes.coefficientOrigin routes.coefficientRoute (tail coefficients 0 width) [((coefficients)[0]?.getD 0)]
  have tailSize : (tail coefficients 0 width).length = width := by simp [tail]
  rw [tailSize] at packets
  apply packets.bind
  rintro l v ⟨history, rfl, rfl⟩
  rw [show [((coefficients)[0]?.getD 0)] ++ tail coefficients 0 width = coefficients from
    reconstruct coefficients width coefficientSize]
  simp only [GkrVerifier.lineCheck]
  rw [ite_eq_left checked]
  simp only [GkrVerifier.lineDelivery,
    PIR.Process.interpret, CommonAdapter.embed, PIR.Process.bind]
  rw [routes.producer]
  let beforeDraw : State (F := F) (G := G) := { state with history := history }
  apply challenge_step routing replacement profile beforeDraw _ _ "bls12-381.fr" handle routes.drawOrigin
    routes.deliveryOrigin routes.deliveryRoute routes.queryRoute routes.sentRoute routes.request
  intro r
  apply Readback.done
  refine ⟨linePoints left.point right.point r, _, rfl, ?_, ?_⟩
  · congr 2
    rw [Families.Gkr.Combination.honest_evaluation _ _ _ _ polynomial,
      coordinates_linePoints _ _ _ leftLength rightLength]
  · simp only [linePoints_length, leftLength, rightLength, min_self]

end ZkcSecurity.Realizations.Gkr.HonestProducerLayers
