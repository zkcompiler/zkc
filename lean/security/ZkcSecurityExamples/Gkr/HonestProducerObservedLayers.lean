module

public import ZkcSecurityExamples.Gkr.HonestProducerOccurrences
public import ZkcSecurityExamples.Gkr.HonestProducerAlgorithm
public import ZkcSecurity.Families.Gkr.Combination

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
open ZkcSecurity.Source HonestProducerRounds
open HonestProducerPackets HonestProducerSource HonestProducerOccurrences

variable {F G : Type} [Field F] [DecidableEq F]

/-- Sites are supplied by the checked current-source body association. They
are neither inferred from old helper numbers nor erased during construction. -/
structure Sites where
  left : String
  right : String
  coefficients : String

def producerCoefficients (ctx : ProtocolContext) (site : String) : Nat → List F →
    PIR.Process (Signature F G) Unit
  | _, [] => .done ()
  | index, value :: rest =>
    (Occurrence.iterations.within site index
      ((@PIR.Process.call (participantInterface F G) Unit (.send (ty := .field "bls12-381.fr")
        (GkrVerifier.lineCoefficientSite ctx) (ctx.roles 1) value) .done).interpret
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
theorem coefficient_pair (ctx : ProtocolContext) (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (site : String) (index : Nat) (values coefficients : List F) :
    Pair scope (fun _ received => received = coefficients ++ values)
      (producerCoefficients (G := G) ctx site index values)
      (validatorCoefficients ctx site index values.length coefficients) := by
  induction values generalizing index coefficients with
  | nil => exact .done (by simp)
  | cons value rest ih =>
    rw [producerCoefficients, List.length_cons, validatorCoefficients]
    have one : Pair scope (fun (_ : Unit) next => next = coefficients ++ [value])
        ((@PIR.Process.call (participantInterface F G) Unit (.send (ty := .field "bls12-381.fr")
          (GkrVerifier.lineCoefficientSite ctx) (ctx.roles 1) value) .done).interpret Occurrence.actions)
        (((GkrVerifier.lineCoefficient ctx coefficients).interpret CommonAdapter.embed).interpret Occurrence.actions) :=
      by
        simp only [GkrVerifier.lineCoefficient, PIR.Process.interpret,
          CommonAdapter.embed, Occurrence.actions, PIR.Process.bind,
          GkrVerifier.lineCoefficientSite, GkrVerifier.lineCoefficientSite]
        rw [show (@PIR.Process.done (Signature F G) Unit) = (fun _ => .done ()) from by
          funext reply; cases reply; rfl]
        apply Pair.message _ _ _ _ _ rfl roles
        exact .done rfl
    exact (one.within site index).bind _ _ (by
      rintro ignored received rfl
      apply (ih (index + 1) (coefficients ++ [value])).mono
      intro _ result same
      simpa only [List.append_assoc, List.singleton_append] using same)

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
  (producerRounds (GkrVerifier.leftContext ctx) sites.left 0 width (n := width)
    reference (encode reference) []).bind fun left =>
  (producerRounds (GkrVerifier.rightContext ctx) sites.right 0 width (n := 0)
    ((Nat.zero_add width).symm ▸ left.reference) left.raw []).bind fun right =>
  let coefficients := line (circuit.wires remaining (index + 1)) left.point right.point
  ((@PIR.Process.call (participantInterface F G) Unit (.send (ty := .field "bls12-381.fr")
    (GkrVerifier.lineConstantSite ctx) (ctx.roles 1) ((coefficients)[0]?.getD 0)) .done).interpret
      Occurrence.actions).bind fun _ =>
  (producerCoefficients ctx sites.coefficients 0 (tail coefficients 0 width)).bind fun _ =>
  ((@PIR.Process.call (participantInterface F G) F (.receive (.field "bls12-381.fr")
    (GkrVerifier.lineDeliverySite ctx) (ctx.roles 1)) .done).interpret Occurrence.actions).bind fun r =>
  .done (linePoints left.point right.point r)

def validatorLayer (ctx : ProtocolContext) (handle width : Nat) (sites : Sites)
    (add mul : Nat → Table F (width + width + width)) (value : Nat × List F × F) :
    PIR.Process (Signature F G) (Nat × List F × F) :=
  (validatorRounds (GkrVerifier.leftContext ctx) handle sites.left 0 width ([], value.2.2)).bind fun left =>
  (validatorRounds (GkrVerifier.rightContext ctx) handle sites.right 0 width ([], left.2)).bind fun right =>
  (((@PIR.Process.call (Actions F G) F (.receive (.field "bls12-381.fr")
    (GkrVerifier.lineConstantSite ctx) (ctx.roles 0)) .done).interpret
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

/-- Both Sumcheck applications and the line polynomial compose at the source
level. Roles, deliveries and full returned values precede routing installation. -/
theorem layer_pair (ctx : ProtocolContext) (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (handle : Nat) (sites : Sites) {width : Nat}
    (circuit : Families.Gkr.Circuit F width) (remaining index : Nat)
    (point : List F) (pointSize : point.length = width)
    (leftDelivery : (GkrVerifier.challengeSite (GkrVerifier.leftContext ctx),
      GkrVerifier.deliverySite (GkrVerifier.leftContext ctx)) ∈ scope.deliveries)
    (rightDelivery : (GkrVerifier.challengeSite (GkrVerifier.rightContext ctx),
      GkrVerifier.deliverySite (GkrVerifier.rightContext ctx)) ∈ scope.deliveries)
    (lineDelivery : (GkrVerifier.lineChallengeSite ctx,
      GkrVerifier.lineDeliverySite ctx) ∈ scope.deliveries) :
    Pair scope (fun next value => value =
      (index + 1, next, extension width (circuit.wires remaining (index + 1))
        (coordinates width next)) ∧ next.length = width)
      (producerLayer (G := G) ctx sites circuit remaining index point)
      (validatorLayer ctx handle width sites circuit.add circuit.mul
        (index, point, extension width (circuit.wires (remaining + 1) index) (coordinates width point))) := by
  let reference := Circuit.factors circuit remaining index (coordinates width point)
  have allowed := Circuit.factors_admissible circuit remaining index (coordinates width point)
  unfold producerLayer validatorLayer
  dsimp only
  rw [Circuit.layer_identity]
  have left := (rounds (G := G) (GkrVerifier.leftContext ctx) scope roles handle sites.left 0 width
    reference (encode reference) [] allowed leftDelivery).frame_left
      (erased_yields _ _ (by
        rw [producerRounds_erase]
        exact execute_yields _ width reference (encode reference) [] (encode_decodes reference) allowed))
  apply left.bind
  rintro left value ⟨rfl, leftDecoded, leftAllowed, leftSuffix, leftPoint, leftSize, leftAnchor⟩
  have leftLength : left.point.length = width := by simp_all
  have leftPointEq : left.point = leftSuffix := by simpa only [List.nil_append] using leftPoint
  let rightReference : GkrRoundsReference.State F (0 + width) := (Nat.zero_add width).symm ▸ left.reference
  have rightDecoded := cast_decodes (Nat.zero_add width).symm left.reference left.raw leftDecoded
  have rightAllowed := cast_admissible (Nat.zero_add width).symm left.reference leftAllowed
  have right := (rounds (G := G) (GkrVerifier.rightContext ctx) scope roles handle sites.right 0 width
    rightReference left.raw [] rightAllowed rightDelivery).frame_left
      (erased_yields _ _ (by
        rw [producerRounds_erase]
        exact execute_yields _ width rightReference left.raw [] rightDecoded rightAllowed))
  rw [cast_total] at right
  apply right.bind
  rintro right value ⟨rfl, _, _, rightSuffix, rightPoint, rightSize, rightAnchor⟩
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
  change Pair scope _ (.call (.action (.send _ _ _)) _) (.call (.action (.receive _ _ _)) _)
  apply Pair.message _ _ _ _ _ rfl roles
  have tailSize : (tail coefficients 0 width).length = width := by simp [tail]
  have packets := coefficient_pair (G := G) ctx scope roles sites.coefficients 0
    (tail coefficients 0 width) [((coefficients)[0]?.getD 0)]
  rw [tailSize] at packets
  apply packets.bind
  rintro ignored received rfl
  rw [show [((coefficients)[0]?.getD 0)] ++ tail coefficients 0 width = coefficients from
    reconstruct coefficients width coefficientSize]
  dsimp only [coefficients] at checked ⊢
  simp only [GkrVerifier.lineCheck, checked, ↓reduceIte, GkrVerifier.lineDelivery,
    PIR.Process.interpret, CommonAdapter.embed, Occurrence.actions, PIR.Process.bind]
  apply Pair.challenge _ _ _ _ _ _ roles lineDelivery
  intro r
  apply Pair.done
  constructor
  · congr 1
    rw [Families.Gkr.Combination.honest_evaluation _ _ _ _ polynomial,
      coordinates_linePoints _ _ _ leftLength rightLength]
  · simp only [linePoints_length, leftLength, rightLength, min_self]

end ZkcSecurity.Realizations.Gkr.HonestProducerObservedLayers
