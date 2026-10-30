module

public import ZkcSecurityExamples.Gkr.HonestProducerObservedLayers

@[expose] public section

/-! Whole honest GKR pair with real nested source iteration observations.
Source body associations are kept explicit, separate from circuit truth. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerObserved
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured
open ZkcSecurity.Examples.Components
open ZkcSecurity.Source HonestProducerOccurrences
open HonestProducerSource

variable {F G : Type} [Field F] [DecidableEq F]

structure Sites where
  output : String
  layers : String
  layer : HonestProducerObservedLayers.Sites

def producerOutput (ctx : ProtocolContext) (site : String) : Nat → Nat → List F →
    PIR.Process (Signature F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (Occurrence.iterations.within site index
      ((output (G := G) ctx 1 point).interpret Occurrence.actions)).bind fun next =>
    producerOutput ctx site (index + 1) count next

def validatorOutput (ctx : ProtocolContext) (handle : Nat) (site : String) : Nat → Nat → List F →
    PIR.Process (Signature F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (Occurrence.iterations.within site index
      (((GkrVerifier.outputRound (G := G) ctx handle point).interpret CommonAdapter.embed).interpret
        Occurrence.actions)).bind fun next => validatorOutput ctx handle site (index + 1) count next

omit [Field F] [DecidableEq F] in
theorem output_pair (ctx : ProtocolContext) (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (handle : Nat) (site : String) (index count : Nat) (point : List F)
    (delivery : (GkrVerifier.outputSite ctx, GkrVerifier.outputDeliverySite ctx) ∈ scope.deliveries) :
    Pair scope (fun next value => value = next ∧ next.length = point.length + count)
      (producerOutput (G := G) ctx site index count point)
      (validatorOutput ctx handle site index count point) := by
  induction count generalizing index point with
  | zero => exact .done ⟨rfl, by omega⟩
  | succ count ih =>
    rw [producerOutput, validatorOutput]
    have one : Pair scope (fun (next value : List F) => value = next ∧ next.length = point.length + 1)
        ((output (G := G) ctx 1 point).interpret Occurrence.actions)
        (((GkrVerifier.outputRound (G := G) ctx handle point).interpret CommonAdapter.embed).interpret Occurrence.actions) :=
      .challenge _ _ _ _ _ _ roles delivery (fun r => .done ⟨rfl, by simp⟩)
    exact (one.within site index).bind _ _ (by
      rintro next value ⟨same, size⟩
      subst value
      apply (ih (index + 1) next).mono
      rintro result value ⟨rfl, finalSize⟩
      exact ⟨rfl, by omega⟩)

noncomputable def producerLayers (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F) :
    Nat → Nat → List F → PIR.Process (Signature F G) (List F)
  | _, 0, point => .done point
  | index, count + 1, point =>
    (Occurrence.iterations.within sites.layers index
      (HonestProducerObservedLayers.producerLayer ctx sites.layer encoding.circuit
        (encoding.layers - index - 1) index point)).bind fun next =>
    producerLayers ctx sites encoding (index + 1) count next

def validatorLayers (ctx : ProtocolContext) (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F) :
    Nat → Nat → (Nat × List F × F) → PIR.Process (Signature F G) (Nat × List F × F)
  | _, 0, value => .done value
  | index, count + 1, value =>
    (Occurrence.iterations.within sites.layers index
      (HonestProducerObservedLayers.validatorLayer ctx handle encoding.width sites.layer
        encoding.circuit.add encoding.circuit.mul value)).bind fun next =>
    validatorLayers ctx handle sites encoding (index + 1) count next

theorem layers_pair (ctx : ProtocolContext) (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F)
    (index count : Nat) (counted : index + count = encoding.layers)
    (point : List F) (pointSize : point.length = encoding.width)
    (leftDelivery : (GkrVerifier.challengeSite (GkrVerifier.leftContext ctx),
      GkrVerifier.deliverySite (GkrVerifier.leftContext ctx)) ∈ scope.deliveries)
    (rightDelivery : (GkrVerifier.challengeSite (GkrVerifier.rightContext ctx),
      GkrVerifier.deliverySite (GkrVerifier.rightContext ctx)) ∈ scope.deliveries)
    (lineDelivery : (GkrVerifier.lineChallengeSite ctx,
      GkrVerifier.lineDeliverySite ctx) ∈ scope.deliveries) :
    Pair scope (fun next value => value =
      (encoding.layers, next, extension encoding.width encoding.circuit.inputs
        (coordinates encoding.width next)) ∧ next.length = encoding.width)
      (producerLayers (G := G) ctx sites encoding index count point)
      (validatorLayers ctx handle sites encoding index count
        (index, point, extension encoding.width (encoding.circuit.wires count index)
          (coordinates encoding.width point))) := by
  induction count generalizing index point with
  | zero =>
    have same : index = encoding.layers := by omega
    subst index
    exact .done ⟨rfl, pointSize⟩
  | succ count ih =>
    have remaining : encoding.layers - index - 1 = count := by omega
    rw [producerLayers, validatorLayers, remaining]
    have one := HonestProducerObservedLayers.layer_pair (G := G) ctx scope roles handle sites.layer
      encoding.circuit count index point pointSize leftDelivery rightDelivery lineDelivery
    exact (one.within sites.layers index).bind _ _ (by
      rintro next value ⟨rfl, nextSize⟩
      exact ih (index + 1) (by omega) next nextSize)

noncomputable def producer (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F) :
    PIR.Process (Signature F G) (Values (Component (assignment F G)) [.boolean]) :=
  (producerOutput ctx sites.output 0 encoding.width []).bind fun point =>
  (producerLayers ctx sites encoding 0 encoding.layers point).bind fun _ => .done (.cons none .nil)

noncomputable def validator (ctx : ProtocolContext) (handle : Nat) (sites : Sites)
    (encoding : CircuitEncoding F) (outputs : List F) : PIR.Process (Signature F G) (Option Bool) :=
  (validatorOutput ctx handle sites.output 0 encoding.width []).bind fun point =>
  (validatorLayers ctx handle sites encoding 0 encoding.layers
    (0, point, extension encoding.width ((ofList? encoding.width outputs).getD 0)
      (coordinates encoding.width point))).bind fun value =>
  (((PIR.Process.done (GkrVerifier.decision encoding.width encoding.circuit.inputs value)).interpret CommonAdapter.embed).interpret
    Occurrence.actions)

omit [Field F] [DecidableEq F] in
theorem producerOutput_erase (ctx : ProtocolContext) (site : String) (index count : Nat) (point : List F) :
    (producerOutput (G := G) ctx site index count point).interpret Occurrence.erase = output ctx count point := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [producerOutput, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, actions_erase]
    simp only [output, PIR.Process.bind]
    congr 1
    funext r
    exact ih (index + 1) (point ++ [r])

omit [DecidableEq F] in
theorem producerLayers_erase (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F)
    (index count : Nat) (point : List F) :
    (producerLayers (G := G) ctx sites encoding index count point).interpret Occurrence.erase =
      layers ctx encoding index count point := by
  induction count generalizing index point with
  | zero => rfl
  | succ count ih =>
    rw [producerLayers, PIR.Process.interpret_bind,
      IterationObservations.within_interpret _ Occurrence.iterations_erase,
      IterationObservations.silent_within, HonestProducerObservedLayers.producerLayer_erase, layers]
    apply congrArg (PIR.Process.bind _)
    funext next
    exact ih (index + 1) next

omit [DecidableEq F] in
theorem producer_erase (ctx : ProtocolContext) (sites : Sites) (encoding : CircuitEncoding F) :
    (producer (G := G) ctx sites encoding).interpret Occurrence.erase = HonestProducerSource.producer ctx encoding := by
  unfold producer HonestProducerSource.producer
  simp only [PIR.Process.interpret_bind, producerOutput_erase, producerLayers_erase, PIR.Process.interpret]

/-- Successful source pairing for every challenge. The terminal relation keeps
both complete source outputs; no handler success or refusal is assumed. -/
theorem pair (ctx : ProtocolContext) (scope : PairScope)
    (roles : ctx.roles 0 = scope.producer ∧ ctx.roles 1 = scope.validator)
    (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F) (outputs : List F)
    (correct : encoding.Outputs outputs)
    (outputDelivery : (GkrVerifier.outputSite ctx,
      GkrVerifier.outputDeliverySite ctx) ∈ scope.deliveries)
    (leftDelivery : (GkrVerifier.challengeSite (GkrVerifier.leftContext ctx),
      GkrVerifier.deliverySite (GkrVerifier.leftContext ctx)) ∈ scope.deliveries)
    (rightDelivery : (GkrVerifier.challengeSite (GkrVerifier.rightContext ctx),
      GkrVerifier.deliverySite (GkrVerifier.rightContext ctx)) ∈ scope.deliveries)
    (lineDelivery : (GkrVerifier.lineChallengeSite ctx,
      GkrVerifier.lineDeliverySite ctx) ∈ scope.deliveries) :
    Pair scope (fun p v => p = .cons none .nil ∧ v = some true)
      (producer (G := G) ctx sites encoding) (validator ctx handle sites encoding outputs) := by
  unfold producer validator
  rw [correct.2]
  dsimp only [Option.getD]
  apply (output_pair (G := G) ctx scope roles handle sites.output 0 encoding.width [] outputDelivery).bind
  rintro point value ⟨same, size⟩
  subst value
  have pointSize : point.length = encoding.width := by simpa only [List.length_nil, Nat.zero_add] using size
  apply (layers_pair (G := G) ctx scope roles handle sites encoding 0 encoding.layers (by omega)
    point pointSize leftDelivery rightDelivery lineDelivery).bind
  rintro next value ⟨rfl, _⟩
  apply Pair.done
  simp only [GkrVerifier.decision, decide_true, PIR.Process.interpret]
  exact ⟨trivial, trivial⟩

end ZkcSecurity.Realizations.Gkr.HonestProducerObserved
