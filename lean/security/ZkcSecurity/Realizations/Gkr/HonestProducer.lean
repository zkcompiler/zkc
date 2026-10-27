module

public import ZkcSecurity.Realizations.Gkr.HonestProducerLayers

@[expose] public section

/-! Full honest GKR producer/validator composition against the independent
circuit semantics. The source-algorithm correspondence is imported separately;
nominal original-root occurrence association belongs to the root binding. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false

namespace ZkcSecurity.Realizations.Gkr.HonestProducer
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcExamples.Structured
open ZkcSecurity.FiatShamir HonestProducerComposition
open HonestProducerSource HonestProducerLayers

variable {F G : Type} [Field F] [DecidableEq F]

structure OutputRoutes (routing : Original.Routing) (ctx : ProtocolContext)
    (frames : Original.Frames) (handle : Nat) where
  producer : ctx.roles 0 = routing.context.producer
  validator : ctx.roles 1 = routing.context.validator
  drawOrigin : Origin
  deliveryOrigin : Origin
  queryRoute : routing.draw frames (GkrSourceCallbacks.outputSite ctx)
    "bls12-381.fr" handle = some drawOrigin
  deliveryRoute : routing.delivery frames (GkrSourceCallbacks.outputDeliverySite ctx)
    "bls12-381.fr" routing.context.validator = some (drawOrigin, deliveryOrigin)
  sentRoute : routing.message frames (GkrSourceCallbacks.outputDeliverySite ctx)
    routing.context.validator routing.context.producer = some deliveryOrigin
  request : drawOrigin.request = some (.draw "bls12-381.fr")

omit [Field F] [DecidableEq F] in
theorem output_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle count : Nat) (point : List F)
    (state : State (F := F) (G := G)) (routes : OutputRoutes routing ctx state.frames handle) :
    Readback (fun left right => ∃ next history,
      left = (next, { state with history := history }) ∧
      right = (next, { state with history := history }) ∧ next.length = point.length + count)
      (constructed { routing with mode := .producer } (output ctx count point) state)
      (HonestProducerPair.validator routing
        (PIR.repeatN count (GkrVerifier.outputRound ctx handle) point) state) := by
  induction count generalizing point state with
  | zero => exact .done ⟨point, state.history, rfl, rfl, by omega⟩
  | succ count ih =>
    simp only [output, PIR.repeatN, GkrVerifier.outputRound, GkrVerifier.outputDelivery,
      HonestProducerPair.validator, PIR.Process.bind, PIR.Process.interpret, CommonAdapter.embed]
    rw [routes.validator, routes.producer]
    apply challenge_step routing replacement profile state _ _ "bls12-381.fr" handle routes.drawOrigin
      routes.deliveryOrigin routes.deliveryRoute routes.queryRoute routes.sentRoute routes.request
    intro r
    let reached : State (F := F) (G := G) := { state with history := state.history ++
      [.challenge routes.drawOrigin, .message routes.deliveryOrigin (.field "bls12-381.fr" r)] }
    apply (ih (point ++ [r]) reached routes).mono
    rintro left right ⟨next, history, rfl, rfl, sized⟩
    refine ⟨next, history, rfl, rfl, ?_⟩
    simp only [List.length_append, List.length_singleton] at sized
    omega

theorem layers_pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (encoding : CircuitEncoding F)
    (index count : Nat) (counted : index + count = encoding.layers)
    (point : List F) (pointSize : point.length = encoding.width)
    (state : State (F := F) (G := G)) (routes : Routes routing ctx state.frames handle) :
    Readback (fun left right => ∃ next history,
      left = (next, { state with history := history }) ∧
      right = ((encoding.layers, next, extension encoding.width encoding.circuit.inputs
        (coordinates encoding.width next)), { state with history := history }) ∧ next.length = encoding.width)
      (constructed { routing with mode := .producer } (layers ctx encoding index count point) state)
      (HonestProducerPair.validator routing
        (PIR.repeatN count (GkrVerifier.layerStep ctx handle encoding.width encoding.circuit.add encoding.circuit.mul)
          (index, point, extension encoding.width (encoding.circuit.wires count index)
            (coordinates encoding.width point))) state) := by
  induction count generalizing index point state with
  | zero =>
    apply Readback.done
    refine ⟨point, state.history, rfl, ?_, pointSize⟩
    have same : index = encoding.layers := by omega
    subst index
    rfl
  | succ count ih =>
    have remaining : encoding.layers - index - 1 = count := by omega
    simp only [layers, PIR.repeatN, remaining, HonestProducerPair.validator,
      PIR.Process.interpret_bind, constructed_bind]
    apply (layer_pair routing replacement profile ctx handle encoding.circuit count index point pointSize state routes).bind
    rintro left right ⟨next, history, rfl, rfl, nextSize⟩
    exact ih (index + 1) (by omega) next nextSize { state with history := history } routes

/-- Whole computed honest producer/pair theorem. All challenge replies are
unrestricted, the field is arbitrary, and the initial history is arbitrary.
The only mathematical truth hypothesis compares outputs with independent wires.
No transcript, helper law, or producer correctness premise is supplied. -/
theorem pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (encoding : CircuitEncoding F) (outputs : List F)
    (correct : encoding.Outputs outputs)
    (state : State (F := F) (G := G))
    (outputRoutes : OutputRoutes routing ctx state.frames handle)
    (layerRoutes : Routes routing ctx state.frames handle) :
    Readback (fun left right => ∃ history,
      left = (.cons none .nil, { state with history := history }) ∧
      right = (some true, { state with history := history }))
      (constructed { routing with mode := .producer } (producer ctx encoding) state)
      (HonestProducerPair.validator routing (GkrVerifier.verifier ctx handle encoding.layers encoding.width
        ((ofList? encoding.width outputs).getD 0) encoding.circuit.inputs encoding.circuit.add encoding.circuit.mul) state) := by
  rw [correct.2]
  dsimp only [Option.getD]
  unfold producer GkrVerifier.verifier HonestProducerPair.validator
  rw [PIR.Process.interpret_bind, constructed_bind, constructed_bind]
  apply (output_pair routing replacement profile ctx handle encoding.width [] state outputRoutes).bind
  rintro left right ⟨point, history, rfl, rfl, size⟩
  have pointSize : point.length = encoding.width := by simpa only [List.length_nil, Nat.zero_add] using size
  simp only [GkrVerifier.afterOutputs, PIR.Process.interpret_bind, constructed_bind]
  apply (layers_pair routing replacement profile ctx handle encoding 0 encoding.layers (by omega)
    point pointSize { state with history := history } layerRoutes).bind
  rintro left right ⟨next, finalHistory, rfl, rfl, _⟩
  apply Readback.done
  refine ⟨finalHistory, rfl, ?_⟩
  simp only [GkrVerifier.decision, decide_true]

end ZkcSecurity.Realizations.Gkr.HonestProducer
