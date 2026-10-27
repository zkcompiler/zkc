module

public import ZkcSecurity.Realizations.Gkr.HonestProducerObserved

@[expose] public section

/-! Returning actual producer executions compose at the reached runtime state.
The generic honest-composition rule sees the whole value, environment, proof
buffer, oracle state and accumulated observation prefix. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace ZkcSecurity.Realizations.Gkr.HonestProducerExecution
open Zkc Source Structured Construction
open Zkc.Polynomial Zkc.Polynomial.Multilinear
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerObserved
open OracleComp OracleSpec PIR.WeakestPrecondition

variable {F G : Type} [Field F] [DecidableEq F]

/-- Success of the producer is proved by its output-stage invariant followed
by the layer stage at exactly the runtime state returned by that output stage.
A failed operation or source boundary cannot satisfy the stop postcondition. -/
theorem producer_returns (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F)
    (state : State (F := F) (G := G))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing ctx (state.frames ++ [⟨sites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing ctx
      (state.frames ++ [⟨sites.layers, i⟩]) handle sites.layer)
    (answers : QueryImpl (TranscriptOracle.DomainSpec (uniformCarriers F G)) Id)
    (runtime : Domain.RuntimeState (uniformCarriers F G) Unit)
    (preceding : List (Domain.Event (uniformCarriers F G))) :
    satisfies
      ((Original.fold { routing with mode := .producer } (producer ctx sites encoding) state).run
        (Domain.handler .producer (HonestCompiled.tableOracle answers)) runtime)
      (fun result _ _ => ∃ history, result = (.cons none .nil, { state with history := history }))
      (fun _ _ _ => False) preceding := by
  let handler := Domain.handler .producer (HonestCompiled.tableOracle answers)
  let first := Original.fold { routing with mode := .producer }
    (producerOutput (G := G) ctx sites.output 0 encoding.width []) state
  let next := fun result : List F × State (F := F) (G := G) =>
    Original.fold { routing with mode := .producer }
      ((producerLayers ctx sites encoding 0 encoding.layers result.1).bind
        fun _ => .done (.cons none .nil : Values (Component (assignment F G)) [.boolean])) result.2
  let intermediate := fun result : List F × State (F := F) (G := G) =>
    fun (_ : Domain.RuntimeState (uniformCarriers F G) Unit) (_ : List (Domain.Event (uniformCarriers F G))) =>
      ∃ point history, result = (point, { state with history := history }) ∧ point.length = encoding.width
  have honestPrefix : satisfies (first.run handler runtime) intermediate (fun _ _ _ => False) preceding := by
    have aligned := output_pair routing replacement profile ctx handle sites.output 0 encoding.width [] state outputRoutes
    obtain ⟨left, right, leftFinal, rightFinal, leftEvents, rightEvents, emitted, produced, _, post⟩ :=
      aligned.run answers runtime.environment [] runtime.proof []
    have runtimeEq : runtime = ⟨runtime.environment, runtime.proof, ()⟩ := by cases runtime; rfl
    rw [runtimeEq]
    change satisfies (_ : PIR.Execution _ _ _) intermediate _ _
    rw [show first.run handler ⟨runtime.environment, runtime.proof, ()⟩ = _ from produced]
    obtain ⟨point, history, rfl, _, size⟩ := post
    exact ⟨point, history, rfl, by simpa only [List.length_nil, Nat.zero_add] using size⟩
  have suffix : ∀ value reached events,
      first.run handler runtime = ⟨.returned value, reached, events⟩ →
      intermediate value reached (preceding ++ events) →
      satisfies ((next value).run handler reached)
        (fun result _ _ => ∃ history, result = (.cons none .nil, { state with history := history }))
        (fun _ _ _ => False) (preceding ++ events) := by
    rintro value reached events _ ⟨point, history, rfl, size⟩
    let atLayers : State (F := F) (G := G) := { state with history := history }
    have aligned := layers_pair routing replacement profile ctx handle sites encoding 0 encoding.layers
      (by omega) point size atLayers layerRoutes
    have finished := aligned.bind
      (Final := fun result (_ : (Nat × List F × F) × State (F := F) (G := G)) =>
        ∃ h, result = ((.cons none .nil : Values (Component (assignment F G)) [.boolean]),
          { state with history := h }))
      (fun result => Original.fold { routing with mode := .producer }
        (.done (.cons none .nil : Values (Component (assignment F G)) [.boolean])) result.2)
      (fun result => PIR.Process.done result)
      (by
        rintro left right ⟨point, history, rfl, rfl, _⟩
        exact .done ⟨history, rfl⟩)
    obtain ⟨left, right, leftFinal, rightFinal, leftEvents, rightEvents, emitted, produced, _, post⟩ :=
      finished.run answers reached.environment [] reached.proof []
    have reachedEq : reached = ⟨reached.environment, reached.proof, ()⟩ := by cases reached; rfl
    rw [reachedEq]
    let leftTail := (Original.fold { routing with mode := .producer }
      (producerLayers ctx sites encoding 0 encoding.layers point) atLayers).bind fun result =>
        Original.fold { routing with mode := .producer }
          (.done (.cons none .nil : Values (Component (assignment F G)) [.boolean])) result.2
    have joined : next (point, atLayers) = leftTail := by
      dsimp only [next, leftTail]
      rw [Original.fold_bind]
    change satisfies ((next (point, atLayers)).run handler _) _ _ _
    rw [joined, show leftTail.run handler ⟨reached.environment, reached.proof, ()⟩ = _ from produced]
    exact post
  have composed := ZkcSecurity.Obligations.HonestComposition.deterministic_bind handler first next runtime preceding
    intermediate (fun result _ _ => ∃ history, result = (.cons none .nil, { state with history := history })) honestPrefix suffix
  simpa only [producer, Original.fold_bind, first, next] using composed

/-- The proof buffer is generated by the computed producer. On the same
keyed oracle, the actual validator consumes precisely that generated buffer.
Both full runs return, preserve the caller frames, and reach one history. -/
theorem pair_returns (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (ctx : ProtocolContext) (handle : Nat) (sites : Sites) (encoding : CircuitEncoding F)
    (outputs : List F) (correct : encoding.Outputs outputs)
    (state : State (F := F) (G := G))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing ctx (state.frames ++ [⟨sites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing ctx
      (state.frames ++ [⟨sites.layers, i⟩]) handle sites.layer)
    (answers : QueryImpl (TranscriptOracle.DomainSpec (uniformCarriers F G)) Id)
    (producerEnvironment validatorEnvironment : Domain.Environment (uniformCarriers F G))
    (preceding suffix : Domain.Proof (uniformCarriers F G)) :
    ∃ history producerFinal validatorFinal producerEvents validatorEvents generated,
      (Original.fold { routing with mode := .producer } (producer ctx sites encoding) state).run
        (Domain.handler .producer (HonestCompiled.tableOracle answers))
        ⟨producerEnvironment, preceding, ()⟩ =
          ⟨.returned (.cons none .nil, { state with history := history }),
            ⟨producerFinal, preceding ++ generated, ()⟩, producerEvents⟩ ∧
      (Original.fold { routing with mode := .validator }
        (validator ctx handle sites encoding outputs) state).run
        (Domain.handler .validator (HonestCompiled.tableOracle answers))
        ⟨validatorEnvironment, generated ++ suffix, ()⟩ =
          ⟨.returned (some true, { state with history := history }),
            ⟨validatorFinal, suffix, ()⟩, validatorEvents⟩ := by
  obtain ⟨left, right, leftFinal, rightFinal, leftEvents, rightEvents, generated,
    produced, validated, history, rfl, rfl⟩ :=
    (pair routing replacement profile ctx handle sites encoding outputs correct state
      outputRoutes layerRoutes).run answers producerEnvironment validatorEnvironment preceding suffix
  exact ⟨history, leftFinal, rightFinal, leftEvents, rightEvents, generated, produced, validated⟩

end ZkcSecurity.Realizations.Gkr.HonestProducerExecution
