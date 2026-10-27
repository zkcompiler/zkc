module

public import ZkcSecurity.Realizations.Gkr.HonestProducerCurrent
public import ZkcSecurity.Realizations.Gkr.HonestProducerExecution

@[expose] public section

/-! Honest synchrony and exact generated-proof replay for the actual current
producer. Inputs are independently admitted; truth is mathematical circuit truth. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Realizations.Gkr.HonestProducerCurrentExecution
open Zkc Source Structured Construction
open ZkcExamples.Structured
open ZkcSecurity.FiatShamir HonestProducerComposition HonestProducerObserved
open HonestProducerSource
open OracleComp OracleSpec
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]

/-- The actual admitted producer returns for every oracle table, including
when the independent output claim is false. Stops cannot satisfy this postcondition. -/
theorem producer_returns (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (handle : Nat) (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (service : Option Nat)
    (state : State (F := F) (G := G))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing {} (state.frames ++ [⟨currentSites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing {}
      (state.frames ++ [⟨currentSites.layers, i⟩]) handle currentSites.layer)
    (answers : QueryImpl (TranscriptOracle.DomainSpec (uniformCarriers F G)) Id)
    (runtime : Domain.RuntimeState (uniformCarriers F G) Unit)
    (preceding : List (Domain.Event (uniformCarriers F G))) :
    PIR.WeakestPrecondition.satisfies
      ((Original.fold { routing with mode := .producer } (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
        (currentInputs encoding outputs service)) state).run
        (Domain.handler .producer (HonestCompiled.tableOracle answers)) runtime)
      (fun result _ _ => ∃ history, result = (.cons none .nil, { state with history := history }))
      (fun _ _ _ => False) preceding := by
  rw [HonestProducerSource.observed encoding outputs admitted service]
  exact HonestProducerExecution.producer_returns routing replacement profile {} handle currentSites encoding
    state outputRoutes layerRoutes answers runtime preceding

theorem pair (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (handle : Nat) (encoding : CircuitEncoding F) (outputs : List F)
    (admitted : encoding.Admitted 4 4 outputs) (correct : encoding.Outputs outputs)
    (service : Option Nat) (state : State (F := F) (G := G))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing {} (state.frames ++ [⟨currentSites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing {}
      (state.frames ++ [⟨currentSites.layers, i⟩]) handle currentSites.layer) :
    Readback (fun left right => ∃ history,
      left = (.cons none .nil, { state with history := history }) ∧
      right = (some true, { state with history := history }))
      (Original.fold { routing with mode := .producer } (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
        (currentInputs encoding outputs service)) state)
      (Original.fold { routing with mode := .validator } (validator {} handle currentSites encoding outputs) state) := by
  rw [HonestProducerSource.observed encoding outputs admitted service]
  exact HonestProducerObserved.pair routing replacement profile {} handle currentSites encoding outputs
    correct state outputRoutes layerRoutes

theorem pair_returns (routing : Original.Routing) (replacement : Replacement)
    (profile : routing.context.profile = .fiatShamir replacement)
    (handle : Nat) (encoding : CircuitEncoding F)
    (outputs : List F) (admitted : encoding.Admitted 4 4 outputs) (correct : encoding.Outputs outputs)
    (service : Option Nat)
    (state : State (F := F) (G := G))
    (outputRoutes : ∀ i, HonestProducer.OutputRoutes routing {} (state.frames ++ [⟨currentSites.output, i⟩]) handle)
    (layerRoutes : ∀ i, HonestProducerObservedLayers.Routes routing {}
      (state.frames ++ [⟨currentSites.layers, i⟩]) handle currentSites.layer)
    (answers : QueryImpl (TranscriptOracle.DomainSpec (uniformCarriers F G)) Id)
    (producerEnvironment validatorEnvironment : Domain.Environment (uniformCarriers F G))
    (preceding suffix : Domain.Proof (uniformCarriers F G)) :
    ∃ history producerFinal validatorFinal producerEvents validatorEvents generated,
      (Original.fold { routing with mode := .producer } (Occurrence.participant (ringModel F G) GkrSourceViews.program 0
        (currentInputs encoding outputs service)) state).run
        (Domain.handler .producer (HonestCompiled.tableOracle answers))
        ⟨producerEnvironment, preceding, ()⟩ =
          ⟨.returned (.cons none .nil, { state with history := history }),
            ⟨producerFinal, preceding ++ generated, ()⟩, producerEvents⟩ ∧
      (Original.fold { routing with mode := .validator }
        (validator {} handle currentSites encoding outputs) state).run
        (Domain.handler .validator (HonestCompiled.tableOracle answers))
        ⟨validatorEnvironment, generated ++ suffix, ()⟩ =
          ⟨.returned (some true, { state with history := history }),
            ⟨validatorFinal, suffix, ()⟩, validatorEvents⟩ := by
  rw [HonestProducerSource.observed encoding outputs admitted service]
  exact HonestProducerExecution.pair_returns routing replacement profile {} handle currentSites encoding outputs
    correct state outputRoutes layerRoutes answers producerEnvironment validatorEnvironment preceding suffix
end ZkcSecurity.Realizations.Gkr.HonestProducerCurrentExecution
