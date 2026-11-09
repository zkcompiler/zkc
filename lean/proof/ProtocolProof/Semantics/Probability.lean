module

public import ProtocolProof.Semantics.Quantitative
public import ProtocolProof.Semantics.System

/-!
# Exact probability laws for complete Process executions

Sequential execution passes the reached state and whole event prefix to the next process.
Stopped executions retain their complete record. Exact local expectations fold to the
integral of any measurable complete reward, including after sampling the whole initial law.
These laws reuse the upstream FreeM evaluator and the checked internal quantitative bridge.
-/

public section

set_option autoImplicit false

open PIR MeasureTheory ProbabilityTheory PFunctor

namespace ProtocolProof.System

variable {E : Type} {I : Signature} {S L A B : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace A] [MeasurableSpace B]
  (system : System E I S L)

/-- A returned value selects a measurable continuation; a stop preserves its complete record. -/
theorem measurable_runFrom_continuation [Countable A] [MeasurableSingletonClass A]
    (environment : E) (next : A → Process I B) :
    Measurable (fun out : Execution S L A ↦ match out.outcome with
      | .returned value => system.runFrom environment (next value) (out.state, out.events)
      | .stopped reason => Measure.dirac
          (⟨.stopped reason, out.state, out.events⟩ : Execution S L B)) := by
  have hcont : Measurable (fun out : Outcome A × (S × List L) ↦ match out.1 with
      | .returned value => system.runFrom environment (next value) out.2
      | .stopped reason => Measure.dirac
          (⟨.stopped reason, out.2.1, out.2.2⟩ : Execution S L B)) := by
    apply measurable_from_prod_countable_right
    intro outcome
    cases outcome with
    | returned value => exact (system.runFrom environment (next value)).measurable
    | stopped reason =>
        exact Measure.measurable_dirac.comp
          (Execution.measurableEquiv.symm.measurable.comp
            (measurable_const.prodMk measurable_id))
  exact hcont.comp Execution.measurableEquiv.measurable

/-- Bind threads the returned value, reached state and whole prefix, retaining every stop. -/
theorem runFrom_bind [Countable A] [MeasurableSingletonClass A]
    (environment : E) (program : Process I A) (next : A → Process I B)
    (current : S × List L) :
    system.runFrom environment (program.bind next) current =
      (system.runFrom environment program current).bind (fun out ↦ match out.outcome with
        | .returned value => system.runFrom environment (next value) (out.state, out.events)
        | .stopped reason => Measure.dirac ⟨.stopped reason, out.state, out.events⟩) := by
  let continuation : Outcome A → FreeM (Internal.effects I) (Outcome B) := fun outcome ↦
    match outcome with
    | .returned value => Internal.encode (next value)
    | .stopped reason => FreeM.pure (.stopped reason)
  have hencoded :
      FreeM.runKernel (system.accumulatedOperations environment)
          (Internal.encode (program.bind next)) current =
        (FreeM.runKernel (system.accumulatedOperations environment)
          (Internal.encode program) current).bind (fun out ↦
            FreeM.runKernel (system.accumulatedOperations environment)
              (continuation out.1) out.2) := by
    rw [Internal.encode_bind]
    exact FreeM.runKernel_bind (system.accumulatedOperations environment)
      (Internal.encode program) continuation current
  have hcont := FreeM.measurable_runKernel_continuation
    (system.accumulatedOperations environment) continuation
  rw [runFrom_apply, hencoded]
  refine (Measure.map_bind hcont.aemeasurable
    Execution.measurableEquiv.symm.measurable.aemeasurable).trans ?_
  rw [runFrom_apply, Measure.bind_map Execution.measurableEquiv.symm.measurable.aemeasurable
    (system.measurable_runFrom_continuation environment next).aemeasurable]
  congr 1
  funext out
  cases out with
  | mk outcome reached =>
      cases outcome with
      | returned value => exact (system.runFrom_apply environment (next value) reached).symm
      | stopped reason =>
          exact (congrArg (Measure.map Execution.measurableEquiv.symm)
            (FreeM.runKernel_pure (P := Internal.effects I)
              (system.accumulatedOperations environment) (Outcome.stopped (A := B) reason)
              reached)).trans (Measure.map_dirac' Execution.measurableEquiv.symm.measurable _)

/-- The complete experiment samples the entire initial law with an empty event prefix. -/
theorem experiment_runFrom (client : E → Process I A) (environment : E) :
    (system.experiment client).run environment =
      (system.initialWithEvents environment).bind
        (system.runFrom environment (client environment)) := by
  change ((system.initialWithEvents environment).bind
    (FreeM.runKernel (system.accumulatedOperations environment)
      (Internal.encode (client environment)))).map Execution.measurableEquiv.symm = _
  refine (Measure.map_bind (FreeM.runKernel _ _).aemeasurable
    Execution.measurableEquiv.symm.measurable.aemeasurable).trans ?_
  congr 1
  funext current
  exact (system.runFrom_apply environment (client environment) current).symm

/-- Exact local expectations equal the public execution integral of a measurable complete reward. -/
theorem wpFold_eq_lintegral_runFrom (environment : E) (program : Process I A)
    (post : Outcome A → (S × List L) → ENNReal)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2)
    (current : S × List L) :
    wpFold (opExpectation (system.accumulatedOperations environment)) program post current =
      ∫⁻ out, post out.outcome (out.state, out.events)
        ∂system.runFrom environment program current := by
  have hrecord : Measurable (fun out : Execution S L A ↦
      post out.outcome (out.state, out.events)) :=
    hpost.comp Execution.measurableEquiv.measurable
  rw [runFrom_apply, lintegral_map hrecord
    Execution.measurableEquiv.symm.measurable]
  exact congrFun (Internal.wpFold_eq_runExpectation_of_measurable
    (system.accumulatedOperations environment) (Internal.encode program) post hpost) current

/-- A measurable complete reward has a measurable exact potential on state and event prefixes. -/
theorem measurable_wpFold (environment : E) (program : Process I A)
    (post : Outcome A → (S × List L) → ENNReal)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2) :
    Measurable (wpFold (opExpectation (system.accumulatedOperations environment))
      program post) := by
  have heq := funext (system.wpFold_eq_lintegral_runFrom environment program post hpost)
  rw [heq]
  exact (hpost.comp Execution.measurableEquiv.measurable).lintegral_kernel

/-- Integrating the exact potential over the whole augmented initial law closes the experiment. -/
theorem lintegral_wpFold_eq_experiment (client : E → Process I A) (environment : E)
    (post : Outcome A → (S × List L) → ENNReal)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2) :
    (∫⁻ current, wpFold (opExpectation (system.accumulatedOperations environment))
      (client environment) post current ∂system.initialWithEvents environment) =
      ∫⁻ out, post out.outcome (out.state, out.events)
        ∂(system.experiment client).run environment := by
  simp_rw [system.wpFold_eq_lintegral_runFrom environment (client environment) post hpost]
  rw [experiment_runFrom]
  exact (Measure.lintegral_bind (system.runFrom environment (client environment)).aemeasurable
    (hpost.comp Execution.measurableEquiv.measurable).aemeasurable).symm

/-- The same exact equation uses the original initial state law and the empty starting prefix. -/
theorem lintegral_wpFold_initial_eq_experiment (client : E → Process I A) (environment : E)
    (post : Outcome A → (S × List L) → ENNReal)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2) :
    (∫⁻ state, wpFold (opExpectation (system.accumulatedOperations environment))
      (client environment) post (state, []) ∂system.initial environment) =
      ∫⁻ out, post out.outcome (out.state, out.events)
        ∂(system.experiment client).run environment := by
  rw [← system.lintegral_wpFold_eq_experiment client environment post hpost, initialWithEvents]
  have hinitial : Measurable (fun state : S ↦ (state, ([] : List L))) :=
    measurable_id.prodMk measurable_const
  exact (lintegral_map
    (system.measurable_wpFold environment (client environment) post hpost) hinitial).symm

/-- Indicator rewards measure the full event, including stopped outcomes and their logs. -/
theorem wpFold_indicator (environment : E) (program : Process I A)
    (event : Set (Execution S L A)) (hevent : MeasurableSet event) (current : S × List L) :
    wpFold (opExpectation (system.accumulatedOperations environment)) program
      (fun outcome reached ↦ event.indicator 1 ⟨outcome, reached.1, reached.2⟩) current =
        system.runFrom environment program current event := by
  rw [system.wpFold_eq_lintegral_runFrom environment program _
    ((measurable_const.indicator hevent).comp Execution.measurableEquiv.symm.measurable)]
  exact lintegral_indicator_one hevent

/-- Integrating an event indicator gives its unconditional probability in the whole experiment. -/
theorem lintegral_wpFold_indicator (client : E → Process I A) (environment : E)
    (event : Set (Execution S L A)) (hevent : MeasurableSet event) :
    (∫⁻ current, wpFold (opExpectation (system.accumulatedOperations environment))
      (client environment)
      (fun outcome reached ↦ event.indicator 1 ⟨outcome, reached.1, reached.2⟩) current
        ∂system.initialWithEvents environment) =
      (system.experiment client).run environment event := by
  rw [system.lintegral_wpFold_eq_experiment client environment _
    ((measurable_const.indicator hevent).comp Execution.measurableEquiv.symm.measurable)]
  exact lintegral_indicator_one hevent

/-- Dirac initial and primitive laws agree with the full canonical deterministic execution. -/
theorem experiment_eq_dirac (client : E → Process I A) (environment : E)
    (handler : Handler I S L)
    (hlocal : ∀ operation state, system.operations environment operation state =
      Measure.dirac (handler operation state))
    (initial : S) (hinitial : system.initial environment = Measure.dirac initial) :
    (system.experiment client).run environment =
      Measure.dirac ((client environment).run handler initial) := by
  rw [experiment_run, hinitial,
    Measure.dirac_bind (system.run environment (client environment)).measurable]
  exact system.run_eq_dirac environment handler hlocal (client environment) initial

/-- The complete prefix-aware execution kernel is normalized, including all stopped branches. -/
instance runFrom_isMarkov (environment : E) (program : Process I A) :
    IsMarkovKernel (system.runFrom environment program) :=
  ⟨fun current ↦ ⟨system.runFrom_mass_one environment program current⟩⟩

/-- The public state-to-execution kernel is normalized. -/
instance run_isMarkov (environment : E) (program : Process I A) :
    IsMarkovKernel (system.run environment program) :=
  ⟨fun state ↦ ⟨system.run_mass_one environment program state⟩⟩

end ProtocolProof.System
