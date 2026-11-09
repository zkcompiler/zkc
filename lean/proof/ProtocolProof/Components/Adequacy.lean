module

public import ProtocolProof.Components.Contract
public import ProtocolProof.Semantics.Probability

/-! Process contract adequacy for complete kernels and whole initial experiments. -/

public section
open PIR MeasureTheory

namespace ProtocolProof
variable {E : Type} {I : Signature} {S L A : Type}
  [∀ op, MeasurableSpace (I.Reply op)]
  [∀ op, Countable (I.Reply op)] [∀ op, MeasurableSingletonClass (I.Reply op)]
  [MeasurableSpace S] [MeasurableSpace L] [MeasurableSpace A]
  {spec : OperationSpec I S L} {program : Process I A}
  {post : Outcome A → (S × List L) → ENNReal} {bound : (S × List L) → ENNReal}

namespace UpperBound

/-- Local upper operation laws make the composed contract adequate on every reached prefix. -/
theorem adequate (h : UpperBound spec program post bound) (system : System E I S L)
    (environment : E)
    (hlocal : ∀ operation continuation,
      opExpectation (system.accumulatedOperations environment) operation continuation ≤
        spec operation continuation)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2)
    (current : S × List L) :
    (∫⁻ out, post out.outcome (out.state, out.events)
      ∂system.runFrom environment program current) ≤ bound current := by
  have hrecord : Measurable (fun out : Execution S L A ↦
      post out.outcome (out.state, out.events)) :=
    hpost.comp Execution.measurableEquiv.measurable
  rw [system.runFrom_apply, lintegral_map hrecord Execution.measurableEquiv.symm.measurable]
  exact Internal.UpperBound.adequate h (system.accumulatedOperations environment)
    hlocal hpost current

/-- The budget covers the whole initial distribution, without conditioning on returned values. -/
theorem closed_expectation_le (system : System E I S L) (client : E → Process I A)
    (environment : E) (h : UpperBound spec (client environment) post bound)
    (hlocal : ∀ operation continuation,
      opExpectation (system.accumulatedOperations environment) operation continuation ≤
        spec operation continuation)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2)
    {budget : ENNReal}
    (hbudget : (∫⁻ current, bound current ∂system.initialWithEvents environment) ≤ budget) :
    (∫⁻ out, post out.outcome (out.state, out.events)
      ∂(system.experiment client).run environment) ≤ budget := by
  have hrecord : Measurable (fun out : Execution S L A ↦
      post out.outcome (out.state, out.events)) :=
    hpost.comp Execution.measurableEquiv.measurable
  rw [system.experiment_runFrom, Measure.lintegral_bind
    (system.runFrom environment (client environment)).aemeasurable hrecord.aemeasurable]
  exact (lintegral_mono (h.adequate system environment hlocal hpost)).trans hbudget

/-- An upper indicator contract bounds the fixed event on complete execution records. -/
theorem closed_event_le (system : System E I S L) (client : E → Process I A)
    (environment : E)
    (hlocal : ∀ operation continuation,
      opExpectation (system.accumulatedOperations environment) operation continuation ≤
        spec operation continuation)
    (event : Set (Execution S L A)) (hevent : MeasurableSet event)
    (h : UpperBound spec (client environment)
      (fun outcome reached ↦ event.indicator 1 ⟨outcome, reached.1, reached.2⟩) bound)
    {budget : ENNReal}
    (hbudget : (∫⁻ current, bound current ∂system.initialWithEvents environment) ≤ budget) :
    (system.experiment client).run environment event ≤ budget := by
  simpa only [lintegral_indicator_one hevent] using
    closed_expectation_le system client environment h hlocal
      ((measurable_const.indicator hevent).comp Execution.measurableEquiv.symm.measurable) hbudget

end UpperBound

namespace LowerBound

/-- Lower operation laws retain the reversed inequality on every complete terminal outcome. -/
theorem adequate (h : LowerBound spec program post bound) (system : System E I S L)
    (environment : E)
    (hlocal : ∀ operation continuation,
      spec operation continuation ≤
        opExpectation (system.accumulatedOperations environment) operation continuation)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2)
    (current : S × List L) :
    bound current ≤ ∫⁻ out, post out.outcome (out.state, out.events)
      ∂system.runFrom environment program current := by
  have hrecord : Measurable (fun out : Execution S L A ↦
      post out.outcome (out.state, out.events)) :=
    hpost.comp Execution.measurableEquiv.measurable
  rw [system.runFrom_apply, lintegral_map hrecord Execution.measurableEquiv.symm.measurable]
  exact Internal.LowerBound.adequate h (system.accumulatedOperations environment)
    hlocal hpost current

/-- The lower budget is integrated over the same entire initial distribution. -/
theorem le_closed_expectation (system : System E I S L) (client : E → Process I A)
    (environment : E) (h : LowerBound spec (client environment) post bound)
    (hlocal : ∀ operation continuation,
      spec operation continuation ≤
        opExpectation (system.accumulatedOperations environment) operation continuation)
    (hpost : Measurable fun out : Outcome A × (S × List L) ↦ post out.1 out.2)
    {budget : ENNReal}
    (hbudget : budget ≤ ∫⁻ current, bound current ∂system.initialWithEvents environment) :
    budget ≤ ∫⁻ out, post out.outcome (out.state, out.events)
      ∂(system.experiment client).run environment := by
  have hrecord : Measurable (fun out : Execution S L A ↦
      post out.outcome (out.state, out.events)) :=
    hpost.comp Execution.measurableEquiv.measurable
  rw [system.experiment_runFrom, Measure.lintegral_bind
    (system.runFrom environment (client environment)).aemeasurable hrecord.aemeasurable]
  exact hbudget.trans (lintegral_mono (h.adequate system environment hlocal hpost))

/-- A lower indicator contract proves unconditional complete-event mass, including stops. -/
theorem le_closed_event (system : System E I S L) (client : E → Process I A)
    (environment : E)
    (hlocal : ∀ operation continuation,
      spec operation continuation ≤
        opExpectation (system.accumulatedOperations environment) operation continuation)
    (event : Set (Execution S L A)) (hevent : MeasurableSet event)
    (h : LowerBound spec (client environment)
      (fun outcome reached ↦ event.indicator 1 ⟨outcome, reached.1, reached.2⟩) bound)
    {budget : ENNReal}
    (hbudget : budget ≤ ∫⁻ current, bound current ∂system.initialWithEvents environment) :
    budget ≤ (system.experiment client).run environment event := by
  simpa only [lintegral_indicator_one hevent] using
    le_closed_expectation system client environment h hlocal
      ((measurable_const.indicator hevent).comp Execution.measurableEquiv.symm.measurable) hbudget

end LowerBound
end ProtocolProof
