module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Complete experiments and fixed observations

An experiment includes every outcome with its original probability mass. Observing an
experiment is a measurable pushforward, never conditioning on successful execution.
-/

public section

open MeasureTheory

namespace ProtocolProof

universe u v w

/-- A complete probability law for each fixed environment. -/
structure Experiment (Environment : Type u) (Output : Type v) [MeasurableSpace Output] where
  run : Environment → Measure Output
  normalized : ∀ environment, IsProbabilityMeasure (run environment)

/-- The information selected by a claim, fixed independently of its proof. -/
structure Observation (Output : Type v) (View : Type w)
    [MeasurableSpace Output] [MeasurableSpace View] where
  observe : Output → View
  measurable : Measurable observe

namespace Observation

variable {O : Type u} {V : Type v} {W : Type w}
  [MeasurableSpace O] [MeasurableSpace V] [MeasurableSpace W]

/-- Retain the complete output. -/
@[expose] def identity : Observation O O := ⟨id, measurable_id⟩

/-- Observation composition does not discard mass. -/
@[expose] def comp (first : Observation O V) (second : Observation V W) : Observation O W :=
  ⟨second.observe ∘ first.observe, second.measurable.comp first.measurable⟩

/-- A returned value is one possible observation of a result and private state. -/
@[expose] def result : Observation (O × V) O := ⟨Prod.fst, measurable_fst⟩

end Observation

namespace Experiment

variable {E : Type u} {O : Type v} {V : Type w}
  [MeasurableSpace O] [MeasurableSpace V]

/-- Push forward the whole law, including rejection and abort outcomes. -/
@[expose] noncomputable def observe (experiment : Experiment E O) (observation : Observation O V) :
    Experiment E V where
  run environment := (experiment.run environment).map observation.observe
  normalized environment := by
    have := experiment.normalized environment
    refine ⟨?_⟩
    rw [Measure.map_apply observation.measurable MeasurableSet.univ]
    simp

/-- Reindex an environment before execution; this does not condition its output. -/
@[expose] def reindex {F : Type*} (experiment : Experiment E O) (input : F → E) :
    Experiment F O where
  run environment := experiment.run (input environment)
  normalized environment := experiment.normalized (input environment)

end Experiment

end ProtocolProof
