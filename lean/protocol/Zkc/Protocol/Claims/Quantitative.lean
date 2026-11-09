module

public import Zkc.Protocol.Semantics.Experiment

/-!
Fixed upper and lower event bounds. Property requests derive their events and budgets here.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w

/-- An upper bound on one fixed measurable event of a fixed experiment. -/
structure UpperRequest (Environment : Type u) (Output : Type v) [MeasurableSpace Output] where
  experiment : Experiment Environment Output
  admissible : Environment → Prop
  event : Set Output
  measurable_event : MeasurableSet event
  bound : Environment → ℝ≥0∞

/-- A lower bound is distinct: missing or rejected mass cannot establish completeness. -/
structure LowerRequest (Environment : Type u) (Output : Type v) [MeasurableSpace Output] where
  experiment : Experiment Environment Output
  admissible : Environment → Prop
  event : Set Output
  measurable_event : MeasurableSet event
  bound : Environment → ℝ≥0∞

/-- The request's meaning has no evidence argument. -/
@[expose] def UpperRequest.Holds {E : Type u} {O : Type v} [MeasurableSpace O]
    (request : UpperRequest E O) : Prop :=
  ∀ environment, request.admissible environment →
    request.experiment.run environment request.event ≤ request.bound environment

/-- Accepting mass must actually meet the requested lower bound. -/
@[expose] def LowerRequest.Holds {E : Type u} {O : Type v} [MeasurableSpace O]
    (request : LowerRequest E O) : Prop :=
  ∀ environment, request.admissible environment →
    request.bound environment ≤ request.experiment.run environment request.event

end ProtocolProof
