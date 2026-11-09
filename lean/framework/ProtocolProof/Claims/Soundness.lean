module

public import ProtocolProof.Claims.Quantitative
public import ProtocolProof.Claims.Problem

/-!
Promise soundness with output-selected statements and request-fixed adversarial admission.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w

/-- Promise soundness tests the negative region of the returned statement, allowing adaptive choice.
The environment type and admissibility predicate fix the quantified adversary interface. -/
structure SoundnessRequest (Environment : Type u) (Output : Type v) (Statement : Type w)
    [MeasurableSpace Output] where
  experiment : Experiment Environment Output
  admissible : Environment → Prop
  accepts : Output → Prop
  statement : Output → Statement
  problem : PromiseProblem Statement
  measurable_bad : MeasurableSet {out | accepts out ∧ problem.no (statement out)}
  error : Environment → ℝ≥0∞

/-- Negative-instance acceptance is derived from the request, never supplied by evidence. -/
@[expose] def SoundnessRequest.toUpper {E : Type u} {O : Type v} {X : Type w} [MeasurableSpace O]
    (request : SoundnessRequest E O X) : UpperRequest E O where
  experiment := request.experiment
  admissible := request.admissible
  event := {out | request.accepts out ∧ request.problem.no (request.statement out)}
  measurable_event := request.measurable_bad
  bound := request.error

@[expose] def SoundnessRequest.Holds {E : Type u} {O : Type v} {X : Type w} [MeasurableSpace O]
    (request : SoundnessRequest E O X) : Prop := request.toUpper.Holds

end ProtocolProof
