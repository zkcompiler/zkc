module

public import Zkc.Protocol.Claims.Quantitative
public import Zkc.Protocol.Claims.Problem

/-!
Unconditional honest accepting mass. Rejection and abort never disappear by conditioning.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w

/-- Completeness quantifies over the request's admitted honest initial environments.
An environment contains the public input and its valid honest witness or other honest inputs. -/
structure CompletenessRequest (Environment : Type u) (Output : Type v)
    [MeasurableSpace Output] where
  experiment : Experiment Environment Output
  admissible : Environment → Prop
  accepts : Set Output
  measurable_accepts : MeasurableSet accepts
  error : Environment → ℝ≥0∞

/-- Completeness is an unconditional lower bound on accepting mass. -/
@[expose] def CompletenessRequest.toLower {E : Type u} {O : Type v} [MeasurableSpace O]
    (request : CompletenessRequest E O) : LowerRequest E O where
  experiment := request.experiment
  admissible := request.admissible
  event := request.accepts
  measurable_event := request.measurable_accepts
  bound environment := 1 - request.error environment

@[expose] def CompletenessRequest.Holds {E : Type u} {O : Type v} [MeasurableSpace O]
    (request : CompletenessRequest E O) : Prop := request.toLower.Holds

end ProtocolProof
