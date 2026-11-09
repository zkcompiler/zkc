module

public import Zkc.Protocol.Claims.Quantitative

/-!
Correctness of a request-fixed recovery map, separate from a knowledge extraction experiment.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w

/-- A recovery request fixes both the experiment and the recovery function. A full knowledge
claim additionally requires an appropriate extraction experiment and acceptance-to-extraction
bound; this type does not manufacture either from a single transcript. -/
structure RecoveryRequest (Environment : Type u) (Output : Type v) (Witness : Type w)
    [MeasurableSpace Output] where
  experiment : Experiment Environment Output
  admissible : Environment → Prop
  requiresRecovery : Output → Prop
  recover : Output → Option Witness
  validWitness : Output → Witness → Prop
  measurable_failure : MeasurableSet {out | requiresRecovery out ∧
    ¬ ∃ witness, recover out = some witness ∧ validWitness out witness}
  error : Environment → ℝ≥0∞

@[expose] def RecoveryRequest.toUpper {E : Type u} {O : Type v} {W : Type w} [MeasurableSpace O]
    (request : RecoveryRequest E O W) : UpperRequest E O where
  experiment := request.experiment
  admissible := request.admissible
  event := {out | request.requiresRecovery out ∧
    ¬ ∃ witness, request.recover out = some witness ∧ request.validWitness out witness}
  measurable_event := request.measurable_failure
  bound := request.error

@[expose] def RecoveryRequest.Holds {E : Type u} {O : Type v} {W : Type w}
    [MeasurableSpace O] (request : RecoveryRequest E O W) : Prop := request.toUpper.Holds

end ProtocolProof
