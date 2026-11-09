module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Requests precede methods

An experiment includes its complete probability law. A request fixes admissibility, the
observation, and the numerical claim before evidence is selected. Assumptions remain theorem
premises; evidence cannot add an unreported condition to one of these meanings.

`UpperRequest` and `LowerRequest` are general quantitative requests. The security-facing
constructors below compute their events rather than allowing a proof method to replace them.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProtocolProof

universe u v w

/-- A complete experiment for each fixed environment, including all failure outcomes. -/
structure Experiment (Environment : Type u) (Output : Type v) [MeasurableSpace Output] where
  run : Environment → Measure Output
  normalized : ∀ environment, IsProbabilityMeasure (run environment)

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

/-- Soundness tests truth of the statement returned by the experiment, allowing adaptive choice.
The environment type and admissibility predicate fix the quantified adversary interface. -/
structure SoundnessRequest (Environment : Type u) (Output : Type v) (Statement : Type w)
    [MeasurableSpace Output] where
  experiment : Experiment Environment Output
  admissible : Environment → Prop
  accepts : Output → Prop
  statement : Output → Statement
  trueStatement : Statement → Prop
  measurable_bad : MeasurableSet {out | accepts out ∧ ¬trueStatement (statement out)}
  error : Environment → ℝ≥0∞

/-- The false-acceptance event is derived from the request, never supplied by evidence. -/
@[expose] def SoundnessRequest.toUpper {E : Type u} {O : Type v} {X : Type w} [MeasurableSpace O]
    (request : SoundnessRequest E O X) : UpperRequest E O where
  experiment := request.experiment
  admissible := request.admissible
  event := {out | request.accepts out ∧ ¬request.trueStatement (request.statement out)}
  measurable_event := request.measurable_bad
  bound := request.error

@[expose] def SoundnessRequest.Holds {E : Type u} {O : Type v} {X : Type w} [MeasurableSpace O]
    (request : SoundnessRequest E O X) : Prop := request.toUpper.Holds

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

/-- A fixed simulator receives public inputs only. The property quantifies over every valid
private witness afterwards; it is not `∀ witness, ∃ simulator`. Observations must include the
view claimed by the request. This is statistical view security, not a computational reduction. -/
structure ViewRequest (Public : Type u) (Witness : Type v) (View : Type w)
    [MeasurableSpace View] where
  real : Experiment (Public × Witness) View
  simulated : Experiment Public View
  valid : Public → Witness → Prop
  error : Public → ℝ≥0∞

@[expose] def ViewRequest.Holds {P : Type u} {W : Type v} {V : Type w} [MeasurableSpace V]
    (request : ViewRequest P W V) : Prop :=
  ∀ publicInput witness, request.valid publicInput witness →
    ∀ event, MeasurableSet event →
      request.real.run (publicInput, witness) event ≤
        request.simulated.run publicInput event + request.error publicInput ∧
      request.simulated.run publicInput event ≤
        request.real.run (publicInput, witness) event + request.error publicInput

end ProtocolProof
