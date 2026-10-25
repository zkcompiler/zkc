module

public import ZkcSecurity.FiatShamir.Honest

@[expose] public section

/-! Honest execution with fresh private samples and one shared public ROM.
The uniform summand forwards every draw independently. Only the transcript
summand reads or writes the cache. The final cache is part of the observation;
fixing a transcript table leaves the private sampling probabilistic. -/

set_option autoImplicit false
namespace ZkcSecurity.FiatShamir.HonestSampling
open OracleComp OracleSpec

variable {E A : Type} {Raw : E → Type}

abbrev Spec (Raw : E → Type) := unifSpec + TranscriptOracle.Spec Raw

section Experiment
variable [DecidableEq E] [∀ event, SampleableType (Raw event)]

/-- One cache encloses the entire computation, not one cache per participant. -/
def run (computation : OracleComp (Spec Raw) A) :
    ProbComp (A × (TranscriptOracle.Spec Raw).QueryCache) :=
  (simulateQ (TranscriptOracle.Spec Raw).romImpl computation).run ∅

/-- Stops, failed input preparation and rejection all remain failure mass. -/
noncomputable def failure (computation : OracleComp (Spec Raw) A) (success : A → Prop) : ENNReal :=
  1 - Pr{let observed ← run computation}[success observed.1]

theorem failure_eq_unsuccessful (computation : OracleComp (Spec Raw) A) (success : A → Prop) :
    failure computation success = Pr{let observed ← run computation}[¬ success observed.1] :=
  (prEvent_not_eq_one_sub _ _).symm

/-- Conservative extension of the complete old experiment, including the
final cache. This is stronger than equality of acceptance probabilities. -/
theorem run_transcript (computation : OracleComp (TranscriptOracle.Spec Raw) A) :
    run (Raw := Raw) (liftM computation) = Honest.run computation := by
  unfold run Honest.run
  rw [QueryImpl.simulateQ_add_liftM_right]

theorem failure_transcript (computation : OracleComp (TranscriptOracle.Spec Raw) A)
    (success : A → Prop) : failure (Raw := Raw) (liftM computation) success = Honest.failure computation success := by
  simp only [failure, Honest.failure, run_transcript]

/-- A fixed-table proof must still quantify over the support of fresh coins.
It cannot identify two samples merely because their nominal types agree. -/
theorem success_probability_one_iff (computation : OracleComp (Spec Raw) A) (success : A → Prop) :
    Pr{let observed ← run computation}[success observed.1] = 1 ↔
      ∀ answers : QueryImpl (TranscriptOracle.Spec Raw) Id,
        Pr{let observed ← simulateQ (unifFwdAnswerImpl answers) computation}[success observed] = 1 := by
  rw [run, prEvent_eq_one_simulateQ_romImpl_run_iff]
  simp [QueryCache.AgreesWithFn]

theorem failure_zero_of_all_tables (computation : OracleComp (Spec Raw) A) (success : A → Prop)
    (agreement : ∀ answers : QueryImpl (TranscriptOracle.Spec Raw) Id,
      Pr{let observed ← simulateQ (unifFwdAnswerImpl answers) computation}[success observed] = 1) :
    failure computation success = 0 := by
  unfold failure
  rw [(success_probability_one_iff computation success).mpr agreement, tsub_self]

theorem failure_one_of_all_tables (computation : OracleComp (Spec Raw) A) (success : A → Prop)
    (failed : ∀ answers : QueryImpl (TranscriptOracle.Spec Raw) Id,
      Pr{let observed ← simulateQ (unifFwdAnswerImpl answers) computation}[¬ success observed] = 1) :
    failure computation success = 1 := by
  rw [failure_eq_unsuccessful]
  exact (success_probability_one_iff computation (fun observed => ¬ success observed)).mpr failed

/-- Private sampling retains any existing public cache. The equation holds
at arbitrary pre-query state, so it also applies inside adaptive continuations. -/
theorem private_preserves_cache (computation : ProbComp A)
    (cache : (TranscriptOracle.Spec Raw).QueryCache) :
    (simulateQ (TranscriptOracle.Spec Raw).romImpl
      (liftM computation : OracleComp (Spec Raw) A)).run cache =
      (fun value => (value, cache)) <$> computation :=
  OracleSpec.simulateQ_romImpl_liftM_run computation cache

end Experiment
end ZkcSecurity.FiatShamir.HonestSampling
