module

public import ZkcSecurity.Transformations.FiatShamir.TranscriptOracle
public import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

@[expose] public section

/-! Honest computations share one lazily sampled typed history oracle. The
cache encloses the entire computation, including both compiled participants.
No adversarial query bound or private-coin operation is introduced here. -/

set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.Honest
open OracleComp OracleSpec

variable {E A : Type} {Raw : E → Type}

section Experiment
variable [DecidableEq E] [∀ event, SampleableType (Raw event)]

/-- The complete observation includes the final oracle cache. There is exactly
one initially empty cache, outside all phases of the supplied computation. -/
def run (computation : OracleComp (TranscriptOracle.Spec Raw) A) : ProbComp (A × (TranscriptOracle.Spec Raw).QueryCache) :=
  (simulateQ randomOracle computation).run ∅

/-- The complement counts all mass not assigned to successful acceptance.
It remains the intended definition if a later interpreter is partial. -/
noncomputable def failure (computation : OracleComp (TranscriptOracle.Spec Raw) A) (success : A → Prop) : ENNReal :=
  1 - Pr{let observed ← run computation}[success observed.1]

/-- The present OracleComp experiment is lossless; explicit PIR stops are
returned observations, not missing probability mass. -/
theorem lossless (computation : OracleComp (TranscriptOracle.Spec Raw) A) :
    Pr{let _ ← run computation}[True] = 1 := prEvent_true_eq_one _

/-- Only after normalization has been established may the complement be read
as the probability of a returned unsuccessful observation. -/
theorem failure_eq_unsuccessful (computation : OracleComp (TranscriptOracle.Spec Raw) A) (success : A → Prop) :
    failure computation success = Pr{let observed ← run computation}[¬ success observed.1] := by
  exact (prEvent_not_eq_one_sub _ _).symm

/-- The all-table law is connected to the actual cached experiment, rather
than serving as an alternative definition of completeness. -/
theorem success_probability_one_iff (computation : OracleComp (TranscriptOracle.Spec Raw) A) (success : A → Prop) :
    Pr{let observed ← run computation}[success observed.1] = 1 ↔
      ∀ answers : QueryImpl (TranscriptOracle.Spec Raw) Id, success (evalWithAnswerFn answers computation) := by
  rw [run, prEvent_eq_one_simulateQ_randomOracle_run_iff]
  simp [QueryCache.AgreesWithFn]

theorem failure_zero_of_all_tables (computation : OracleComp (TranscriptOracle.Spec Raw) A) (success : A → Prop)
    (agreement : ∀ answers : QueryImpl (TranscriptOracle.Spec Raw) Id,
      success (evalWithAnswerFn answers computation)) : failure computation success = 0 := by
  unfold failure
  rw [(success_probability_one_iff computation success).mpr agreement, tsub_self]

theorem failure_one_of_all_tables (computation : OracleComp (TranscriptOracle.Spec Raw) A) (success : A → Prop)
    (failureEverywhere : ∀ answers : QueryImpl (TranscriptOracle.Spec Raw) Id,
      ¬ success (evalWithAnswerFn answers computation)) : failure computation success = 1 := by
  rw [failure_eq_unsuccessful]
  exact (success_probability_one_iff computation (fun value => ¬ success value)).mpr failureEverywhere

end Experiment

section Cache
variable {D : Type} {R : D → Type} [DecidableEq D] [∀ key, SampleableType (R key)]

/-- A memoized query returns the existing typed answer and leaves the cache
unchanged. It is not a fresh private-coin sample. -/
theorem cached (key : D) (cache : (OracleSpec.ofFn R).QueryCache) (answer : R key)
    (found : cache key = some answer) :
    ((OracleSpec.ofFn R).randomOracle key).run cache = pure (answer, cache) := by
  rw [randomOracle.run_eq, found]

/-- A fresh key draws uniformly in its own carrier and installs that answer
in the shared cache before the next phase can query it. -/
theorem fresh (key : D) (cache : (OracleSpec.ofFn R).QueryCache)
    (absent : cache key = none) :
    ((OracleSpec.ofFn R).randomOracle key).run cache =
      ($ᵗ (R key)) >>= fun answer => pure (answer, cache.cacheQuery key answer) := by
  rw [randomOracle.run_eq, absent]

end Cache
end ZkcSecurity.FiatShamir.Honest
