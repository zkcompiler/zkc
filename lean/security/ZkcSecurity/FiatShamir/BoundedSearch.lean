module

public import ZkcSecurity.FiatShamir.Laws
public import VCVio.OracleComp.QueryTracking.QueryBound
public import VCVio.OracleComp.EvalDist.Measure
public import VCVio.EvalDist.Monad.Branch

@[expose] public section

/-! Finite honest search for a passing accepted-value decoder.

The search visits an explicit ordered candidate list, stops at the first
successful trial, and counts every reached trial, including failures. `none`
means that the list was exhausted; it is not a successful proof. A trial is an
oracle computation returning an optional value. Hardware failures and custody
are not interpreted by this mathematical search.

The probability results concern fresh probabilistic trials. Applying them to a
cached random oracle requires a separate freshness/simulation theorem. In
particular, repeating one nonce against a cached oracle is not an independent
trial. The bound includes challenge-decoder refusal, not just the gate test.
-/
set_option autoImplicit false

namespace ZkcSecurity.FiatShamir.BoundedSearch
open OracleComp OracleSpec MeasureTheory
open scoped ENNReal

variable {ι Witness Value : Type} {spec : OracleSpec ι}

/-- First successful candidate and the number of actual trial evaluations. -/
def run (trial : Witness → OracleComp spec (Option Value)) :
    List Witness → OracleComp spec (Option (Witness × Value) × Nat)
  | [] => pure (none, 0)
  | witness :: rest => do
      match ← trial witness with
      | some value => pure (some (witness, value), 1)
      | none =>
        let result ← run trial rest
        pure (result.1, result.2 + 1)

/-- A search does not spend a trial after the first successful candidate. -/
theorem run_success (trial : Witness → OracleComp spec (Option Value))
    (witness : Witness) (value : Value) (rest : List Witness)
    (success : trial witness = pure (some value)) :
    run trial (witness :: rest) = pure (some (witness, value), 1) := by
  simp [run, success]

/-- Every reached output counts at most the requested number of candidates. -/
theorem attempts_le (trial : Witness → OracleComp spec (Option Value))
    (candidates : List Witness) (result : Option (Witness × Value) × Nat)
    (reached : result ∈ support (run trial candidates)) : result.2 ≤ candidates.length := by
  induction candidates generalizing result with
  | nil =>
    have same : result = (none, 0) := by simpa [run] using reached
    simp [same]
  | cons witness rest ih =>
    simp only [run, mem_support_bind_iff] at reached
    obtain ⟨answer, _, reached⟩ := reached
    cases answer with
    | some value =>
      have same : result = (some (witness, value), 1) := by simpa using reached
      simp [same]
    | none =>
      simp only [mem_support_bind_iff] at reached
      obtain ⟨tail, member, returned⟩ := reached
      have same : result = (tail.1, tail.2 + 1) := by simpa using returned
      subst result
      exact Nat.succ_le_succ (ih tail member)

/-- Successful output is an actual candidate whose trial returned that value.
This supplies the honest re-check property without choosing a witness by choice. -/
theorem returned_valid (trial : Witness → OracleComp spec (Option Value))
    (valid : Witness → Value → Prop)
    (trials : ∀ witness value, some value ∈ support (trial witness) → valid witness value)
    (candidates : List Witness) (witness : Witness) (value : Value) (count : Nat)
    (reached : (some (witness, value), count) ∈ support (run trial candidates)) :
    witness ∈ candidates ∧ valid witness value := by
  induction candidates generalizing count with
  | nil => simp [run] at reached
  | cons current rest ih =>
    simp only [run, mem_support_bind_iff] at reached
    obtain ⟨answer, member, reached⟩ := reached
    cases answer with
    | some output =>
      have same : (some (witness, value), count) = (some (current, output), 1) := by
        simpa using reached
      have pair := Option.some.inj (congrArg Prod.fst same)
      cases pair
      exact ⟨List.mem_cons_self, trials _ _ member⟩
    | none =>
      simp only [mem_support_bind_iff] at reached
      obtain ⟨tail, member, returned⟩ := reached
      have same : (some (witness, value), count) = (tail.1, tail.2 + 1) := by simpa using returned
      have first : some (witness, value) = tail.1 := congrArg Prod.fst same
      have tailMember : (some (witness, value), tail.2) ∈ support (run trial rest) := by
        rw [first]
        exact member
      obtain ⟨inRest, correct⟩ := ih tail.2 tailMember
      exact ⟨List.mem_cons_of_mem _ inRest, correct⟩

/-- A bound on primitive calls is independent of the count of logical trials.
A multi-block gate may have `perTrial > 1`; it is never charged as one hash call
merely because it is one logical request. -/
theorem queryBound (trial : Witness → OracleComp spec (Option Value))
    (perTrial : Nat) (bounded : ∀ witness, IsTotalQueryBound (trial witness) perTrial)
    (candidates : List Witness) :
    IsTotalQueryBound (run trial candidates) (candidates.length * perTrial) := by
  induction candidates with
  | nil => trivial
  | cons witness rest ih =>
    rw [List.length_cons, Nat.succ_mul, Nat.add_comm]
    apply isTotalQueryBound_bind (bounded witness)
    intro answer
    cases answer with
    | some value => trivial
    | none =>
      simpa only [Nat.add_zero] using
        (isTotalQueryBound_bind ih (n₂ := 0) (fun _ => by trivial))

section Fresh
variable (trial : Witness → ProbComp (Option Value))

/-- Exact exhaustion recurrence for fresh independent probabilistic trials. -/
theorem exhaustion_cons (witness : Witness) (rest : List Witness) :
    Pr{let result ← run trial (witness :: rest)}[result.1 = none] =
      Pr{let answer ← trial witness}[answer = none] *
        Pr{let result ← run trial rest}[result.1 = none] := by
  classical
  rw [run]
  apply prEvent_bind_eq_mul_of_ite (trial witness) _ (· = none) _
    (run trial rest) (fun result => result.1 = none)
  intro answer
  cases answer <;> simp

/-- Varying fresh trial laws multiply their actual failure probabilities. -/
theorem exhaustion (candidates : List Witness) :
    Pr{let result ← run trial candidates}[result.1 = none] =
      (candidates.map fun witness => Pr{let answer ← trial witness}[answer = none]).prod := by
  induction candidates with
  | nil => simp [run]
  | cons witness rest ih => rw [exhaustion_cons, ih]; rfl

/-- A uniform upper bound on the complete trial's failure gives the finite
geometric exhaustion bound. No claim of independence is inferred from marginals. -/
theorem exhaustion_le (candidates : List Witness) (failure : ENNReal)
    (bounded : ∀ witness ∈ candidates, Pr{let answer ← trial witness}[answer = none] ≤ failure) :
    Pr{let result ← run trial candidates}[result.1 = none] ≤ failure ^ candidates.length := by
  induction candidates with
  | nil => simp [run]
  | cons witness rest ih =>
    rw [exhaustion_cons, List.length_cons, pow_succ']
    exact mul_le_mul' (bounded witness List.mem_cons_self)
      (ih fun next member => bounded next (List.mem_cons_of_mem _ member))

/-- A lower bound on successful accepted values includes both passing the gate
and successful challenge decoding. Its complement controls honest exhaustion. -/
theorem exhaustion_le_of_success (candidates : List Witness) (success : ENNReal)
    (successful : ∀ witness ∈ candidates,
      success ≤ Pr{let answer ← trial witness}[answer.isSome]) :
    Pr{let result ← run trial candidates}[result.1 = none] ≤ (1 - success) ^ candidates.length := by
  apply exhaustion_le trial candidates (1 - success)
  intro witness member
  have complement : Pr{let answer ← trial witness}[answer = none] =
      1 - Pr{let answer ← trial witness}[answer.isSome] := by
    rw [← prEvent_not_eq_one_sub]
    apply prEvent_congr
    intro answer
    cases answer <;> simp
  rw [complement]
  exact tsub_le_tsub_left (successful witness member) 1

/-- Expected logical attempts, measured on the actual returned counter.
Primitive hash work is a separate observation and uses the per-trial budget. -/
noncomputable def expectedAttempts (candidates : List Witness) : ENNReal :=
  ∫⁻ (count : Nat), (count : ENNReal) ∂𝒟[Prod.snd <$> run trial candidates]

/-- Reaching a candidate always costs one trial; only failure reaches the tail. -/
theorem expectedAttempts_cons (witness : Witness) (rest : List Witness) :
    expectedAttempts trial (witness :: rest) =
      1 + Pr{let answer ← trial witness}[answer = none] * expectedAttempts trial rest := by
  classical
  let : MeasurableSpace (Option Value) := ⊤
  rw [expectedAttempts, run, map_bind]
  rw [lintegral_evalDist_bind_of_discrete _ _ Measurable.of_discrete]
  have inner (answer : Option Value) :
      (∫⁻ (count : Nat), (count : ENNReal) ∂𝒟[Prod.snd <$>
        (match answer with
        | some value => pure (some (witness, value), 1)
        | none => do
          let result ← run trial rest
          pure (result.1, result.2 + 1))]) =
        1 + ({none} : Set (Option Value)).indicator
          (fun _ => expectedAttempts trial rest) answer := by
    cases answer with
    | some value => simp
    | none =>
      simp only [map_bind, map_pure]
      rw [show (do let result ← run trial rest; pure (result.2 + 1)) =
        (fun result => result.2 + 1) <$> run trial rest by
          simp [map_eq_bind_pure_comp]]
      rw [lintegral_evalDist_map_add_nat]
      simp [expectedAttempts, add_comm]
  simp_rw [inner]
  rw [lintegral_add_left measurable_const, lintegral_indicator_const (measurableSet_singleton none)]
  simp only [lintegral_const, OracleComp.evalDist_apply_univ_eq_one, mul_one]
  rw [prEvent_eq_evalDist_singleton]
  congr 1
  exact mul_comm _ _

/-- Exact finite geometric work for fresh trials with the same failure mass. -/
theorem expectedAttempts_eq_sum (candidates : List Witness) (failure : ENNReal)
    (exactFailure : ∀ witness ∈ candidates,
      Pr{let answer ← trial witness}[answer = none] = failure) :
    expectedAttempts trial candidates = ∑ index ∈ Finset.range candidates.length, failure ^ index := by
  induction candidates with
  | nil => simp [expectedAttempts, run]
  | cons witness rest ih =>
    rw [expectedAttempts_cons, exactFailure witness List.mem_cons_self,
      ih (fun next member => exactFailure next (List.mem_cons_of_mem _ member)),
      List.length_cons, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', ← Finset.mul_sum, add_comm]

/-- Fresh trials need not have the same law: a failure bound gives a geometric
upper bound on the work of the actual bounded search. -/
theorem expectedAttempts_le_sum (candidates : List Witness) (failure : ENNReal)
    (bounded : ∀ witness ∈ candidates,
      Pr{let answer ← trial witness}[answer = none] ≤ failure) :
    expectedAttempts trial candidates ≤ ∑ index ∈ Finset.range candidates.length, failure ^ index := by
  induction candidates with
  | nil => simp [expectedAttempts, run]
  | cons witness rest ih =>
    rw [expectedAttempts_cons, List.length_cons, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', ← Finset.mul_sum]
    rw [add_comm _ 1]
    exact add_le_add le_rfl (mul_le_mul' (bounded witness List.mem_cons_self)
      (ih fun next member => bounded next (List.mem_cons_of_mem _ member)))

end Fresh
end ZkcSecurity.FiatShamir.BoundedSearch
