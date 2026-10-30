import ZkcSecurity.Transformations.FiatShamir.BoundedSearch

/-! Honest finite search is a probabilistic computation, not an assumption that
repeated cached nonces are independent. These controls exercise empty search,
early success, exhaustion, fresh versus cached trials, and primitive-call cost. -/
set_option autoImplicit false
namespace TestsSecurity.BoundedSearch
open OracleComp OracleSpec
open ZkcSecurity.FiatShamir.BoundedSearch
open scoped ENNReal

private def fresh (_ : Nat) : ProbComp (Option Unit) := do
  let passes ← $ᵗ Bool
  pure (if passes then some () else none)

private theorem failure (candidate : Nat) :
    Pr{let answer ← fresh candidate}[answer = none] = (2 : ENNReal)⁻¹ := by
  rw [show fresh candidate = (fun bit : Bool => if bit then some () else none) <$> ($ᵗ Bool) by
    simp [fresh, map_eq_bind_pure_comp], prEvent_map]
  have same : (fun bit : Bool => (if bit then some () else none) = none) = (· = false) := by
    funext bit
    cases bit <;> simp
  rw [same, SampleableType.prEvent_uniformSample_eq_singleton]
  simp

/-- An empty search has not produced a passing witness. -/
example : run fresh [] = pure (none, 0) := rfl

/-- A successful first candidate stops, even with a large unused suffix. -/
example (rest : List Nat) :
    run (fun _ : Nat => (pure (some ()) : ProbComp (Option Unit))) (7 :: rest) =
      pure (some (7, ()), 1) := run_success _ _ _ _ rfl

/-- Exhaustion is an explicit failure and includes both spent attempts. -/
example : run (fun _ : Nat => (pure none : ProbComp (Option Unit))) [0, 1] =
    pure (none, 2) := by simp [run]

/-- Two fresh trials have failure one quarter, not one half. -/
theorem fresh_two : Pr{let result ← run fresh [0, 1]}[result.1 = none] = (4 : ENNReal)⁻¹ := by
  rw [exhaustion]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, failure]
  rw [← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
  norm_num

/-- The counted output gives expected work 1 + 1/2 for two fresh trials. -/
theorem expected_two : expectedAttempts fresh [0, 1] = 1 + (2 : ENNReal)⁻¹ := by
  rw [expectedAttempts_eq_sum fresh [0, 1] (2 : ENNReal)⁻¹ (fun candidate _ => failure candidate)]
  norm_num [Finset.sum_range_succ]

/-- Accepted values may be variable-length vectors; the probability theorem
requires no finite enumeration of the decoder's output type. -/
example (trial : Nat → ProbComp (Option (List Bool))) (candidates : List Nat)
    (success : ENNReal)
    (successful : ∀ witness ∈ candidates,
      success ≤ Pr{let answer ← trial witness}[answer.isSome]) :
    Pr{let result ← run trial candidates}[result.1 = none] ≤
      (1 - success) ^ candidates.length :=
  exhaustion_le_of_success trial candidates success successful

/-- The same cached answer is reused for both candidates. The decoder has the
same one-trial marginal as `fresh`, but this is a different joint computation. -/
private def cached : ProbComp (Option (Nat × Unit) × Nat) := do
  let passes ← $ᵗ Bool
  run (fun _ : Nat => pure (if passes then some () else none)) [0, 0]

private theorem cached_expanded : cached =
    (fun passes : Bool => if passes then (some (0, ()), 1) else (none, 2)) <$> ($ᵗ Bool) := by
  simp only [cached, map_eq_bind_pure_comp]
  apply bind_congr
  intro passes
  cases passes <;> simp [run]

/-- A cached nonce cannot use the independent-trial completeness bound. -/
theorem cached_failure : Pr{let result ← cached}[result.1 = none] = (2 : ENNReal)⁻¹ := by
  rw [cached_expanded]
  rw [prEvent_map]
  have same : (fun bit : Bool => (if bit then (some (0, ()), 1) else (none, 2)).1 = none) =
      (· = false) := by
    funext bit
    cases bit <;> simp
  rw [same, SampleableType.prEvent_uniformSample_eq_singleton]
  simp

theorem cached_not_fresh_bound :
    ¬ Pr{let result ← cached}[result.1 = none] ≤ (4 : ENNReal)⁻¹ := by
  rw [cached_failure]
  norm_num

private abbrev bitSpec := OracleSpec.ofFn (fun _ : Unit => Bool)
private def twoCalls (_ : Nat) : OracleComp bitSpec (Option Unit) := do
  let first ← query (spec := bitSpec) ()
  let second ← query (spec := bitSpec) ()
  pure (if first && second then some () else none)

private theorem twoCalls_bound (candidate : Nat) : IsTotalQueryBound (twoCalls candidate) 2 := by
  change 0 < 2 ∧ ∀ _ : Bool, 0 < 1 ∧ ∀ _ : Bool, True
  simp

/-- The two-trial search allows four primitive calls, not two. -/
example : IsTotalQueryBound (run twoCalls [0, 1]) 4 :=
  queryBound twoCalls 2 twoCalls_bound [0, 1]

#print axioms ZkcSecurity.FiatShamir.BoundedSearch.exhaustion_le_of_success
#print axioms ZkcSecurity.FiatShamir.BoundedSearch.expectedAttempts_le_sum
#print axioms ZkcSecurity.FiatShamir.BoundedSearch.queryBound
#print axioms cached_not_fresh_bound
end TestsSecurity.BoundedSearch
