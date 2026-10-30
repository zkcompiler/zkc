import ZkcSecurity.Claims.Completeness
import ZkcSecurity.Claims.Methods.HonestReadbackCompleteness
import ZkcSecurityExamples.RootProperties.SmallSumcheck

/-! Exact-run WP controls. The cache handler uses VCVio's actual `withCaching`,
with an additional counter and ordered events. The final test re-establishes
the existing SmallSumcheck canonical claim through the pointwise WP route.
No adversary or probabilistic WP instance is installed. -/

set_option autoImplicit false
namespace TestsSecurity.HonestWeakestPrecondition
open PIR PIR.WeakestPrecondition Std.WP
open OracleComp OracleSpec ZkcSecurity.FiatShamir

abbrev CacheSpec := OracleSpec.ofFn (fun _ : Nat => Fin 2)
abbrev State := CacheSpec.QueryCache × Nat
abbrev signature : Signature := ⟨Nat, fun _ => Fin 2⟩

def cachedHandler (answers : QueryImpl CacheSpec Id) : Handler signature State Nat :=
  fun key state =>
    let observed := (answers.withCaching key).run state.1
    ⟨.returned observed.1, (observed.2, state.2 + 1), [key]⟩

-- These are the actual probabilistic cache steps. A fresh entry remains a
-- uniform draw; the pointwise handler does not replace this experiment.
theorem randomOracle_cache_hit (key : Nat) (cache : CacheSpec.QueryCache) (reply : Fin 2)
    (found : cache key = some reply) :
    (CacheSpec.randomOracle key).run cache = pure (reply, cache) :=
  Honest.cached key cache reply found

theorem randomOracle_cache_miss (key : Nat) (cache : CacheSpec.QueryCache)
    (absent : cache key = none) :
    (CacheSpec.randomOracle key).run cache =
      ($ᵗ (Fin 2)) >>= fun reply => pure (reply, cache.cacheQuery key reply) :=
  Honest.fresh key cache absent

def query (key : Nat) : Process signature (Fin 2) := .call key .done

def twice (key : Nat) : Process signature (Fin 2 × Fin 2) := do
  let first ← query key
  let second ← query key
  pure (first, second)

theorem query_spec (answers : QueryImpl CacheSpec Id) (key : Nat)
    (post : Fin 2 → State → List Nat → Prop)
    (stopped : Stop → State → List Nat → Prop) :
    (letI := wpMonad (cachedHandler answers)
     Triple (query key)
       (fun state preceding =>
         let observed := (answers.withCaching key).run state.1
         post observed.1 (observed.2, state.2 + 1) (preceding ++ [key]))
       post estack⟨stopped⟩) := by
  simpa only [query, cachedHandler, satisfies] using
    (call_spec (cachedHandler answers) key post stopped)

theorem uncached_twice (answers : QueryImpl CacheSpec Id) (key : Nat)
    (cache : CacheSpec.QueryCache) (count : Nat) (preceding : List Nat)
    (absent : cache key = none) :
    (letI := wpMonad (cachedHandler answers)
     Triple (twice key) (fun state history => state = (cache, count) ∧ history = preceding)
       (fun result state history => result = (answers key, answers key) ∧
         state = (cache.cacheQuery key (answers key), count + 2) ∧
         history = preceding ++ [key, key])
       estack⟨fun _ _ _ => False⟩) := by
  apply (triple_iff_run _ _ _ _ _).mpr
  rintro state history ⟨rfl, rfl⟩
  simp only [twice, query, Bind.bind, Pure.pure, Process.bind, Process.run,
    cachedHandler, Execution.follow, satisfies]
  rw [QueryImpl.withCaching_run_none answers absent]
  dsimp only [Functor.map, Pure.pure]
  rw [QueryImpl.withCaching_run_some answers (cache.cacheQuery_self key (answers key))]
  simp only [Nat.add_assoc, List.singleton_append, and_true, true_and, Prod.mk.injEq]
  exact ⟨rfl, rfl⟩

set_option experimental.vcgen true in
theorem cached_twice (answers : QueryImpl CacheSpec Id) (key : Nat)
    (cache : CacheSpec.QueryCache) (reply : Fin 2) (count : Nat) (preceding : List Nat)
    (found : cache key = some reply) :
    (letI := wpMonad (cachedHandler answers)
     Triple (twice key) (fun state history => state = (cache, count) ∧ history = preceding)
       (fun result state history => result = (reply, reply) ∧
         state = (cache, count + 2) ∧ history = preceding ++ [key, key])
       estack⟨fun _ _ _ => False⟩) :=
  letI := wpMonad (cachedHandler answers)
  by
    unfold twice
    vcgen [query_spec answers]
    rcases ‹_ ∧ _› with ⟨rfl, rfl⟩
    simp only [QueryImpl.withCaching_run_some answers found]
    dsimp only [Pure.pure]
    rw [QueryImpl.withCaching_run_some answers found]
    simp [List.append_assoc, Nat.add_assoc]
    exact ⟨rfl, rfl⟩

-- An existing cache entry wins even if the fixed fallback table disagrees.
theorem cached_answer_overrides_table (answers : QueryImpl CacheSpec Id) (key : Nat)
    (cache : CacheSpec.QueryCache) (reply : Fin 2) (count : Nat)
    (found : cache key = some reply) (different : reply ≠ answers key) :
    (twice key).run (cachedHandler answers) (cache, count) ≠
      ⟨.returned (answers key, answers key), (cache, count + 2), [key, key]⟩ := by
  have returned := (triple_iff_returned _ _ _ _).mp
    (cached_twice answers key cache reply count [] found) (cache, count) [] ⟨rfl, rfl⟩
  obtain ⟨value, outcome, post⟩ := returned
  intro wrong
  rw [wrong] at outcome
  have same := Outcome.returned.inj outcome
  exact different (congrArg Prod.fst (post.1.symm.trans same.symm))

def stoppingHandler (answers : QueryImpl CacheSpec Id) : Handler signature State Nat :=
  fun key state =>
    if key = 7 then ⟨.stopped .exhausted, (state.1, state.2 + 10), [7, 8]⟩
    else cachedHandler answers key state

def stoppedPrefix : Process signature (Fin 2) := do
  let _ ← query 1
  let _ ← query 7
  query 9

-- The handler stop retains its own updates and the entire preceding history.
-- Neither the reply continuation nor key 9 is reached.
theorem handler_stop_retains_state_and_events (answers : QueryImpl CacheSpec Id)
    (cache : CacheSpec.QueryCache) (count : Nat) (preceding : List Nat) :
    (letI := wpMonad (stoppingHandler answers)
     Triple stoppedPrefix (fun state history => state = (cache, count) ∧ history = preceding)
       (fun _ _ _ => False)
       estack⟨fun reason state history => reason = .exhausted ∧
         state = ((answers.withCaching 1).run cache |>.2, count + 11) ∧
         history = preceding ++ [1, 7, 8]⟩) := by
  apply (triple_iff_run _ _ _ _ _).mpr
  rintro state history ⟨rfl, rfl⟩
  simp [stoppedPrefix, query, Process.run, Bind.bind, Pure.pure, Process.bind, stoppingHandler,
    cachedHandler, Execution.follow, satisfies, Nat.add_assoc]

theorem stops_are_not_success (answers : QueryImpl CacheSpec Id) (reason : Stop) (state : State) :
    ¬ (letI := wpMonad (cachedHandler answers)
       Triple (Process.halt reason : Process signature Bool)
         (fun current _ => current = state) (fun _ _ _ => True)
         estack⟨fun _ _ _ => False⟩) := by
  intro triple
  have impossible := (triple_iff_returned _ _ _ _).mp triple state [] rfl
  obtain ⟨_, returned, _⟩ := impossible
  cases returned

theorem returned_false_is_not_a_stop (answers : QueryImpl CacheSpec Id) :
    (letI := wpMonad (cachedHandler answers)
     Triple (pure false : Process signature Bool) (fun _ _ => True)
       (fun value _ _ => value = false) estack⟨fun _ _ _ => False⟩) := by
  apply (triple_iff_run _ _ _ _ _).mpr
  intro state history _
  rfl

-- The exact adequacy theorem also permits a deliberately selected stop policy.
theorem stop_policy_is_explicit (answers : QueryImpl CacheSpec Id) (reason : Stop) :
    (letI := wpMonad (cachedHandler answers)
     Triple (Process.halt reason : Process signature Bool) (fun _ _ => True)
       (fun _ _ _ => False) estack⟨fun observed _ _ => observed = reason⟩) := by
  apply (triple_iff_run _ _ _ _ _).mpr
  intro state history _
  rfl

open Zkc.Source.Structured Zkc.Construction ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Domains.PrimeField

noncomputable section

local instance : ∀ event : Domain.Event blsScalarModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem smallSumcheck_perfect_via_wp : CanonicalCompleteness SmallSumcheck.subject 0 := by
  apply perfect_of_pointwise_wp SmallSumcheck.subject
    ZkcSecurity.Examples.Components.SmallSumcheck.Formula.nonvacuous (by rfl) (by rfl)
  intro inputs related honest producer validator prepared answers
  have aligned := Readback.of_abi SmallSumcheck.subject
    Components.SmallSumcheckABI.abi ZkcSecurity.Examples.RootProperties.SmallSumcheck.abi_readback
    inputs related honest producer validator prepared
  exact aligned.pair_wp _ _ _ _ _ _ _ _ answers

end

#print axioms uncached_twice
#print axioms cached_twice
#print axioms handler_stop_retains_state_and_events
#print axioms stops_are_not_success
#print axioms smallSumcheck_perfect_via_wp
#print axioms PIR.WeakestPrecondition.triple_iff_run
#print axioms ZkcSecurity.FiatShamir.HonestCompiled.pair_success_iff_wp
#print axioms ZkcSecurity.Claims.HonestPair.perfect_of_pointwise_wp

end TestsSecurity.HonestWeakestPrecondition
