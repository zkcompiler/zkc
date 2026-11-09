import Zkc.Protocol.Logic.Oracle.PermutationExposure.Adaptive

/-! Kernel-checked controls for the shared two-sided permutation sampler.
All numeric event calculations use exact finite cardinalities. No executable cryptographic
primitive, source protocol or receipt is asserted by this file.
-/

set_option autoImplicit false

namespace TestsSecurity.PermutationExposure

open OracleComp OracleSpec
open ZkcSecurity.Probability.PermutationExposure
open scoped ENNReal

abbrev Small := Fin 2
abbrev Point := Small × Small

def noTargets {D : Type} [DecidableEq D] : Targets D := fun _ _ ↦ (∅, ∅)

theorem noTargets_bounded {D : Type} [DecidableEq D] (b : ℕ) :
    TargetBound (noTargets (D := D)) b := by
  intro s q
  simp [noTargets]

/-- At an empty prefix a single coordinate fiber has exactly half the four states. -/
theorem empty_forward_fiber :
    Pr{let result ← step (noTargets (D := Small)) ⟨.forward, (0, 0)⟩ State.empty}[
      result.1.1 = 0] = 1 / 2 := by
  rw [fresh_step_law _ _ _ (by simp [State.cached, State.empty]) (fun x ↦ x.1 = 0)]
  have count : (((State.empty (S := Point)).available .forward).filter
      (fun x ↦ x.1 = 0)).card = 2 := by decide
  rw [count]
  norm_num only [State.empty, Finset.card_empty, Nat.sub_zero, Fintype.card_fin,
    Nat.reducePow, Nat.cast_ofNat]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr
  norm_num

/-- Inverse calls sample the input, with the same initial uniform input-fiber law. -/
theorem empty_inverse_fiber :
    Pr{let result ← step (noTargets (D := Small)) ⟨.inverse, (0, 0)⟩ State.empty}[
      result.1.1 = 0] = 1 / 2 := by
  rw [fresh_step_law _ _ _ (by simp [State.cached, State.empty]) (fun x ↦ x.1 = 0)]
  have count : (((State.empty (S := Point)).available .inverse).filter
      (fun x ↦ x.1 = 0)).card = 2 := by decide
  rw [count]
  norm_num only [State.empty, Finset.card_empty, Nat.sub_zero, Fintype.card_fin,
    Nat.reducePow, Nat.cast_ofNat]
  apply (ENNReal.div_eq_div_iff (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).mpr
  norm_num

def onePair : State Point := State.empty.insert ⟨.forward, (0, 0)⟩ (1, 1) false

/-- Removing one state biases coordinate marginals; they are not uniform coordinates. -/
theorem exclusion_bias :
    Pr{let result ← step (noTargets (D := Small)) ⟨.forward, (0, 1)⟩ onePair}[
      result.1.1 = 1] = 1 / 3 := by
  rw [fresh_step_law _ _ _ (by decide) (fun x ↦ x.1 = 1)]
  have count : ((onePair.available .forward).filter (fun x ↦ x.1 = 1)).card = 1 := by
    decide
  rw [count]
  norm_num [onePair, State.insert, State.empty]

theorem empty_targets_zero (s : State Point) (q : Query Point) (good : s.bad = false) :
    Pr{let result ← step noTargets q s}[result.2.bad = true] = 0 := by
  by_cases cached : s.cached q
  · exact cached_bad_mass noTargets q s cached good
  · rw [step_fresh noTargets q s cached, prEvent_map]
    simp [noTargets, FiberHit, good]

/-- Repeating an exposed forward pair is cached despite arbitrary large target sets. -/
theorem duplicate_zero :
    Pr{let result ← step (fun _ _ ↦ (Finset.univ, Finset.univ))
        ⟨.forward, (0, 0)⟩ onePair}[result.2.bad = true] = 0 := by
  exact cached_bad_mass _ _ _ (by decide) (by decide)

/-- Querying the opposite direction of an exposed pair is also cached. -/
theorem mixed_direction_cache :
    onePair.cached ⟨.inverse, (1, 1)⟩ ∧
      onePair.answer ⟨.inverse, (1, 1)⟩ = (0, 0) := by decide

theorem duplicate_still_counts :
    ∀ result ∈ support (step (noTargets (D := Small)) ⟨.forward, (0, 0)⟩ onePair),
      result.2.calls = 2 := by
  intro result member
  simpa [onePair, State.empty] using step_calls noTargets ⟨.forward, (0, 0)⟩ onePair result member

def exhausted : State Point := ⟨Equiv.refl Point, Finset.univ, 4, by decide, false⟩

theorem exhausted_available_empty (direction : Direction) : exhausted.available direction = ∅ := by
  cases direction <;> decide

/-- Exhaustion cannot cause a fresh sample from an empty set: every valid query is cached. -/
theorem exhausted_cached (q : Query Point) : exhausted.cached q := by
  cases h : q.direction <;> simp [State.cached, exhausted, h]

theorem exhausted_zero (q : Query Point) :
    Pr{let result ← step (fun _ _ ↦ (Finset.univ, Finset.univ)) q exhausted}[
      result.2.bad = true] = 0 :=
  cached_bad_mass _ q exhausted (exhausted_cached q) rfl

/-- Empty carriers admit no primitive query at all. -/
theorem empty_carrier_no_query (q : Query (Fin 0 × Fin 0)) : False := q.point.1.elim0

theorem empty_carrier_state :
    (State.empty (S := Fin 0 × Fin 0)).calls = 0 ∧
      (State.empty (S := Fin 0 × Fin 0)).used.card = 0 := by decide

/-- A nonempty union of all coordinate fibers saturates the bound at one. -/
theorem saturated_fiber :
    Pr{let x ← draw (Finset.univ : Finset Point) (by decide)}[
      FiberHit Finset.univ Finset.univ x] = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro x _
  exact Or.inl (Finset.mem_univ _)

theorem outside_budget_domain : epsilon 2 4 0 = 1 ∧ epsilon 2 5 0 = 1 := by
  norm_num [epsilon]

theorem zero_budget (d b : ℕ) : epsilon d 0 b = if 0 < d ^ 2 then 0 else 1 := by
  simp [epsilon]

theorem exact_arithmetic : work 3 4 = 58 ∧ 5 * (4 * (4 - 1) / 2) + (3 + 4) * 4 = 58 := by
  decide

/-- A reply-adaptive mixed-direction program, with the cache hit charged as a third call. -/
def adaptiveProgram : OracleComp (Oracle Small) Point := do
  let a ← (Oracle Small).query ⟨.forward, (0, 0)⟩
  let _ ← (Oracle Small).query ⟨.inverse, a⟩
  (Oracle Small).query ⟨.forward, (a.1, 1)⟩

theorem adaptive_program_budget : IsTotalQueryBound adaptiveProgram 3 := by
  simp [adaptiveProgram, IsTotalQueryBound]

theorem actual_adaptive_composition :
    Pr{let result ← (simulateQ (impl (noTargets (D := Small))) adaptiveProgram).run State.empty}[
      result.2.bad = true] ≤ epsilon 2 3 0 := by
  exact adaptive_bound noTargets 0 3 (noTargets_bounded 0) adaptiveProgram adaptive_program_budget

def singleTarget : Targets (Fin 32) := fun _ _ ↦ ({0}, ∅)

theorem singleTarget_bounded : TargetBound singleTarget 0 := by
  intro s q
  simp [singleTarget]

/-- The second query depends on the first reply, with a nonempty charged target. -/
def twoAdaptiveQueries : OracleComp (Oracle (Fin 32)) (Fin 32 × Fin 32) := do
  let a ← (Oracle (Fin 32)).query ⟨.forward, (0, 0)⟩
  (Oracle (Fin 32)).query ⟨.forward, (1, a.1)⟩

theorem two_adaptive_queries_budget : IsTotalQueryBound twoAdaptiveQueries 2 := by
  simp [twoAdaptiveQueries, IsTotalQueryBound]

/-- A concrete adaptive composition whose certified upper bound is strictly below one. -/
theorem nonsaturated_adaptive_composition :
    Pr{let result ← (simulateQ (impl singleTarget) twoAdaptiveQueries).run State.empty}[
      result.2.bad = true] ≤ (416 : ENNReal) / 1022 := by
  apply (adaptive_bound singleTarget 0 2 singleTarget_bounded twoAdaptiveQueries
    two_adaptive_queries_budget).trans
  change min 1 ((416 : ENNReal) / 1022) ≤ _
  exact min_le_right _ _

theorem nonsaturated_bound_lt_one : (416 : ENNReal) / 1022 < 1 := by
  apply (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mpr
  norm_num

def selectedTarget (context : Fin 32) : Targets (Fin 32) := fun _ _ ↦ ({context}, ∅)

theorem selectedTarget_bounded (context : Fin 32) : TargetBound (selectedTarget context) 0 := by
  intro s q
  simp [selectedTarget]

/-- Metadata selects the second target from a previous answer, before its next draw. -/
def contextProgram : OracleComp (ContextOracle (Fin 32) (Fin 32)) (Fin 32 × Fin 32) := do
  let a ← (ContextOracle (Fin 32) (Fin 32)).query (0, ⟨.forward, (0, 0)⟩)
  (ContextOracle (Fin 32) (Fin 32)).query (a.1, ⟨.forward, (1, a.2)⟩)

theorem context_program_budget : IsTotalQueryBound contextProgram 2 := by
  simp [contextProgram, IsTotalQueryBound]

theorem actual_adaptive_context_composition :
    Pr{let result ← (simulateQ (contextImpl selectedTarget) contextProgram).run State.empty}[
      result.2.bad = true] ≤ (416 : ENNReal) / 1022 := by
  apply (adaptive_context_bound selectedTarget 0 2 selectedTarget_bounded contextProgram
    context_program_budget).trans
  change min 1 ((416 : ENNReal) / 1022) ≤ _
  exact min_le_right _ _

/-- Two chosen inverse outputs share a rate coordinate with probability one. This event is
about the actual full pairs in the retained permutation, not about the newly uniform inputs. -/
noncomputable def forcedInverseCollision :
    ProbComp (((Fin 4 × Fin 4) × (Fin 4 × Fin 4)) × State (Fin 4 × Fin 4)) := do
  let first ← step noTargets ⟨.inverse, (0, 0)⟩ State.empty
  let second ← step noTargets ⟨.inverse, (0, 1)⟩ first.2
  pure ((first.1, second.1), second.2)

theorem inverse_output_collision_certain :
    Pr{let result ← forcedInverseCollision}[
      (result.2.completion result.1.1).1 = (result.2.completion result.1.2).1] = 1 := by
  apply (OracleComp.prEvent_eq_one_iff _ _).mpr
  intro result member
  simp only [forcedInverseCollision, mem_support_bind_iff, support_pure,
    Set.mem_singleton_iff] at member
  obtain ⟨first, hf, second, hs, rfl⟩ := member
  have one := step_realizes noTargets ⟨.inverse, (0, 0)⟩ State.empty first hf
  have two := step_realizes noTargets ⟨.inverse, (0, 1)⟩ first.2 second hs
  have kept := step_extends noTargets ⟨.inverse, (0, 1)⟩ first.2 second hs first.1 one.1
  rw [kept, one.2, two.2]

/-- The one-coordinate fresh forward bound `4/(16-1)` is false for these inverse-selected
output collisions. Only the inverse sampler's newly generated inputs can be charged. -/
theorem inverse_cannot_use_forward_output_bound :
    ¬ Pr{let result ← forcedInverseCollision}[
      (result.2.completion result.1.1).1 = (result.2.completion result.1.2).1] ≤
        (4 : ENNReal) / 15 := by
  rw [inverse_output_collision_certain]
  apply not_le.mpr
  apply (ENNReal.div_lt_iff (by norm_num) (by norm_num)).mpr
  norm_num

#print axioms fresh_fiber_le
#print axioms draw_pmf
#print axioms fresh_step_law
#print axioms fresh_preserves
#print axioms fresh_used_card
#print axioms step_extends
#print axioms step_realizes
#print axioms potential_step
#print axioms adaptive_bound
#print axioms randomized_adaptive_bound
#print axioms adaptive_context_bound
#print axioms randomized_adaptive_context_bound
#print axioms actual_adaptive_context_composition
#print axioms triangular_cast
#print axioms pinned_octic_adaptive_bound
#print axioms inverse_cannot_use_forward_output_bound

end TestsSecurity.PermutationExposure
