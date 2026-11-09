module

public import Zkc.Protocol.Logic.Oracle.PermutationExposure.State
public import VCVio.OracleComp.QueryTracking.RandomOracle.FreshAnswer

@[expose] public section

/-! Adaptive composition of the shared-permutation exposure sampler.

The target-cardinality premise is local, on the state and query before drawing. It is not a
premise about the probability of an entire execution. The proof instantiates VCVio's existing
potential-charged first-fire theorem and its existing `simulateQ`; there is no protocol
evaluator here. All calls, in either direction and including repeats, count towards `Q`.
-/

set_option autoImplicit false

namespace ZkcSecurity.Probability.PermutationExposure

open OracleComp OracleSpec
open scoped ENNReal BigOperators

variable {D : Type} [DecidableEq D] [Fintype D]

/-- The deterministic cumulative numerator before multiplication by the coordinate size. -/
def work (b n : ℕ) : ℕ := ∑ k ∈ Finset.range n, (5 * k + b + 4)

@[simp] theorem work_zero (b : ℕ) : work b 0 = 0 := by simp [work]

theorem work_succ (b n : ℕ) : work b (n + 1) = work b n + (5 * n + b + 4) := by
  exact Finset.sum_range_succ _ _

theorem work_mono (b : ℕ) : Monotone (work b) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [work_succ]
  omega

/-- Exact integer arithmetic: division by two applies to the triangular number. -/
theorem work_closed (b n : ℕ) :
    work b n = 5 * (n * (n - 1) / 2) + (b + 4) * n := by
  unfold work
  simp_rw [show ∀ k : ℕ, 5 * k + b + 4 = 5 * k + (b + 4) from fun k ↦ by omega]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_range_id]
  simp [mul_comm]

/-- Casting the triangular number is exact division in `ENNReal`, not a floor estimate. -/
theorem triangular_cast (n : ℕ) :
    ((n * (n - 1) / 2 : ℕ) : ENNReal) =
      (n : ENNReal) * ((n - 1 : ℕ) : ENNReal) / 2 := by
  apply (ENNReal.eq_div_iff (by norm_num) (by norm_num)).mpr
  have exactSum := Finset.sum_range_id_mul_two n
  rw [Finset.sum_range_id] at exactSum
  have castSum := congrArg (fun x : ℕ ↦ (x : ENNReal)) exactSum
  simp only [Nat.cast_mul, Nat.cast_ofNat] at castSum
  simpa only [mul_comm] using castSum

/-- A fixed-budget charge, infinite only beyond the declared total-call budget. -/
noncomputable def charge (d Q b n : ℕ) : ENNReal :=
  if n ≤ Q then ((d * work b n : ℕ) : ENNReal) / ((d ^ 2 - Q : ℕ) : ENNReal) else ⊤

@[simp] theorem charge_zero (d Q b : ℕ) : charge d Q b 0 = 0 := by simp [charge]

theorem charge_mono (d Q b : ℕ) : Monotone (charge d Q b) := by
  intro n m le
  by_cases hm : m ≤ Q
  · rw [charge, ite_eq_left (le.trans hm), charge, ite_eq_left hm]
    apply ENNReal.div_le_div_right
    exact_mod_cast Nat.mul_le_mul_left d (work_mono b le)
  · simp [charge, hm]

theorem charge_finite (d Q b : ℕ) (room : Q < d ^ 2) : charge d Q b Q ≠ ⊤ := by
  simp only [charge, le_refl, ↓reduceIte]
  exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (by exact_mod_cast Nat.sub_ne_zero_of_lt room)

/-- The local targets needed by the later deterministic bad-event classification. -/
def TargetBound (targets : Targets D) (b : ℕ) : Prop :=
  ∀ s q, (targets s q).1.card + (targets s q).2.card ≤ 5 * s.used.card + b + 4

/-- A fresh draw has the required bound before replacing its own denominator by the budget's. -/
theorem step_bad_le (targets : Targets D) (s : State (D × D)) (q : Query (D × D))
    (good : s.bad = false) (b Q : ℕ) (bounded : TargetBound targets b)
    (room : Q < (Fintype.card D) ^ 2) (before : s.calls < Q) :
    Pr{let result ← step targets q s}[result.2.bad = true] ≤
      ((Fintype.card D * (5 * s.calls + b + 4) : ℕ) : ENNReal) /
        (((Fintype.card D) ^ 2 - Q : ℕ) : ENNReal) := by
  classical
  by_cases cached : s.cached q
  · rw [cached_bad_mass targets q s cached good]
    exact zero_le
  · rw [step_fresh targets q s cached, prEvent_map]
    simp only [insert_bad, good, Bool.false_or, decide_eq_true_eq]
    have freshBound := fresh_fiber_le (s.excluded q.direction) (targets s q).1
      (targets s q).2 s.used.card (excluded_card s q.direction)
      (s.used_le_calls.trans_lt (before.trans room)) (available_nonempty s q cached)
    apply (freshBound.trans (min_le_right _ _)).trans
    apply ENNReal.div_le_div
    · have count : (targets s q).1.card + (targets s q).2.card ≤ 5 * s.calls + b + 4 :=
        (bounded s q).trans (by have := s.used_le_calls; omega)
      exact_mod_cast (by simpa only [Nat.mul_comm] using
        Nat.mul_le_mul_right (Fintype.card D) count :
        ((targets s q).1.card + (targets s q).2.card) * Fintype.card D ≤
          Fintype.card D * (5 * s.calls + b + 4))
    · exact_mod_cast Nat.sub_le_sub_left (s.used_le_calls.trans before.le) _

/-- Every actual handler step realizes a locally charged hazard. The charge beyond `Q` is
infinite so that the upstream theorem applies to every state, including unreachable ones. -/
theorem potential_step (targets : Targets D) (b Q : ℕ) (bounded : TargetBound targets b)
    (room : Q < (Fintype.card D) ^ 2) :
    IsPotentialStep (impl targets) (fun s ↦ s.bad = true)
      (fun s ↦ charge (Fintype.card D) Q b s.calls) := by
  classical
  constructor
  · intro q s result member
    apply charge_mono
    rw [step_calls targets q s result member]
    omega
  · intro q s quiet
    have good : s.bad = false := by simpa using quiet
    by_cases cached : s.cached q
    · exact Or.inl ⟨s.answer q, s.tick, step_cached targets q s cached, by
        simp [State.tick, good]⟩
    · apply Or.inr
      let update := fun a ↦ s.insert q a (decide (FiberHit (targets s q).1 (targets s q).2 a))
      refine ⟨draw (s.available q.direction) (available_nonempty s q cached), update,
        if s.calls < Q then
          ((Fintype.card D * (5 * s.calls + b + 4) : ℕ) : ENNReal) /
            (((Fintype.card D) ^ 2 - Q : ℕ) : ENNReal) else 1,
        step_fresh targets q s cached, ?_, ?_⟩
      · split_ifs with before
        · have bound := step_bad_le targets s q good b Q bounded room before
          rwa [step_fresh targets q s cached, prEvent_map] at bound
        · exact prEvent_le_one _
      · intro a
        dsimp only [update]
        rw [insert_calls]
        by_cases before : s.calls < Q
        · rw [ite_eq_left before, charge, ite_eq_left before.le, charge,
            ite_eq_left (by omega)]
          rw [ENNReal.div_add_div_same, ← Nat.cast_add]
          apply le_of_eq
          congr 1
          rw [work_succ]
          push_cast
          ring
        · simp only [ite_eq_right before, charge, show ¬s.calls + 1 ≤ Q by omega, ↓reduceIte]
          exact le_top

/-- Structural total-call bounds imply the corresponding final counter bound. -/
theorem run_calls_le {α : Type} (targets : Targets D) (program : OracleComp (Oracle D) α) :
    ∀ (remaining : ℕ) (s : State (D × D)), IsTotalQueryBound program remaining →
      ∀ result ∈ support ((simulateQ (impl targets) program).run s),
        result.2.calls ≤ s.calls + remaining := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    intro remaining s _ result member
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact Nat.le_add_right _ _
  | query_bind q next ih =>
    intro remaining s bound result member
    obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bound
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      at member
    obtain ⟨middle, hm, hr⟩ := member
    have tail := ih middle.1 (remaining - 1) middle.2 (rest middle.1) result hr
    have inc := step_calls targets q s middle hm
    omega

/-- The specified conservative bound, with no real-valued rounding or asymptotic arithmetic. -/
noncomputable def epsilon (d Q b : ℕ) : ENNReal :=
  if Q < d ^ 2 then
    min 1 (((d * (5 * (Q * (Q - 1) / 2) + (b + 4) * Q) : ℕ) : ENNReal) /
      ((d ^ 2 - Q : ℕ) : ENNReal))
  else 1

/-- Actual adaptive composition for the chosen shared two-sided lazy sampler. All theorem
inputs are deterministic cardinality/budget conditions, not a final-probability hypothesis. -/
theorem adaptive_bound {α : Type} (targets : Targets D) (b Q : ℕ)
    (bounded : TargetBound targets b) (program : OracleComp (Oracle D) α)
    (budget : IsTotalQueryBound program Q) :
    Pr{let result ← (simulateQ (impl targets) program).run State.empty}[result.2.bad = true] ≤
      epsilon (Fintype.card D) Q b := by
  classical
  by_cases room : Q < (Fintype.card D) ^ 2
  · rw [epsilon, ite_eq_left room]
    apply le_min (prEvent_le_one _)
    have localLaw := potential_step targets b Q bounded room
    have bound := prEvent_and_le_of_potential (impl targets) (fun s ↦ s.bad = true)
      (fun s ↦ charge (Fintype.card D) Q b s.calls) localLaw.mono localLaw.step program
      (charge (Fintype.card D) Q b Q) (charge_finite _ Q b room) State.empty (by simp [State.empty])
    have same := prEvent_congr_of_support ((simulateQ (impl targets) program).run State.empty)
      (fun result ↦ result.2.bad = true)
      (fun result ↦ result.2.bad = true ∧
        charge (Fintype.card D) Q b result.2.calls ≤ charge (Fintype.card D) Q b Q)
      (fun result member ↦ ⟨fun h ↦ ⟨h, charge_mono _ Q b (by
        simpa [State.empty] using run_calls_le targets program Q State.empty budget result member)⟩,
        And.left⟩)
    rw [same]
    simpa [State.empty, charge, work_closed] using bound
  · rw [epsilon, ite_eq_right room]
    exact prEvent_le_one _

/-- Arbitrary private randomization as a distribution over reply-adaptive programs.
Only programs in the operational support need satisfy the total-call bound. -/
theorem randomized_adaptive_bound {α : Type} (targets : Targets D) (b Q : ℕ)
    (bounded : TargetBound targets b) (programs : ProbComp (OracleComp (Oracle D) α))
    (budget : ∀ program ∈ support programs, IsTotalQueryBound program Q) :
    Pr{let result ← programs >>= fun program ↦
      (simulateQ (impl targets) program).run State.empty}[result.2.bad = true] ≤
      epsilon (Fintype.card D) Q b := by
  exact prEvent_bind_le_of_forall_le_of_support programs _ _ fun program member ↦
    adaptive_bound targets b Q bounded program (budget program member)

/-- Caller metadata can carry an ordered trace, registered roots, private state, or targets.
It is chosen before the reply. It does not create an extra primitive call. -/
abbrev ContextOracle (D Context : Type) := (Context × Query (D × D)) →ₒ (D × D)

noncomputable def contextImpl {Context : Type} (targets : Context → Targets D) :
    QueryImpl (ContextOracle D Context) (StateT (State (D × D)) ProbComp) :=
  fun request ↦ impl (targets request.1) request.2

/-- The same local law works when the caller adaptively chooses metadata at each call. -/
theorem context_potential_step {Context : Type} (targets : Context → Targets D)
    (b Q : ℕ) (bounded : ∀ context, TargetBound (targets context) b)
    (room : Q < (Fintype.card D) ^ 2) :
    IsPotentialStep (contextImpl targets) (fun s ↦ s.bad = true)
      (fun s ↦ charge (Fintype.card D) Q b s.calls) := by
  constructor
  · intro request s result member
    exact (potential_step (targets request.1) b Q (bounded request.1) room).mono
      request.2 s result member
  · intro request s quiet
    exact (potential_step (targets request.1) b Q (bounded request.1) room).step
      request.2 s quiet

theorem context_run_calls_le {Context α : Type} (targets : Context → Targets D)
    (program : OracleComp (ContextOracle D Context) α) :
    ∀ (remaining : ℕ) (s : State (D × D)), IsTotalQueryBound program remaining →
      ∀ result ∈ support ((simulateQ (contextImpl targets) program).run s),
        result.2.calls ≤ s.calls + remaining := by
  induction program using OracleComp.inductionOn with
  | pure value =>
    intro remaining s _ result member
    simp only [simulateQ_pure, StateT.run_pure, support_pure, Set.mem_singleton_iff] at member
    subst result
    exact Nat.le_add_right _ _
  | query_bind request next ih =>
    intro remaining s bound result member
    obtain ⟨positive, rest⟩ := isTotalQueryBound_query_bind_iff.mp bound
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, mem_support_bind_iff]
      at member
    obtain ⟨middle, hm, hr⟩ := member
    have tail := ih middle.1 (remaining - 1) middle.2 (rest middle.1) result hr
    have inc := step_calls (targets request.1) request.2 s middle hm
    omega

/-- Adaptive composition with arbitrary caller-selected pre-draw context. No normalization
or extractor is evaluated here; the parent proves the context's deterministic interpretation
and the target-cardinality premise at its own integration boundary. -/
theorem adaptive_context_bound {Context α : Type} (targets : Context → Targets D)
    (b Q : ℕ) (bounded : ∀ context, TargetBound (targets context) b)
    (program : OracleComp (ContextOracle D Context) α)
    (budget : IsTotalQueryBound program Q) :
    Pr{let result ← (simulateQ (contextImpl targets) program).run State.empty}[
      result.2.bad = true] ≤ epsilon (Fintype.card D) Q b := by
  classical
  by_cases room : Q < (Fintype.card D) ^ 2
  · rw [epsilon, ite_eq_left room]
    apply le_min (prEvent_le_one _)
    have localLaw := context_potential_step targets b Q bounded room
    have bound := prEvent_and_le_of_potential (contextImpl targets) (fun s ↦ s.bad = true)
      (fun s ↦ charge (Fintype.card D) Q b s.calls) localLaw.mono localLaw.step program
      (charge (Fintype.card D) Q b Q) (charge_finite _ Q b room) State.empty
      (by simp [State.empty])
    have same := prEvent_congr_of_support
      ((simulateQ (contextImpl targets) program).run State.empty)
      (fun result ↦ result.2.bad = true)
      (fun result ↦ result.2.bad = true ∧
        charge (Fintype.card D) Q b result.2.calls ≤ charge (Fintype.card D) Q b Q)
      (fun result member ↦ ⟨fun h ↦ ⟨h, charge_mono _ Q b (by
        simpa [State.empty] using context_run_calls_le targets program Q State.empty
          budget result member)⟩, And.left⟩)
    rw [same]
    simpa [State.empty, charge, work_closed] using bound
  · rw [epsilon, ite_eq_right room]
    exact prEvent_le_one _

theorem randomized_adaptive_context_bound {Context α : Type}
    (targets : Context → Targets D) (b Q : ℕ)
    (bounded : ∀ context, TargetBound (targets context) b)
    (programs : ProbComp (OracleComp (ContextOracle D Context) α))
    (budget : ∀ program ∈ support programs, IsTotalQueryBound program Q) :
    Pr{let result ← programs >>= fun program ↦
      (simulateQ (contextImpl targets) program).run State.empty}[result.2.bad = true] ≤
      epsilon (Fintype.card D) Q b := by
  exact prEvent_bind_le_of_forall_le_of_support programs _ _ fun program member ↦
    adaptive_context_bound targets b Q bounded program (budget program member)

/-- The concrete octic cardinality substitution is solely a corollary of the generic result.
This type is an eight-coordinate finite carrier, with no computational permutation assertion. -/
theorem octic_adaptive_bound {α : Type} (q b Q : ℕ)
    (targets : Targets (Fin 8 → Fin q)) (bounded : TargetBound targets b)
    (program : OracleComp (Oracle (Fin 8 → Fin q)) α)
    (budget : IsTotalQueryBound program Q) :
    Pr{let result ← (simulateQ (impl targets) program).run State.empty}[result.2.bad = true] ≤
      epsilon (q ^ 8) Q b := by
  simpa using adaptive_bound targets b Q bounded program budget

/-- The pinned coordinate modulus appears only by specializing the generic cardinality. -/
theorem pinned_octic_adaptive_bound {α : Type} (b Q : ℕ)
    (targets : Targets (Fin 8 → Fin 2130706433)) (bounded : TargetBound targets b)
    (program : OracleComp (Oracle (Fin 8 → Fin 2130706433)) α)
    (budget : IsTotalQueryBound program Q) :
    Pr{let result ← (simulateQ (impl targets) program).run State.empty}[result.2.bad = true] ≤
      epsilon (2130706433 ^ 8) Q b :=
  octic_adaptive_bound 2130706433 b Q targets bounded program budget

end ZkcSecurity.Probability.PermutationExposure
