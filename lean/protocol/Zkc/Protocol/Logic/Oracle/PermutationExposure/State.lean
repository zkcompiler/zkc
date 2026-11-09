module

public import Zkc.Protocol.Logic.Oracle.PermutationExposure.Sampling
public import VCVio.OracleComp.SimSemantics.StateT.Basic

@[expose] public section

/-! A shared two-sided lazy permutation sampler.

`State.completion` is an arbitrary bijective filler for the as-yet-unexposed part, not a
uniform random function. Only its restriction to `used` is exposed. A fresh call swaps its
chosen uniform answer into that filler, preserving every previously exposed pair. Both
directions use this one state. The filler starts at identity and is not an eager sampled
permutation. The proved sampling contract is `fresh_step_law`, together with
`fresh_preserves` and the exact cache equations.

The caller supplies target sets *before* a draw. Inverse targets concern the newly sampled
input, never the adversary-selected output. All calls increment `calls`, including cache hits.
-/

set_option autoImplicit false

namespace ZkcSecurity.Probability.PermutationExposure

open OracleComp OracleSpec
open scoped ENNReal

inductive Direction where
  | forward
  | inverse
  deriving DecidableEq, Repr

structure Query (S : Type) where
  direction : Direction
  point : S

/-- A finite partial bijection represented by a bijective completion and exposed domain.
The internal completion is not returned by primitive queries. -/
structure State (S : Type) [DecidableEq S] where
  completion : Equiv.Perm S
  used : Finset S
  calls : ℕ
  used_le_calls : used.card ≤ calls
  bad : Bool

variable {S D : Type} [DecidableEq S] [DecidableEq D] [Fintype D]

def State.empty : State S := ⟨Equiv.refl S, ∅, 0, by simp, false⟩

def State.cached (s : State S) (q : Query S) : Prop :=
  match q.direction with
  | .forward => q.point ∈ s.used
  | .inverse => s.completion.symm q.point ∈ s.used

instance (s : State S) (q : Query S) : Decidable (s.cached q) := by
  unfold State.cached
  split <;> infer_instance

def State.answer (s : State S) (q : Query S) : S :=
  match q.direction with
  | .forward => s.completion q.point
  | .inverse => s.completion.symm q.point

/-- Outputs already used for forward queries; inputs already used for inverse queries. -/
def State.excluded (s : State S) (direction : Direction) : Finset S :=
  match direction with
  | .forward => s.used.image s.completion
  | .inverse => s.used

def State.available [Fintype S] (s : State S) (direction : Direction) : Finset S :=
  Finset.univ \ s.excluded direction

@[simp] theorem excluded_card (s : State S) (direction : Direction) :
    (s.excluded direction).card = s.used.card := by
  cases direction <;> simp [State.excluded, Finset.card_image_of_injective, s.completion.injective]

@[simp] theorem available_card [Fintype S] (s : State S) (direction : Direction) :
    (s.available direction).card = Fintype.card S - s.used.card := by
  simp [State.available, Finset.card_sdiff_of_subset (Finset.subset_univ _)]

theorem available_nonempty [Fintype S] (s : State S) (q : Query S) (fresh : ¬ s.cached q) :
    (s.available q.direction).Nonempty := by
  cases q with
  | mk direction point =>
    cases direction with
    | forward =>
      refine ⟨s.completion point, ?_⟩
      simpa [State.available, State.excluded, State.cached, s.completion.injective.eq_iff]
        using fresh
    | inverse =>
      refine ⟨s.completion.symm point, ?_⟩
      simpa [State.available, State.excluded, State.cached] using fresh

/-- A cache hit still consumes one total call. -/
def State.tick (s : State S) : State S :=
  { s with calls := s.calls + 1, used_le_calls := s.used_le_calls.trans (Nat.le_succ _) }

/-- Insert a fresh oriented pair; the fresh-answer membership is proved at the sampling seam.
This total function also has a value on answers outside the sampler's support. -/
def State.insert (s : State S) (q : Query S) (a : S) (hit : Bool) : State S :=
  match q.direction with
  | .forward =>
    { completion := s.completion.trans (Equiv.swap (s.completion q.point) a)
      used := Insert.insert q.point s.used
      calls := s.calls + 1
      used_le_calls := (Finset.card_insert_le _ _).trans (Nat.add_le_add_right s.used_le_calls 1)
      bad := s.bad || hit }
  | .inverse =>
    { completion := (Equiv.swap (s.completion.symm q.point) a).trans s.completion
      used := Insert.insert a s.used
      calls := s.calls + 1
      used_le_calls := (Finset.card_insert_le _ _).trans (Nat.add_le_add_right s.used_le_calls 1)
      bad := s.bad || hit }

@[simp] theorem insert_calls (s : State S) (q : Query S) (a : S) (hit : Bool) :
    (s.insert q a hit).calls = s.calls + 1 := by
  cases h : q.direction <;> simp [State.insert, h]

@[simp] theorem insert_bad (s : State S) (q : Query S) (a : S) (hit : Bool) :
    (s.insert q a hit).bad = (s.bad || hit) := by
  cases h : q.direction <;> simp [State.insert, h]

/-- The sampled pair really is in the resulting shared bijection. -/
theorem insert_forward (s : State S) (x y : S) (hit : Bool) :
    (s.insert ⟨.forward, x⟩ y hit).completion x = y := by
  simp [State.insert]

theorem insert_inverse (s : State S) (x y : S) (hit : Bool) :
    (s.insert ⟨.inverse, y⟩ x hit).completion x = y := by
  simp [State.insert]

/-- A fresh call preserves every pair previously exposed in either direction. -/
theorem fresh_preserves [Fintype S] (s : State S) (q : Query S) (fresh : ¬ s.cached q)
    (a : S) (available : a ∈ s.available q.direction) (hit : Bool) (z : S)
    (known : z ∈ s.used) :
    (s.insert q a hit).completion z = s.completion z := by
  cases q with
  | mk direction point =>
    cases direction with
    | forward =>
      have different : z ≠ point := by intro h; exact fresh (h ▸ known)
      have unused : s.completion z ≠ a := by
        intro h
        exact (Finset.mem_sdiff.mp available).2
          (Finset.mem_image.mpr ⟨z, known, h⟩)
      exact Equiv.swap_apply_of_ne_of_ne (s.completion.injective.ne different) unused
    | inverse =>
      have different : z ≠ s.completion.symm point := by
        intro h
        apply fresh
        change s.completion.symm point ∈ s.used
        exact h ▸ known
      have unused : z ≠ a := by
        intro h
        exact (Finset.mem_sdiff.mp available).2 (h ▸ known)
      change s.completion (Equiv.swap _ _ z) = s.completion z
      rw [Equiv.swap_apply_of_ne_of_ne different unused]

/-- Each fresh call consumes exactly one pair, also when it is inverse. -/
theorem fresh_used_card [Fintype S] (s : State S) (q : Query S) (fresh : ¬ s.cached q)
    (a : S) (available : a ∈ s.available q.direction) (hit : Bool) :
    (s.insert q a hit).used.card = s.used.card + 1 := by
  cases h : q.direction with
  | forward =>
    simpa [State.insert, h] using Finset.card_insert_of_notMem
      (show q.point ∉ s.used by simpa [State.cached, h] using fresh)
  | inverse =>
    simpa [State.insert, h] using Finset.card_insert_of_notMem
      (show a ∉ s.used by simpa [State.available, State.excluded, h] using
        (Finset.mem_sdiff.mp available).2)

/-- A target policy is evaluated on the pre-draw state and selected query. -/
abbrev Targets (D : Type) [DecidableEq D] :=
  State (D × D) → Query (D × D) → Finset D × Finset D

/-- The only probabilistic primitive: cached calls are deterministic, and fresh calls draw
uniformly from the opposite side of the same partial bijection. -/
noncomputable def step (targets : Targets D) (q : Query (D × D))
    (s : State (D × D)) : ProbComp ((D × D) × State (D × D)) := by
  classical
  exact if cached : s.cached q then pure (s.answer q, s.tick)
    else (fun a ↦ (a, s.insert q a (decide (FiberHit (targets s q).1 (targets s q).2 a)))) <$>
      draw (s.available q.direction) (available_nonempty s q cached)

abbrev Oracle (D : Type) := Query (D × D) →ₒ (D × D)

noncomputable def impl (targets : Targets D) :
    QueryImpl (Oracle D) (StateT (State (D × D)) ProbComp) :=
  fun q ↦ StateT.mk (step targets q)

theorem step_cached (targets : Targets D) (q : Query (D × D)) (s : State (D × D))
    (cached : s.cached q) : step targets q s = pure (s.answer q, s.tick) := by
  classical
  simp [step, cached]

theorem step_fresh (targets : Targets D) (q : Query (D × D)) (s : State (D × D))
    (fresh : ¬ s.cached q) :
    step targets q s =
      (fun a ↦ (a, s.insert q a (decide (FiberHit (targets s q).1 (targets s q).2 a)))) <$>
        draw (s.available q.direction) (available_nonempty s q fresh) := by
  classical
  simp [step, fresh]

/-- The exact fresh conditional law at an arbitrary fixed pre-draw state and query.
The event concerns the returned answer, hence input fibers for inverse calls. -/
theorem fresh_step_law (targets : Targets D) (q : Query (D × D)) (s : State (D × D))
    (fresh : ¬ s.cached q) (event : D × D → Prop) [DecidablePred event] :
    Pr{let result ← step targets q s}[event result.1] =
      ((s.available q.direction).filter event).card /
        (((Fintype.card D) ^ 2 - s.used.card : ℕ) : ENNReal) := by
  rw [step_fresh targets q s fresh, prEvent_map, draw_event, available_card]
  simp [Fintype.card_prod, pow_two]

theorem step_calls (targets : Targets D) (q : Query (D × D)) (s : State (D × D)) :
    ∀ result ∈ support (step targets q s), result.2.calls = s.calls + 1 := by
  classical
  intro result member
  by_cases cached : s.cached q
  · rw [step_cached targets q s cached, support_pure, Set.mem_singleton_iff] at member
    subst result
    rfl
  · rw [step_fresh targets q s cached, support_map] at member
    obtain ⟨a, -, rfl⟩ := member
    exact insert_calls s q a _

/-- The operational sampler extends its exposed partial bijection on every reachable answer. -/
theorem step_extends (targets : Targets D) (q : Query (D × D)) (s : State (D × D))
    (result : (D × D) × State (D × D)) (member : result ∈ support (step targets q s))
    (z : D × D) (known : z ∈ s.used) : result.2.completion z = s.completion z := by
  classical
  by_cases cached : s.cached q
  · rw [step_cached targets q s cached, support_pure, Set.mem_singleton_iff] at member
    subst result
    rfl
  · rw [step_fresh targets q s cached, support_map] at member
    obtain ⟨a, ha, rfl⟩ := member
    exact fresh_preserves s q cached a (draw_mem _ _ a ha) _ z known

/-- The returned answer is a pair of the resulting shared permutation, and its input is
marked exposed. Inverse queries expose `(answer, selectedOutput)`. -/
theorem step_realizes (targets : Targets D) (q : Query (D × D)) (s : State (D × D))
    (result : (D × D) × State (D × D)) (member : result ∈ support (step targets q s)) :
    match q.direction with
    | .forward => q.point ∈ result.2.used ∧ result.2.completion q.point = result.1
    | .inverse => result.1 ∈ result.2.used ∧ result.2.completion result.1 = q.point := by
  classical
  by_cases cached : s.cached q
  · rw [step_cached targets q s cached, support_pure, Set.mem_singleton_iff] at member
    subst result
    cases h : q.direction <;> simpa [State.cached, State.tick, State.answer, h] using cached
  · rw [step_fresh targets q s cached, support_map] at member
    obtain ⟨a, -, rfl⟩ := member
    cases h : q.direction
    · constructor
      · simp [State.insert, h]
      · simp [State.insert, h]
    · constructor
      · simp [State.insert, h]
      · simp [State.insert, h]

/-- Repeated/cached calls have zero fresh bad mass, while `step_calls` still counts them. -/
theorem cached_bad_mass (targets : Targets D) (q : Query (D × D)) (s : State (D × D))
    (cached : s.cached q) (good : s.bad = false) :
    Pr{let result ← step targets q s}[result.2.bad = true] = 0 := by
  rw [step_cached targets q s cached]
  simp [State.tick, good]

end ZkcSecurity.Probability.PermutationExposure
