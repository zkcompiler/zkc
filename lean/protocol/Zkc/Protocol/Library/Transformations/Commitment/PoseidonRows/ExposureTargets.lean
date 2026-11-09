module

public import Zkc.Protocol.Logic.Oracle.PermutationExposure.Adaptive
public import Zkc.Protocol.Library.Transformations.Commitment.PoseidonRows.BatchAdapter

@[expose] public section

/-! Targets computed from the actual exposed partial bijection. Root registrations count
occurrences, including duplicates. No caller-supplied transcript is used for cardinality. -/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

namespace Monitored

open OracleComp OracleSpec
open ZkcSecurity.Probability

abbrev PermState (D : Type) [DecidableEq D] := PermutationExposure.State (D × D)
abbrev PermQuery (D : Type) := PermutationExposure.Query (D × D)

/-- All retained roots, with an aggregate occurrence budget. -/
structure Roots (D : Type) (b : ℕ) where
  entries : List D
  bounded : entries.length ≤ b

variable {F : Type} {rate b : ℕ} [Zero F] [DecidableEq F]

local notation "D" => Digest F rate

def outputRates (s : PermState D) : Finset D := s.used.image (fun x ↦ (s.completion x).1)
def outputCapacities (s : PermState D) : Finset D := s.used.image (fun x ↦ (s.completion x).2)
def inputRates (s : PermState D) : Finset D := s.used.image Prod.fst
def inputCapacities (s : PermState D) : Finset D := s.used.image Prod.snd

/-- Selected before the fresh answer. Inverse targets concern its random input. -/
def targets (roots : Roots D b) : PermutationExposure.Targets D := fun s q ↦
  match q.direction with
  | .forward =>
    (outputRates s ∪ inputRates s ∪ inputCapacities s ∪ roots.entries.toFinset ∪
      {q.point.1, q.point.2},
     outputCapacities s ∪ inputCapacities s ∪ {0, q.point.2})
  | .inverse => (outputRates s, outputRates s ∪ outputCapacities s ∪ {0})

/-- Universal on sampler states, including unreachable states; exactly the required count. -/
theorem targets_bound [Fintype F] (roots : Roots D b) :
    PermutationExposure.TargetBound (targets roots) b := by
  intro s q
  have a := Finset.card_image_le (s := s.used) (f := fun x ↦ (s.completion x).1)
  have c := Finset.card_image_le (s := s.used) (f := fun x ↦ (s.completion x).2)
  have u := Finset.card_image_le (s := s.used) (f := Prod.fst)
  have v := Finset.card_image_le (s := s.used) (f := Prod.snd)
  have k := (List.toFinset_card_le roots.entries).trans roots.bounded
  change (outputRates s).card ≤ s.used.card at a
  change (outputCapacities s).card ≤ s.used.card at c
  change (inputRates s).card ≤ s.used.card at u
  change (inputCapacities s).card ≤ s.used.card at v
  cases direction : q.direction <;> simp only [targets, direction]
  · have r1 := Finset.card_union_le (outputRates s) (inputRates s)
    have r2 := Finset.card_union_le (outputRates s ∪ inputRates s) (inputCapacities s)
    have r3 := Finset.card_union_le
      (outputRates s ∪ inputRates s ∪ inputCapacities s) roots.entries.toFinset
    have r4 := Finset.card_union_le
      (outputRates s ∪ inputRates s ∪ inputCapacities s ∪ roots.entries.toFinset)
      {q.point.1, q.point.2}
    have r5 := Finset.card_le_two (a := q.point.1) (b := q.point.2)
    have c1 := Finset.card_union_le (outputCapacities s) (inputCapacities s)
    have c2 := Finset.card_union_le (outputCapacities s ∪ inputCapacities s) {0, q.point.2}
    have c3 := Finset.card_le_two (a := (0 : D)) (b := q.point.2)
    omega
  · have c1 := Finset.card_union_le (outputRates s) (outputCapacities s)
    have c2 := Finset.card_union_le (outputRates s ∪ outputCapacities s) {0}
    simp only [Finset.card_singleton] at c2
    omega

/-- The oriented full pair of one actual call; birth is decided by normalization. -/
def exposure (q : PermQuery D) (answer : D × D) : Exposure F rate :=
  match q.direction with
  | .forward => ⟨true, q.point, answer⟩
  | .inverse => ⟨false, answer, q.point⟩

/-- Exact coordinate association, with no decoding or extraction premise. -/
def Associated (s : PermState D) (log : List (Exposure F rate)) : Prop :=
  (∀ e ∈ log, e.input ∈ s.used ∧ s.completion e.input = e.output) ∧
    ∀ x ∈ s.used, ∃ e ∈ log, e.input = x

/-- A missed charged fiber supplies both local flags and every chronological flag. -/
theorem miss_good (roots : Roots D b) (s : PermState D) (q : PermQuery D)
    (answer : D × D) (log : List (Exposure F rate)) (assoc : Associated s log)
    (miss : ¬ PermutationExposure.FiberHit (targets roots s q).1
      (targets roots s q).2 answer) :
    LocalGood (exposure q answer) ∧
      (∀ old ∈ log, OrderedGood old (exposure q answer)) ∧
      (∀ root ∈ roots.entries, (exposure q answer).forward = true →
        (exposure q answer).output.1 ≠ root) := by
  have misses := not_or.mp miss
  cases direction : q.direction with
  | forward =>
    simp only [targets, direction, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, List.mem_toFinset] at misses
    rcases misses with ⟨mr, mc⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [exposure, direction, LocalGood, ↓reduceIte]
      exact ⟨fun h ↦ mr (Or.inr (Or.inl h)),
        fun h ↦ mr (Or.inr (Or.inr h)),
        fun h ↦ mc (Or.inr (Or.inl h)), fun h ↦ mc (Or.inr (Or.inr h))⟩
    · intro old member
      obtain ⟨known, image⟩ := assoc.1 old member
      have yr : old.output.1 ∈ outputRates s :=
        Finset.mem_image.mpr ⟨old.input, known, congrArg Prod.fst image⟩
      have yc : old.output.2 ∈ outputCapacities s :=
        Finset.mem_image.mpr ⟨old.input, known, congrArg Prod.snd image⟩
      have xr : old.input.1 ∈ inputRates s := Finset.mem_image.mpr ⟨_, known, rfl⟩
      have xc : old.input.2 ∈ inputCapacities s := Finset.mem_image.mpr ⟨_, known, rfl⟩
      simp only [OrderedGood, exposure, direction, ↓reduceIte]
      exact ⟨fun h ↦ mr (Or.inl (Or.inl (Or.inl (Or.inl (h ▸ yr))))),
        fun h ↦ mr (Or.inl (Or.inl (Or.inl (Or.inr (h ▸ xr))))),
        fun h ↦ mr (Or.inl (Or.inl (Or.inr (h ▸ xc)))),
        fun h ↦ mc (Or.inl (Or.inl (h ▸ yc))),
        fun h ↦ mc (Or.inl (Or.inr (h ▸ xc)))⟩
    · intro root member _ same
      have equal : answer.1 = root := by simpa [exposure, direction] using same
      exact mr (Or.inl (Or.inr (equal ▸ member)))
  | inverse =>
    simp only [targets, direction, Finset.mem_union, Finset.mem_singleton] at misses
    rcases misses with ⟨mr, mc⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa [LocalGood, exposure, direction] using
        (show answer.2 ≠ 0 from fun h ↦ mc (Or.inr h))
    · intro old member
      obtain ⟨known, image⟩ := assoc.1 old member
      have yr : old.output.1 ∈ outputRates s :=
        Finset.mem_image.mpr ⟨old.input, known, congrArg Prod.fst image⟩
      have yc : old.output.2 ∈ outputCapacities s :=
        Finset.mem_image.mpr ⟨old.input, known, congrArg Prod.snd image⟩
      simp only [OrderedGood, exposure, direction, Bool.false_eq_true, ↓reduceIte]
      exact ⟨fun h ↦ mr (h ▸ yr), fun h ↦ mc (Or.inl (Or.inl (h ▸ yr))),
        fun h ↦ mc (Or.inl (Or.inr (h ▸ yc)))⟩
    · simp [exposure, direction]

end Monitored
end ZkcSecurity.Commitment.PoseidonRows
