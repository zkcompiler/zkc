module

public import Zkc.Protocol.Library.Transformations.Commitment.BatchOpening

@[expose] public section

/-! # Chronological two-sided permutation records

Pairs are oriented input/output even for inverse calls. Normalization remembers the direction
of the first exposure of the *full pair*. Repeated forward calls cannot relabel inverse births.
`Good` is a condition on chronological primitive coordinates, not on extraction results.
No distribution, permutation hardness, or native implementation refinement is assumed here.
-/

set_option autoImplicit false

namespace ZkcSecurity.Commitment.PoseidonRows

abbrev Digest (F : Type) (rate : ℕ) := Fin rate → F
abbrev State (F : Type) (rate : ℕ) := Digest F rate × Digest F rate

/-- Full oriented primitive data; `forward = false` means the output was queried. -/
structure Exposure (F : Type) (rate : ℕ) where
  forward : Bool
  input : State F rate
  output : State F rate
  deriving DecidableEq

variable {F : Type} {rate : ℕ}

def SamePair (a b : Exposure F rate) : Prop := a.input = b.input ∧ a.output = b.output

instance [DecidableEq F] (a b : Exposure F rate) : Decidable (SamePair a b) :=
  inferInstanceAs (Decidable (a.input = b.input ∧ a.output = b.output))

/-- Append only a first exposure; a cache hit preserves the earlier direction. -/
def insert [DecidableEq F] (log : List (Exposure F rate)) (e : Exposure F rate) :=
  if log.any (fun old ↦ decide (SamePair old e)) then log else log ++ [e]

def normalize [DecidableEq F] (raw : List (Exposure F rate)) : List (Exposure F rate) :=
  raw.foldl insert []

theorem normalize_snoc [DecidableEq F] (raw : List (Exposure F rate)) (e : Exposure F rate) :
    normalize (raw ++ [e]) = insert (normalize raw) e := by
  simp [normalize, List.foldl_append]

theorem insert_repeat [DecidableEq F] {log : List (Exposure F rate)}
    {old e : Exposure F rate} (member : old ∈ log) (same : SamePair old e) :
    insert log e = log := by
  simp only [insert]
  have : (log.any (fun old ↦ decide (SamePair old e))) = true :=
    List.any_eq_true.mpr ⟨old, member, by simpa using same⟩
  simp [this]

theorem normalize_repeat [DecidableEq F] {raw : List (Exposure F rate)}
    {old e : Exposure F rate} (member : old ∈ normalize raw) (same : SamePair old e) :
    normalize (raw ++ [e]) = normalize raw := by
  rw [normalize_snoc, insert_repeat member same]

theorem mem_insert [DecidableEq F] {log : List (Exposure F rate)} {old : Exposure F rate}
    (member : old ∈ log) (e : Exposure F rate) : old ∈ insert log e := by
  unfold insert
  split <;> simp_all

/-- Every raw call has its oriented pair represented, with the original birth direction. -/
theorem pair_covered [DecidableEq F] {raw : List (Exposure F rate)} {call : Exposure F rate}
    (member : call ∈ raw) : ∃ born ∈ normalize raw, SamePair born call := by
  induction raw using List.reverseRecOn with
  | nil => simp at member
  | append_singleton raw e ih =>
      rw [normalize_snoc]
      rcases List.mem_append.mp member with earlier | last
      · obtain ⟨born, inLog, same⟩ := ih earlier
        exact ⟨born, mem_insert inLog e, same⟩
      · have equal : call = e := by simpa using last
        subst call
        unfold insert
        split
        · rename_i hit
          obtain ⟨born, inLog, same⟩ := List.any_eq_true.mp hit
          exact ⟨born, inLog, by simpa using same⟩
        · exact ⟨e, by simp, ⟨rfl, rfl⟩⟩

/-- Normalization preserves the exposure order at every physical prefix boundary. -/
theorem normalize_prefix [DecidableEq F] (raw later : List (Exposure F rate)) :
    normalize raw <+: normalize (raw ++ later) := by
  induction later using List.reverseRecOn with
  | nil => simp
  | append_singleton earlier fresh ih =>
      rw [← List.append_assoc, normalize_snoc]
      apply ih.trans
      unfold insert
      split
      · exact List.prefix_rfl
      · exact List.prefix_append _ _

theorem normalize_subset [DecidableEq F] (raw : List (Exposure F rate)) :
    ∀ e ∈ normalize raw, e ∈ raw := by
  induction raw using List.reverseRecOn with
  | nil => simp [normalize]
  | append_singleton raw fresh ih =>
      intro e member
      rw [normalize_snoc] at member
      unfold insert at member
      split at member
      · exact List.mem_append_left _ (ih e member)
      · rcases List.mem_append.mp member with earlier | last
        · exact List.mem_append_left _ (ih e earlier)
        · exact List.mem_append_right _ last

theorem normalize_pairwise [DecidableEq F] (raw : List (Exposure F rate)) :
    (normalize raw).Pairwise (fun a b ↦ ¬ SamePair a b) := by
  induction raw using List.reverseRecOn with
  | nil => simp [normalize]
  | append_singleton raw fresh ih =>
      rw [normalize_snoc]
      unfold insert
      split
      · exact ih
      · rename_i absent
        rw [List.pairwise_append]
        refine ⟨ih, by simp, ?_⟩
        intro a am b bm
        have equal : b = fresh := by simpa using bm
        subst b
        have miss := List.any_eq_false.mp (Bool.eq_false_iff.mpr absent) a am
        simpa using miss

variable [Zero F]

/-- Local parts of the specified fresh-exposure flags. -/
def LocalGood (e : Exposure F rate) : Prop :=
  if e.forward then
    e.output.1 ≠ e.input.1 ∧ e.output.1 ≠ e.input.2 ∧
      e.output.2 ≠ 0 ∧ e.output.2 ≠ e.input.2
  else e.input.2 ≠ 0

/-- Cross-exposure flags. The second argument is born strictly later. Inverse outputs are
adversary selected: their rate/capacity collisions are deliberately unrestricted. -/
def OrderedGood (earlier later : Exposure F rate) : Prop :=
  if later.forward then
    later.output.1 ≠ earlier.output.1 ∧ later.output.1 ≠ earlier.input.1 ∧
      later.output.1 ≠ earlier.input.2 ∧ later.output.2 ≠ earlier.output.2 ∧
      later.output.2 ≠ earlier.input.2
  else
    later.input.1 ≠ earlier.output.1 ∧ later.input.2 ≠ earlier.output.1 ∧
      later.input.2 ≠ earlier.output.2

/-- A finite, chronological, coordinate-only premise, normally applied to `normalize raw`. -/
def Good (log : List (Exposure F rate)) : Prop :=
  log.Pairwise OrderedGood ∧ ∀ e ∈ log, LocalGood e

instance [DecidableEq F] (e : Exposure F rate) : Decidable (LocalGood e) := by
  unfold LocalGood
  infer_instance

instance [DecidableEq F] (earlier later : Exposure F rate) :
    Decidable (OrderedGood earlier later) := by
  unfold OrderedGood
  infer_instance

instance [DecidableEq F] (log : List (Exposure F rate)) : Decidable (Good log) := by
  unfold Good
  infer_instance

theorem Good.prefix {a b : List (Exposure F rate)} (good : Good (a ++ b)) : Good a :=
  ⟨(List.pairwise_append.mp good.1).1, fun e member ↦ good.2 e (List.mem_append_left _ member)⟩

theorem Good.order {log : List (Exposure F rate)} (good : Good log)
    {a b : Exposure F rate} (am : a ∈ log) (bm : b ∈ log) :
    a = b ∨ OrderedGood a b ∨ OrderedGood b a := by
  have general {α : Type} {R : α → α → Prop} {xs : List α} (pw : xs.Pairwise R)
      {x y : α} (xm : x ∈ xs) (ym : y ∈ xs) : x = y ∨ R x y ∨ R y x := by
    induction xs generalizing x y with
    | nil => simp at xm
    | cons head tail ih =>
        rcases List.pairwise_cons.mp pw with ⟨first, rest⟩
        rcases List.mem_cons.mp xm with rfl | xm
        · rcases List.mem_cons.mp ym with rfl | ym
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (first _ ym))
        · rcases List.mem_cons.mp ym with eqHead | ym
          · exact Or.inr (Or.inr (eqHead ▸ first _ xm))
          · exact ih rest xm ym
  exact general good.1 am bm

theorem Good.rate_unique {log : List (Exposure F rate)} (good : Good log)
    {a b : Exposure F rate} (am : a ∈ log) (bm : b ∈ log)
    (af : a.forward = true) (bf : b.forward = true) (same : a.output.1 = b.output.1) :
    a = b := by
  rcases good.order am bm with equal | ab | ba
  · exact equal
  · simp only [OrderedGood, bf, ↓reduceIte] at ab
    exact False.elim (ab.1 same.symm)
  · simp only [OrderedGood, af, ↓reduceIte] at ba
    exact False.elim (ba.1 same)

theorem Good.capacity_unique {log : List (Exposure F rate)} (good : Good log)
    {a b : Exposure F rate} (am : a ∈ log) (bm : b ∈ log)
    (af : a.forward = true) (bf : b.forward = true) (same : a.output.2 = b.output.2) :
    a = b := by
  rcases good.order am bm with equal | ab | ba
  · exact equal
  · have flags := ab
    simp only [OrderedGood, bf, ↓reduceIte] at flags
    exact False.elim (flags.2.2.2.1 same.symm)
  · have flags := ba
    simp only [OrderedGood, af, ↓reduceIte] at flags
    exact False.elim (flags.2.2.2.1 same)

/-- Zero initial capacity rules out inverse birth of the first sponge call. -/
theorem Good.initial_forward {log : List (Exposure F rate)} (good : Good log)
    {e : Exposure F rate} (member : e ∈ log) (zero : e.input.2 = 0) :
    e.forward = true := by
  have own := good.2 e member
  cases direction : e.forward <;> simp_all [LocalGood]

/-- Both exposure orders are covered; a later forward cache hit does not supply this proof. -/
theorem Good.capacity_forward {log : List (Exposure F rate)} (good : Good log)
    {a b : Exposure F rate} (am : a ∈ log) (bm : b ∈ log)
    (af : a.forward = true) (link : b.input.2 = a.output.2) : b.forward = true := by
  cases bf : b.forward with
  | true => rfl
  | false =>
      rcases good.order am bm with equal | ab | ba
      · rw [equal] at af
        simp [bf] at af
      · have flags := ab
        simp only [OrderedGood, bf, Bool.false_eq_true, ↓reduceIte] at flags
        exact False.elim (flags.2.2 link)
      · have flags := ba
        simp only [OrderedGood, af, ↓reduceIte] at flags
        exact False.elim (flags.2.2.2.2 link.symm)

/-- An active child can occur in either half of the parent input. -/
theorem Good.parent_forward {log : List (Exposure F rate)} (good : Good log)
    {a b : Exposure F rate} (am : a ∈ log) (bm : b ∈ log)
    (af : a.forward = true)
    (link : b.input.1 = a.output.1 ∨ b.input.2 = a.output.1) : b.forward = true := by
  cases bf : b.forward with
  | true => rfl
  | false =>
      rcases good.order am bm with equal | ab | ba
      · rw [equal] at af
        simp [bf] at af
      · have flags := ab
        simp only [OrderedGood, bf, Bool.false_eq_true, ↓reduceIte] at flags
        exact False.elim (link.elim flags.1 flags.2.1)
      · have flags := ba
        simp only [OrderedGood, af, ↓reduceIte] at flags
        exact False.elim (link.elim (fun h ↦ flags.2.1 h.symm)
          (fun h ↦ flags.2.2.1 h.symm))

end ZkcSecurity.Commitment.PoseidonRows
