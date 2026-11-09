module

public import Zkc.Protocol.Library.Mathematics.Probability.FiniteSelection
public import VCVio.OracleComp.Constructions.SampleableType.Measure
public import Mathlib.GroupTheory.Perm.Basic

@[expose] public section

/-! Uniform sampling without replacement and coordinate-fiber bounds.

The random object is a full state in `D × D`, sampled outside a finite used set.
Its coordinates need not remain uniformly distributed after exclusions. The event is
intersection with the union of the two coordinate target fibers. `draw_pmf` relates the
VCVio sampler to a Mathlib PMF independently of any oracle or extractor.
-/

set_option autoImplicit false

namespace ZkcSecurity.Probability.PermutationExposure

open OracleComp
open scoped ENNReal BigOperators

variable {S D : Type} [DecidableEq D] [Fintype D]

/-- The existing finite uniform sampler, retaining its subtype membership certificate. -/
noncomputable def sample (available : Finset S) (nonempty : available.Nonempty) :
    ProbComp available :=
  @uniformSample available (SampleableType.finsetCoe available nonempty)

/-- Forget only the membership certificate, after sampling. -/
noncomputable def draw (available : Finset S) (nonempty : available.Nonempty) : ProbComp S :=
  Subtype.val <$> sample available nonempty

/-- The PMF of the same finite sampler, using the existing Mathlib construction. -/
noncomputable def drawPMF (available : Finset S) (nonempty : available.Nonempty) : PMF S := by
  let : Nonempty available := nonempty.to_subtype
  exact (FiniteSelection.uniformDraw available).map Subtype.val

theorem draw_mem (available : Finset S) (nonempty : available.Nonempty) (x : S)
    (member : x ∈ support (draw available nonempty)) : x ∈ available := by
  rw [draw, support_map] at member
  obtain ⟨a, -, rfl⟩ := member
  exact a.property

theorem subtype_filter_card (available : Finset S) (event : S → Prop) [DecidablePred event] :
    (Finset.univ.filter fun x : available ↦ event x.val).card =
      (available.filter event).card := by
  apply Finset.card_bij (fun x _ ↦ x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (Finset.mem_filter.mp hx).1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩, rfl⟩

theorem sample_event (available : Finset S) (nonempty : available.Nonempty)
    (event : S → Prop) [DecidablePred event] :
    Pr{let x ← sample available nonempty}[event x.val] =
      (available.filter event).card / (available.card : ENNReal) := by
  let : SampleableType available := SampleableType.finsetCoe available nonempty
  rw [show sample available nonempty = uniformSample available from rfl,
    SampleableType.prEvent_uniformSample]
  congr 1
  · exact_mod_cast (subtype_filter_card available event)
  · simp

theorem draw_event (available : Finset S) (nonempty : available.Nonempty)
    (event : S → Prop) [DecidablePred event] :
    Pr{let x ← draw available nonempty}[event x] =
      (available.filter event).card / (available.card : ENNReal) := by
  rw [draw, prEvent_map]
  exact sample_event available nonempty event

/-- Exact PMF realization, with no assumption about a surrounding protocol. -/
theorem draw_pmf (available : Finset S) (nonempty : available.Nonempty)
    (event : S → Prop) [DecidablePred event] :
    Pr{let x ← draw available nonempty}[event x] =
      (drawPMF available nonempty).toOuterMeasure {x | event x} := by
  let : Nonempty available := nonempty.to_subtype
  rw [draw_event, drawPMF, PMF.toOuterMeasure_map_apply,
    show Subtype.val ⁻¹' {x | event x} = {x : available | event x.val} from rfl,
    FiniteSelection.uniformDraw_event]
  congr 1
  · exact_mod_cast (subtype_filter_card available event).symm
  · simp

/-- A rate hit or a capacity hit of the freshly sampled full state. -/
def FiberHit (rate capacity : Finset D) (state : D × D) : Prop :=
  state.1 ∈ rate ∨ state.2 ∈ capacity

instance (rate capacity : Finset D) : DecidablePred (FiberHit rate capacity) :=
  fun _ ↦ inferInstanceAs (Decidable (_ ∨ _))

/-- Each coordinate fiber has `|D|` full states; overlap is harmless. -/
theorem fiber_card_le (available : Finset (D × D)) (rate capacity : Finset D) :
    (available.filter (FiberHit rate capacity)).card ≤
      (rate.card + capacity.card) * Fintype.card D := by
  have subset : available.filter (FiberHit rate capacity) ⊆
      rate ×ˢ Finset.univ ∪ Finset.univ ×ˢ capacity := by
    intro x hx
    rcases (Finset.mem_filter.mp hx).2 with h | h
    · exact Finset.mem_union_left _ (Finset.mem_product.mpr ⟨h, Finset.mem_univ _⟩)
    · exact Finset.mem_union_right _ (Finset.mem_product.mpr ⟨Finset.mem_univ _, h⟩)
  calc _ ≤ (rate ×ˢ Finset.univ ∪ Finset.univ ×ˢ capacity).card := Finset.card_le_card subset
    _ ≤ (rate ×ˢ Finset.univ).card + (Finset.univ ×ˢ capacity).card :=
      Finset.card_union_le _ _
    _ = _ := by simp [Finset.card_product]; ring

/-- The exact without-replacement fresh-step estimate, including saturation at one.
`usedj` identifies the denominator and `room` makes the sample nonempty. -/
theorem fresh_fiber_le (used : Finset (D × D)) (rate capacity : Finset D)
    (j : ℕ) (usedj : used.card = j) (room : j < (Fintype.card D) ^ 2)
    (nonempty : (Finset.univ \ used).Nonempty) :
    Pr{let x ← draw (Finset.univ \ used) nonempty}[FiberHit rate capacity x] ≤
      min 1 ((((rate.card + capacity.card) * Fintype.card D : ℕ) : ENNReal) /
          ((Fintype.card D) ^ 2 - j : ℕ)) := by
  have _ := room
  apply le_min (prEvent_le_one _)
  rw [draw_event]
  have card : (Finset.univ \ used).card = (Fintype.card D) ^ 2 - j := by
    simp [Finset.card_sdiff_of_subset (Finset.subset_univ used), usedj,
      Fintype.card_prod, pow_two]
  rw [card]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast fiber_card_le (Finset.univ \ used) rate capacity) _

end ZkcSecurity.Probability.PermutationExposure
