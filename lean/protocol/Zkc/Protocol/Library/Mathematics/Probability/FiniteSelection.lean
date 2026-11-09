module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.Vector.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section

/-! First admissible selection from a complete, fixed-length draw history.

`select` is executable postprocessing, and `retain` returns the entire supplied history even
after an early admissible value. `drawAndSelect` draws the complete history with Mathlib's
`List.Vector.mOfFn` before selecting. In particular, it is not an early-exit random search.

The union bound accepts an arbitrary joint history law. Independent-draw results explicitly
use Mathlib's monadic finite product, rather than infer independence from uniform marginals.
Admissibility is an argument: an OOD client must supply its actual excluded domains and any
nonzero condition.
These mathematical laws do not establish correspondence with a source protocol or provider.
-/

set_option autoImplicit false

namespace ZkcSecurity.Probability.FiniteSelection

open MeasureTheory
open scoped BigOperators ENNReal

variable {α : Type} {n : ℕ}

/-- The first admissible value, or `none` when every attempt is invalid. -/
def select (admissible : α → Bool) (history : Fin n → α) : Option α :=
  (List.ofFn history).find? admissible

/-- Selection together with every draw, including those after the selected value. -/
def retain (admissible : α → Bool) (history : Fin n → α) :
    Option α × (Fin n → α) :=
  (select admissible history, history)

@[simp] theorem retain_history (admissible : α → Bool) (history : Fin n → α) :
    (retain admissible history).2 = history := rfl

@[simp] theorem retained_length (admissible : α → Bool) (history : Fin n → α) :
    (List.ofFn (retain admissible history).2).length = n := by
  simp

@[simp] theorem select_empty (admissible : α → Bool) (history : Fin 0 → α) :
    select admissible history = none := by
  simp [select]

@[simp] theorem select_cons (admissible : α → Bool) (x : α) (history : Fin n → α) :
    select admissible (Fin.cons x history) =
      if admissible x then some x else select admissible history := by
  cases hx : admissible x <;> simp [select, hx]

@[simp] theorem select_one (admissible : α → Bool) (history : Fin 1 → α) :
    select admissible history = if admissible (history 0) then some (history 0) else none := by
  rw [select, List.ofFn_succ]
  cases hx : admissible (history 0) <;> simp [hx]

/-- Successful selection is admissible and is a member of the supplied history. -/
theorem selected_valid (admissible : α → Bool) (history : Fin n → α) (x : α)
    (selected : select admissible history = some x) :
    admissible x = true ∧ ∃ i, history i = x := by
  exact ⟨List.find?_some selected, List.mem_ofFn.mp (List.mem_of_find?_eq_some selected)⟩

/-- Exhaustion is exactly the absence of any admissible draw. -/
theorem select_eq_none_iff (admissible : α → Bool) (history : Fin n → α) :
    select admissible history = none ↔ ∀ i, admissible (history i) = false := by
  simp [select, List.find?_eq_none, List.mem_ofFn, Bool.not_eq_true]

/-- A successful output is the earliest admissible entry, including with repeated values. -/
theorem select_eq_some_iff (admissible : α → Bool) (history : Fin n → α) (x : α) :
    select admissible history = some x ↔
      ∃ i, history i = x ∧ admissible x = true ∧
        ∀ j, j < i → admissible (history j) = false := by
  rw [select, List.find?_eq_some_iff_getElem]
  simp only [List.length_ofFn, List.getElem_ofFn]
  constructor
  · rintro ⟨valid, i, hi, hx, earlier⟩
    exact ⟨⟨i, hi⟩, hx, valid, fun j hj ↦ by simpa using earlier j hj⟩
  · rintro ⟨i, hx, valid, earlier⟩
    exact ⟨valid, i, i.isLt, hx, fun j hj ↦ by
      simpa using earlier ⟨j, hj.trans i.isLt⟩ hj⟩

/-- The output is present and satisfies the chosen bad-event predicate. -/
def SelectedBad (admissible : α → Bool) (bad : α → Prop) (history : Fin n → α) : Prop :=
  ∃ x, select admissible history = some x ∧ bad x

@[simp] theorem selectedBad_cons (admissible : α → Bool) (bad : α → Prop) (x : α)
    (history : Fin n → α) :
    SelectedBad admissible bad (Fin.cons x history) ↔
      if admissible x then bad x else SelectedBad admissible bad history := by
  cases hx : admissible x <;> simp [SelectedBad, hx]

/-- A bad output must have occurred as an admissible bad draw. -/
theorem selectedBad_implies_attempt (admissible : α → Bool) (bad : α → Prop)
    (history : Fin n → α) (h : SelectedBad admissible bad history) :
    ∃ i, admissible (history i) = true ∧ bad (history i) := by
  obtain ⟨x, selected, hx⟩ := h
  obtain ⟨valid, i, hi⟩ := selected_valid admissible history x selected
  exact ⟨i, hi ▸ valid, hi ▸ hx⟩

/-- The union bound needs no independence premise on the joint history PMF. -/
theorem selectedBad_le_sum (admissible : α → Bool) (bad : α → Prop)
    (histories : PMF (Fin n → α)) :
    histories.toOuterMeasure {history | SelectedBad admissible bad history} ≤
      ∑ i, histories.toOuterMeasure {history |
        admissible (history i) = true ∧ bad (history i)} := by
  refine (histories.toOuterMeasure.mono ?_).trans
    (measure_iUnion_fintype_le histories.toOuterMeasure _)
  intro history h
  obtain ⟨i, hi⟩ := selectedBad_implies_attempt admissible bad history h
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The iid finite product uses Mathlib's existing vector-valued monadic traversal. -/
noncomputable def drawHistory (draw : PMF α) (n : ℕ) : PMF (Fin n → α) :=
  (List.Vector.mOfFn (fun _ : Fin n ↦ draw)).map List.Vector.get

@[simp] theorem drawHistory_zero (draw : PMF α) :
    drawHistory draw 0 = PMF.pure Fin.elim0 := by
  change (PMF.pure List.Vector.nil).map List.Vector.get = PMF.pure Fin.elim0
  rw [PMF.pure_map]
  apply congrArg PMF.pure
  funext i
  exact i.elim0

theorem drawHistory_succ (draw : PMF α) (n : ℕ) :
    drawHistory draw (n + 1) =
      draw.bind fun x ↦ (drawHistory draw n).map (Fin.cons x) := by
  unfold drawHistory
  change (draw.bind fun x ↦
    (List.Vector.mOfFn (fun _ : Fin n ↦ draw)).bind fun history ↦
      PMF.pure (x ::ᵥ history)).map List.Vector.get = _
  simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  apply congrArg (PMF.bind draw)
  funext x
  apply congrArg (PMF.bind (List.Vector.mOfFn (fun _ : Fin n ↦ draw)))
  funext history
  apply congrArg PMF.pure
  funext i
  refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp [List.Vector.get_cons_succ]

/-- The full history is drawn first, and selection preserves every coordinate. -/
noncomputable def drawAndSelect (admissible : α → Bool) (draw : PMF α) (n : ℕ) :
    PMF (Option α × (Fin n → α)) :=
  (drawHistory draw n).map (retain admissible)

theorem drawAndSelect_history (admissible : α → Bool) (draw : PMF α) (n : ℕ) :
    (drawAndSelect admissible draw n).map Prod.snd = drawHistory draw n := by
  rw [drawAndSelect, PMF.map_comp]
  change (drawHistory draw n).map id = drawHistory draw n
  exact PMF.map_id _

private theorem mass_univ {β : Type} (p : PMF β) : p.toOuterMeasure Set.univ = 1 :=
  (p.toOuterMeasure_apply_eq_one_iff _).mpr (Set.subset_univ _)

/-- Exact exhaustion recurrence; all later attempts remain in the sampled history. -/
theorem independent_exhaustion_succ (admissible : α → Bool) (draw : PMF α) (n : ℕ) :
    (drawHistory draw (n + 1)).toOuterMeasure {history | select admissible history = none} =
      draw.toOuterMeasure {x | admissible x = false} *
        (drawHistory draw n).toOuterMeasure {history | select admissible history = none} := by
  classical
  rw [drawHistory_succ, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    ← ENNReal.tsum_mul_right]
  apply tsum_congr
  intro x
  cases hx : admissible x <;>
    simp [PMF.toOuterMeasure_map_apply, Set.preimage, hx]

theorem independent_exhaustion (admissible : α → Bool) (draw : PMF α) (n : ℕ) :
    (drawHistory draw n).toOuterMeasure {history | select admissible history = none} =
      draw.toOuterMeasure {x | admissible x = false} ^ n := by
  induction n with
  | zero =>
      simp
      funext i
      exact i.elim0
  | succ n ih => rw [independent_exhaustion_succ, ih, pow_succ']

/-- A bad first admissible draw, or a later bad selection after an invalid first draw. -/
theorem independent_selectedBad_succ (admissible : α → Bool) (bad : α → Prop)
    (draw : PMF α) (n : ℕ) :
    (drawHistory draw (n + 1)).toOuterMeasure {history | SelectedBad admissible bad history} =
      draw.toOuterMeasure {x | admissible x = true ∧ bad x} +
        draw.toOuterMeasure {x | admissible x = false} *
          (drawHistory draw n).toOuterMeasure {history | SelectedBad admissible bad history} := by
  classical
  rw [drawHistory_succ, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply tsum_congr
  intro x
  cases hx : admissible x <;> by_cases hb : bad x <;>
    simp [PMF.toOuterMeasure_map_apply, Set.preimage, hx, hb, mass_univ]

/-- Exact unconditioned iid bad-output mass; exhaustion remains a separate outcome. -/
theorem independent_selectedBad (admissible : α → Bool) (bad : α → Prop)
    (draw : PMF α) (n : ℕ) :
    (drawHistory draw n).toOuterMeasure {history | SelectedBad admissible bad history} =
      draw.toOuterMeasure {x | admissible x = true ∧ bad x} *
        ∑ k ∈ Finset.range n, draw.toOuterMeasure {x | admissible x = false} ^ k := by
  induction n with
  | zero => simp [SelectedBad]
  | succ n ih =>
      rw [independent_selectedBad_succ, ih, Finset.sum_range_succ']
      simp only [pow_succ', Finset.mul_sum, mul_add, pow_zero, mul_one]
      ac_rfl

@[simp] theorem selectedBad_true (admissible : α → Bool) (history : Fin n → α) :
    SelectedBad admissible (fun _ ↦ True) history ↔ (select admissible history).isSome := by
  simp [SelectedBad, Option.isSome_iff_exists]

/-- Success mass without conditioning away refusal. -/
theorem independent_success (admissible : α → Bool) (draw : PMF α) (n : ℕ) :
    (drawHistory draw n).toOuterMeasure {history | (select admissible history).isSome} =
      draw.toOuterMeasure {x | admissible x = true} *
        ∑ k ∈ Finset.range n, draw.toOuterMeasure {x | admissible x = false} ^ k := by
  simpa only [selectedBad_true, and_true] using
    independent_selectedBad admissible (fun _ ↦ True) draw n

private theorem mass_ne_top {β : Type} (p : PMF β) (s : Set β) : p.toOuterMeasure s ≠ ⊤ := by
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    ((p.toOuterMeasure.mono (Set.subset_univ _)).trans_eq (mass_univ p))

/-- Successful iid selection has the one-draw law conditioned on admissibility. Positive
success mass is proved, rather than treating conditioning on an impossible event as uniform. -/
theorem independent_selectedBad_conditional (admissible : α → Bool) (bad : α → Prop)
    (draw : PMF α) (n : ℕ) (attempts : 0 < n)
    (canSucceed : 0 < draw.toOuterMeasure {x | admissible x = true}) :
    0 < (drawHistory draw n).toOuterMeasure {history | (select admissible history).isSome} ∧
      (drawHistory draw n).toOuterMeasure {history | SelectedBad admissible bad history} /
        (drawHistory draw n).toOuterMeasure {history | (select admissible history).isSome} =
      draw.toOuterMeasure {x | admissible x = true ∧ bad x} /
        draw.toOuterMeasure {x | admissible x = true} := by
  have positive : (1 : ℝ≥0∞) ≤
      ∑ k ∈ Finset.range n, draw.toOuterMeasure {x | admissible x = false} ^ k := by
    simpa only [pow_zero] using
      (Finset.single_le_sum (fun k (_ : k ∈ Finset.range n) ↦
        (show (0 : ℝ≥0∞) ≤ draw.toOuterMeasure {x | admissible x = false} ^ k from bot_le))
        (Finset.mem_range.mpr attempts))
  constructor
  · rw [independent_success]
    exact ENNReal.mul_pos_iff.mpr ⟨canSucceed, lt_of_lt_of_le zero_lt_one positive⟩
  · rw [independent_selectedBad, independent_success]
    apply ENNReal.mul_div_mul_right
    · exact ne_of_gt (lt_of_lt_of_le zero_lt_one positive)
    · exact ENNReal.sum_ne_top.mpr fun k _ ↦ ENNReal.pow_ne_top (mass_ne_top _ _)

/-- One attempt draws once and refuses if that value is inadmissible. -/
theorem oneShot_selectedBad (admissible : α → Bool) (bad : α → Prop) (draw : PMF α) :
    (drawHistory draw 1).toOuterMeasure {history | SelectedBad admissible bad history} =
      draw.toOuterMeasure {x | admissible x = true ∧ bad x} := by
  simpa using independent_selectedBad admissible bad draw 1

section Uniform

variable [Fintype α] [Nonempty α]

/-- The standard uniform finite PMF, constructed with Mathlib's `PMF.ofFintype`. -/
noncomputable def uniformDraw (α : Type) [Fintype α] [Nonempty α] : PMF α :=
  PMF.ofFintype (fun _ ↦ (Fintype.card α : ℝ≥0∞)⁻¹) (by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp [Fintype.card_ne_zero]) (by simp))

theorem uniformDraw_event (event : α → Prop) [DecidablePred event] :
    (uniformDraw α).toOuterMeasure {x | event x} =
      (Finset.univ.filter event).card / (Fintype.card α : ℝ≥0∞) := by
  classical
  rw [PMF.toOuterMeasure_apply_fintype]
  simp [uniformDraw, Set.indicator_apply, ← Finset.sum_filter, div_eq_mul_inv]

theorem uniform_exhaustion (admissible : α → Bool) (n : ℕ) :
    (drawHistory (uniformDraw α) n).toOuterMeasure {history | select admissible history = none} =
      ((Finset.univ.filter fun x ↦ admissible x = false).card /
        (Fintype.card α : ℝ≥0∞)) ^ n := by
  rw [independent_exhaustion, uniformDraw_event]

/-- Conditional uniformity on the admissible carrier, together with positive success mass. -/
theorem uniform_selectedBad_conditional (admissible : α → Bool) (bad : α → Prop)
    [DecidablePred bad] (n : ℕ) (attempts : 0 < n) (nonempty : ∃ x, admissible x = true) :
    0 < (drawHistory (uniformDraw α) n).toOuterMeasure
        {history | (select admissible history).isSome} ∧
      (drawHistory (uniformDraw α) n).toOuterMeasure
          {history | SelectedBad admissible bad history} /
        (drawHistory (uniformDraw α) n).toOuterMeasure
          {history | (select admissible history).isSome} =
      (Finset.univ.filter fun x ↦ admissible x = true ∧ bad x).card /
        ((Finset.univ.filter fun x ↦ admissible x = true).card : ℝ≥0∞) := by
  have canSucceed : 0 < (uniformDraw α).toOuterMeasure {x | admissible x = true} := by
    rw [uniformDraw_event]
    apply ENNReal.div_pos
    · have members : (Finset.univ.filter fun x : α ↦ admissible x = true).Nonempty := by
        obtain ⟨x, hx⟩ := nonempty
        exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩
      exact_mod_cast (Finset.card_ne_zero.mpr members)
    · simp
  obtain ⟨positive, ratio⟩ :=
    independent_selectedBad_conditional admissible bad (uniformDraw α) n attempts canSucceed
  refine ⟨positive, ?_⟩
  rw [ratio, uniformDraw_event, uniformDraw_event]
  simp only [div_eq_mul_inv]
  apply ENNReal.mul_div_mul_right
  · simp
  · simp [Fintype.card_ne_zero]

end Uniform

end ZkcSecurity.Probability.FiniteSelection
