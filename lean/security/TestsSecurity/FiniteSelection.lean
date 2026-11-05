import ZkcSecurity.Mathematics.Probability.FiniteSelection
import ZkcTools.DeclarationAudit

/-! Kernel-checked finite selection controls. The seven-point carrier has five admissible
points. The same admissibility predicate is tested under iid and repeated-draw histories;
uniform coordinate marginals alone do not justify iid exhaustion. No source connection or
cryptographic provider correspondence is asserted by these controls. -/

namespace TestsSecurity.FiniteSelection

open ZkcSecurity.Probability.FiniteSelection
open scoped ENNReal

def admissible (x : Fin 7) : Bool := decide (2 ≤ x.val)

def earlyHistory : Fin 3 → Fin 7 := ![2, 3, 4]

def laterHistory : Fin 3 → Fin 7 := ![0, 1, 5]

/-- Later admissible points do not replace the first one. -/
theorem selects_first : select admissible earlyHistory = some 2 := by decide

theorem selects_after_failures : select admissible laterHistory = some 5 := by decide

/-- Even after success at the first entry, the complete history remains observable. -/
theorem keeps_later_draws :
    (retain admissible earlyHistory).1 = some 2 ∧
      List.ofFn (retain admissible earlyHistory).2 = [2, 3, 4] := by decide

theorem refuses_exhausted : select admissible ![0, 1, 0] = none := by decide

theorem empty_refuses : select admissible (fun i : Fin 0 ↦ i.elim0) = none := by simp

theorem oneShot_refuses : select admissible ![1] = none := by decide

theorem oneShot_accepts : select admissible ![2] = some 2 := by decide

/-- Seeing a later bad draw does not make the selected value bad. -/
theorem later_bad_not_selected :
    (∃ i, earlyHistory i = 3) ∧ ¬ SelectedBad admissible (· = 3) earlyHistory := by
  unfold SelectedBad
  decide

/-- All excluded values exhaust, at every attempt count, including zero. -/
theorem all_invalid (n : ℕ) :
    (drawHistory (uniformDraw (Fin 7)) n).toOuterMeasure
      {history | select (fun _ ↦ false) history = none} = 1 := by
  rw [independent_exhaustion, uniformDraw_event]
  simp [ENNReal.div_self]

private theorem invalid_count :
    (Finset.univ.filter fun x : Fin 7 ↦ admissible x = false).card = 2 := by decide

private theorem root_count :
    (Finset.univ.filter fun x : Fin 7 ↦ admissible x = true ∧ x = 2).card = 1 := by decide

private theorem admissible_count :
    (Finset.univ.filter fun x : Fin 7 ↦ admissible x = true).card = 5 := by decide

/-- Three iid attempts exhaust with probability `(2/7)^3`. -/
theorem threeDraw_exhaustion :
    (drawHistory (uniformDraw (Fin 7)) 3).toOuterMeasure
      {history | select admissible history = none} = 8 / 343 := by
  rw [uniform_exhaustion, invalid_count]
  norm_num
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  norm_num [ENNReal.toReal_div]

/-- The unconditioned root mass keeps the refusal probability. -/
theorem threeDraw_root_mass :
    (drawHistory (uniformDraw (Fin 7)) 3).toOuterMeasure
      {history | SelectedBad admissible (· = 2) history} = 67 / 343 := by
  rw [independent_selectedBad, uniformDraw_event, uniformDraw_event, root_count, invalid_count]
  norm_num [Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div]

theorem threeDraw_success :
    (drawHistory (uniformDraw (Fin 7)) 3).toOuterMeasure
      {history | (select admissible history).isSome} = 335 / 343 := by
  rw [independent_success, uniformDraw_event, uniformDraw_event, admissible_count, invalid_count]
  norm_num [Finset.sum_range_succ]
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  norm_num [ENNReal.toReal_div]

/-- Conditional uniformity follows from the iid law, including positive success mass. -/
theorem threeDraw_conditional_root :
    (drawHistory (uniformDraw (Fin 7)) 3).toOuterMeasure
        {history | SelectedBad admissible (· = 2) history} /
      (drawHistory (uniformDraw (Fin 7)) 3).toOuterMeasure
        {history | (select admissible history).isSome} = 1 / 5 := by
  have law := (uniform_selectedBad_conditional admissible (· = 2) 3 (by decide)
    ⟨2, by decide⟩).2
  simpa only [root_count, admissible_count, Nat.cast_one, Nat.cast_ofNat] using law

theorem oneShot_root_mass :
    (drawHistory (uniformDraw (Fin 7)) 1).toOuterMeasure
      {history | SelectedBad admissible (· = 2) history} = 1 / 7 := by
  rw [oneShot_selectedBad, uniformDraw_event, root_count]
  norm_num

theorem oneShot_refusal_mass :
    (drawHistory (uniformDraw (Fin 7)) 1).toOuterMeasure
      {history | select admissible history = none} = 2 / 7 := by
  rw [uniform_exhaustion, invalid_count]
  norm_num

/-- Discarding the selection preserves the complete draw law for every count and PMF. -/
theorem draw_history_unchanged (draw : PMF (Fin 7)) (n : ℕ) :
    (drawAndSelect admissible draw n).map Prod.snd = drawHistory draw n :=
  drawAndSelect_history admissible draw n

/-- A repeated cached draw has exhaustion mass `2/7`, rather than the iid mass `4/49`. -/
theorem repeatedDraw_exhaustion :
    (uniformDraw (Fin 7)).toOuterMeasure
      {x | select admissible (fun _ : Fin 2 ↦ x) = none} = 2 / 7 := by
  have events : {x : Fin 7 | select admissible (fun _ : Fin 2 ↦ x) = none} =
      {x | admissible x = false} := by
    ext x
    simp [select_eq_none_iff]
  rw [events, uniformDraw_event, invalid_count]
  norm_num

theorem repeatedDraw_not_iid :
    ¬ (uniformDraw (Fin 7)).toOuterMeasure
      {x | select admissible (fun _ : Fin 2 ↦ x) = none} = (2 / 7 : ℝ≥0∞) ^ 2 := by
  rw [repeatedDraw_exhaustion]
  intro same
  have realSame := congrArg ENNReal.toReal same
  norm_num [ENNReal.toReal_div] at realSame

/-- Every coordinate of the repeated-draw history nevertheless has the uniform marginal. -/
theorem repeatedDraw_uniform_marginals (i : Fin 2) :
    ((uniformDraw (Fin 7)).map (fun x ↦ fun _ : Fin 2 ↦ x)).map (fun h ↦ h i) =
      uniformDraw (Fin 7) := by
  rw [PMF.map_comp]
  change (uniformDraw (Fin 7)).map id = uniformDraw (Fin 7)
  exact PMF.map_id _

/-- The generic union bound still applies to a completely correlated history. -/
theorem correlated_union_bound :
    ((uniformDraw (Fin 7)).map (fun x ↦ fun _ : Fin 2 ↦ x)).toOuterMeasure
        {history | SelectedBad admissible (· = 2) history} ≤
      ∑ i, ((uniformDraw (Fin 7)).map (fun x ↦ fun _ : Fin 2 ↦ x)).toOuterMeasure
        {history | admissible (history i) = true ∧ history i = 2} :=
  selectedBad_le_sum admissible (· = 2) _

end TestsSecurity.FiniteSelection

run_cmd do
  ZkcTools.DeclarationAudit.check
    [`ZkcSecurity.Mathematics.Probability.FiniteSelection] "FINITE-SELECTION-AXIOMS-PASS"
run_cmd ZkcTools.DeclarationAudit.checkCurrent "FINITE-SELECTION-CONTROLS-AXIOMS-PASS"
