module

public import ZkcFormal.ReturnExperiment
public import ZkcFormal.ChargedProbability

@[expose] public section

/-!
From a judgment with fees to the experiment of a bound on returns.

`returnsWithin_of_charged` takes a judgment with fees within a budget to the experiment: a
process judged never to return a value of `bad`, with every fee within what the effect that
pays it is allowed, returns one with probability at most the budget.
-/

namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core OracleComp
open scoped NNRat ENNReal

variable {S : Sig} {H A : Type}

/-- **From the judgment with fees to the experiment.** A process that is judged, within a budget
and with every fee within what the effect that pays it is allowed, never to return a value of
`bad`, returns one with probability at most the budget. -/
theorem returnsWithin_of_charged (p : Process S H A) (samplers : Samplers S)
    (allowance : S.Op → ℚ≥0) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop) (budget : ℚ≥0)
    (judged : p.interpret (.charged allowed (paysWithin samplers allowance)) (fun a _ => ¬ bad a)
      (fun _ _ => True) budget) :
    ReturnsWithin p samplers allowed bad (toProbability budget) := by
  intro σ service conforms s
  have bound := allowed_bounds_probability service samplers allowance allowed bad conforms.permitted
    conforms.follows p budget s judged
  rw [prEvent_run service p s fun outcome => ∃ a, outcome = .returned a ∧ bad a] at bound
  refine le_trans (le_of_eq (prEvent_congr _ _ _ fun out => ?_)) bound
  exact exists_congr fun _ => and_congr_left fun _ => outcomeOf_eq_returned.symm

/-- A process that is judged never to return, within a budget and with every fee within what
the effect that pays it is allowed, returns with probability at most the budget. -/
theorem returnsWithin_of_never (p : Process S H A) (samplers : Samplers S)
    (allowance : S.Op → ℚ≥0) (allowed : ∀ op, S.Reply op → Prop) (budget : ℚ≥0)
    (judged : p.interpret (.charged allowed (paysWithin samplers allowance)) (fun _ _ => False)
      (fun _ _ => True) budget) :
    ReturnsWithin p samplers allowed (fun _ => True) (toProbability budget) :=
  returnsWithin_of_charged p samplers allowance allowed (fun _ => True) budget (by simpa using judged)

end ZkcFormal.ProbabilisticProcess
