module

public import ZkcFormal.Value
public import ZkcFormal.ChargedProbability

@[expose] public section

/-!
From a judgment with fees to the value of a process, and so to the experiment of a bound on
returns.

A process judged within a budget not to return badly has a value of at most the budget
(`charged_bounds_value`), for every signature and every policy whose fees are fees of the
samplers. The value is what bounds the probability of a bad return against every service that
draws as the samplers do and answers only what is allowed (`ZkcFormal.Value`); no induction
here is about a service.

`returnsWithin_of_charged` takes a judgment with fees within a budget to the experiment: a
process judged never to return a value of `bad`, with every fee within what the effect that
pays it is allowed, returns one with probability at most the budget. It is two steps: the
judgment bounds the value of the process (`charged_bounds_value`), and the value is the
experiment (`Value.returnsWithin_of_value`).
-/

namespace ZkcFormal.ProbabilisticProcess
open Zkc.Core OracleComp
open scoped NNRat ENNReal

variable {S : Sig} {H A : Type}

/-! ## Fees bound the value -/

open Value in
/-- One effect: where a fee pays for the excluded replies and every other allowed reply leaves a
value of at most `rest`, the effect's value is at most the fee and `rest` together. -/
theorem node_le_fee_add {X : Type} (draw : Option (ProbComp X)) (allowed excluded : X → Prop)
    (fee rest : ℝ≥0∞) (next : X → ℝ≥0∞)
    (pays : (∀ x, ¬ excluded x) ∨ ∃ coin, draw = some coin ∧ Pr{let x ← coin}[excluded x] ≤ fee)
    (unit : ∀ x, next x ≤ 1) (outside : ∀ x, allowed x → ¬ excluded x → next x ≤ rest) :
    node draw allowed next ≤ fee + rest := by
  classical
  rcases pays with free | ⟨coin, rfl, weight⟩
  · exact (node_bound _ _ fun x ok => outside x ok (free x)).trans le_add_self
  · change mean coin (mask allowed next) ≤ _
    calc
      _ ≤ mean coin (fun x => if excluded x then 1 else rest) := mean_mono _ fun x => by
        by_cases hp : allowed x <;> by_cases he : excluded x <;> simp [mask, hp, he, unit, outside]
      _ ≤ fee + rest := by
        rw [mean_cases, mul_one]
        exact add_le_add weight (mul_le_of_le_one_left' (prEvent_le_one _))

/-- **A judgment with fees bounds the value.** A process judged within a budget not to return
badly, under a policy whose every fee is a fee of the samplers, has a value of at most the
budget. With `Value.returnsWithin_iff` this is the bound on the probability of a bad return
against every conforming service. -/
theorem charged_bounds_value (samplers : Samplers S) (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop)
    (pays : ∀ op fee excluded, small op fee excluded → paysBy samplers op fee excluded)
    (bad : A → Prop) (p : Process S H A) (budget : ℚ≥0)
    (judged : p.interpret (.charged allowed small) (fun a _ => ¬ bad a) (fun _ _ => True) budget) :
    Value.value samplers allowed bad p ≤ toProbability budget := by
  classical
  induction p generalizing budget with
  | done a =>
    change ¬ bad a at judged
    change Value.indicator bad a ≤ _
    simp [Value.indicator, judged]
  | halt h => exact zero_le
  | call op next ih =>
    obtain ⟨fee, excluded, within, isSmall, outside⟩ := judged
    apply le_trans (b := toProbability fee + toProbability (budget - fee))
    · apply node_le_fee_add (samplers op) (allowed op) excluded _ _ _ _
        (fun x => Value.value_le_one samplers allowed bad (next x))
        (fun x ok kept => ih x _ (outside x ok kept))
      rcases pays op fee excluded isSmall with ⟨_, nothing⟩ | sampled
      · exact Or.inl nothing
      · exact Or.inr sampled
    · rw [← toProbability_add, add_tsub_cancel_of_le within]

/-- **From the judgment with fees to the experiment.** A process that is judged, within a budget
and with every fee within what the effect that pays it is allowed, never to return a value of
`bad`, returns one with probability at most the budget. -/
theorem returnsWithin_of_charged (p : Process S H A) (samplers : Samplers S)
    (allowance : S.Op → ℚ≥0) (allowed : ∀ op, S.Reply op → Prop) (bad : A → Prop) (budget : ℚ≥0)
    (judged : p.interpret (.charged allowed (paysWithin samplers allowance)) (fun a _ => ¬ bad a)
      (fun _ _ => True) budget) :
    ReturnsWithin p samplers allowed bad (toProbability budget) :=
  Value.returnsWithin_of_value p samplers allowed bad
    (charged_bounds_value samplers allowed _ (fun _ _ _ paid => paid.1) bad p budget judged)

end ZkcFormal.ProbabilisticProcess
