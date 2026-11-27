module

public import ZkcFormal.Written.Soundness
public import ZkcFormal.Written.Bound
public import ZkcFormal.Written.SiteCaps
public import ZkcFormal.ChargedReturn

@[expose] public section
set_option autoImplicit false

/-! The judgment by fees of a written verifier at a short application: within a table of caps
and a budget, the installed verifier is judged never to return at a rejected statement. A
judgment within a budget gives the bound of `Soundness` at that budget, and so at every number
above it. The statement of soundness does not read this module. -/

namespace ZkcFormal.Written.Fees

open Zkc.Core Zkc.Subject ProbabilisticProcess
open scoped ENNReal

open Goal.Internal
variable {V : Vocabulary} (M : Model V)
variable {pkg : Package V} {scheme : WrittenRoot pkg} (app : ShortApplication scheme)
variable (draws : LawDraws M) (caps : CapTable)

/-- **The fee judgment within a budget.** On every path and every valid verifier input at which
the short application is rejected, the installed verifier is judged never to return: each fee
is paid at its site within the table's allowance for that site, and the fees of a run add up to
at most `budget`. The budget is the judgment's own number; the table bounds each fee. -/
def JudgedWithin (budget : ℚ≥0) : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Soundness.Rejected M app pkg.installed app.relation.member xs →
      (roleMeaning M pkg.installed scheme.entry.member scheme.verifier path xs).interpret
        (.charged (Permitted M) (paysWithin (lawSamplers M draws) (caps.allowance M path)))
        (fun _ _ ↦ False) (fun _ _ ↦ True) budget

/-- The fee judgment within the table's own budget, the total of its caps along one run. -/
def Judged : Prop := JudgedWithin M app draws caps caps.budget

/-- A fee judgment within a budget gives the installed bound at that budget. -/
theorem installed_at_budget {budget : ℚ≥0} (judged : JudgedWithin M app draws caps budget) :
    Soundness.Installed M app draws (toProbability budget) :=
  fun path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦
    returnsWithin_of_never _ _ _ _ _ (h rejected)) (judged path)

/-- **The step of fees to the installed bound**: a fee judgment within a budget that is at most
the bound. -/
theorem installed_of_judged {budget : ℚ≥0} (judged : JudgedWithin M app draws caps budget)
    {b : ℝ≥0∞} (le : toProbability budget ≤ b) : Soundness.Installed M app draws b :=
  Soundness.installed_mono M app draws le (installed_at_budget M app draws caps judged)

/-- A fee judgment within the table's budget gives the installed bound at the table's total. -/
theorem installed_at_total (judged : Judged M app draws caps) :
    Soundness.Installed M app draws caps.total :=
  installed_at_budget M app draws caps judged

/-- A budget that is a count over a positive count is that bound's limit: the lemma between the
spelling of a budget as a probability and the spelling of a bound. -/
theorem toProbability_eq_limit {count total : ℕ} (positive : 0 < total) :
    toProbability ((count : ℚ≥0) / total) = (⟨count, total, positive⟩ : Bound).limit := by
  rw [toProbability_natCast_div count total positive]
  rfl

/-- The total of a table whose budget is a count over a positive count is that bound's limit. -/
theorem total_eq_limit {count total : ℕ} (positive : 0 < total)
    (budget : caps.budget = (count : ℚ≥0) / total) :
    caps.total = (⟨count, total, positive⟩ : Bound).limit := by
  rw [CapTable.total, budget, toProbability_eq_limit]

/-! ## A table's budget against a bound, decided

What the command of the fee facts (`ZkcFormal.Written.FeeFacts`) evaluates and applies. Each
decision is a closed definition of this module, so the instances that it runs on are fixed here
and not where the command is called; each fact is a theorem from the decision's value. -/

/-- A bound as a nonnegative rational. -/
def ratio (b : Bound) : ℚ≥0 := (b.numerator : ℚ≥0) / b.denominator

/-- A bound's rational, as a probability, is its limit. -/
theorem toProbability_ratio (b : Bound) : toProbability (ratio b) = b.limit :=
  toProbability_natCast_div b.numerator b.denominator b.positive

/-- Whether the table's budget is at most the bound. -/
def within (b : Bound) : Bool := decide (caps.budget ≤ ratio b)

/-- Whether the table's budget is the bound. -/
def atBound (b : Bound) : Bool := decide (caps.budget = ratio b)

/-- The numerator of the number at which the budget is stated: the bound's where the budget is
the bound, the budget's own in lowest terms otherwise. -/
def budgetNumerator (b : Bound) : ℕ := if atBound caps b then b.numerator else caps.budget.num

/-- The denominator of the number at which the budget is stated. -/
def budgetDenominator (b : Bound) : ℕ := if atBound caps b then b.denominator else caps.budget.den

/-- Whether the table's budget is `count / total`. -/
def budgetIs (count total : ℕ) : Bool := decide (caps.budget = (count : ℚ≥0) / total)

/-- The table's budget as a number. -/
theorem budget_eq (count total : ℕ) (is : budgetIs caps count total = true) :
    caps.budget = (count : ℚ≥0) / total :=
  of_decide_eq_true is

/-- The total of a table whose budget is the bound is the bound's limit. -/
theorem total_eq_limit_of_atBound (b : Bound) (at_ : atBound caps b = true) : caps.total = b.limit := by
  rw [CapTable.total, of_decide_eq_true at_, toProbability_ratio]

/-- **The fee judgment within the budget `count / total`**: the judgment that the fee facts name. -/
def JudgedAt (count total : ℕ) : Prop := JudgedWithin M app draws caps ((count : ℚ≥0) / total)

/-- **The step of fees to a goal's bound**: a fee judgment within the table's budget, where that
budget is at most the bound. -/
theorem installed_of_judgedAt {count total : ℕ} (judged : JudgedAt M app draws caps count total)
    (is : budgetIs caps count total = true) (b : Bound) (le : within caps b = true) :
    Soundness.Installed M app draws b.limit :=
  installed_of_judged M app draws caps judged <| by
    rw [← budget_eq caps count total is, ← toProbability_ratio]
    exact toProbability_mono (of_decide_eq_true le)

end ZkcFormal.Written.Fees
