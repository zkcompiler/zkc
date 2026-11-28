module

public import ZkcFormal.Written.Value
public import ZkcFormal.Written.Bound
public import ZkcFormal.Written.Blind
public import ZkcFormal.ChargedReturn

@[expose] public section
set_option autoImplicit false

/-! The judgment by fees of a written verifier at a short application: under an allowance of
occurrences and within a budget, the installed verifier is judged never to return at a rejected
statement (`JudgedUnder`); a table of caps gives an allowance (`JudgedWithin`). A judgment
within a budget gives the value of the verifier within that budget (`value_of_judged`), and so
the bound of `Soundness` at that budget and at every number above it. The statement of
soundness does not read this module. -/

namespace ZkcFormal.Written.Fees

open Zkc.Core Zkc.Subject ProbabilisticProcess
open scoped ENNReal

open Goal.Internal
variable {V : Vocabulary} (M : Model V)
variable {pkg : Package V} {scheme : WrittenRoot pkg} (app : ShortApplication scheme)
variable (draws : LawDraws M) (caps : CapTable)

/-- **The fee judgment under an allowance, within a budget.** On every path and every valid
verifier input at which the short application is rejected, the installed verifier is judged by
fees never to return: each fee is paid within what the allowance gives, from the path, where its
effect occurs, and the fees of a run add up to at most `budget`. The budget is the judgment's
own number; the allowance bounds each fee. -/
def JudgedUnder (allowance : List Frame → Occurrence → ℚ≥0) (budget : ℚ≥0) : Prop :=
  ∀ path : List Frame, inputs M scheme.verifier false scheme.entry.header.ins fun xs ↦
    Soundness.Rejected M app pkg.installed app.relation.member xs →
      (roleMeaning M pkg.installed scheme.entry.member scheme.verifier path xs).interpret
        (Fees.judgment draws (allowance path)) (fun _ _ ↦ False) (fun _ _ ↦ True) budget

/-- **The fee judgment within a budget**, under a table of caps: each fee is paid at its site
within the table's cap for that site. -/
def JudgedWithin (budget : ℚ≥0) : Prop := JudgedUnder M app draws caps.allowed budget

/-- The fee judgment within the table's own budget, the total of its caps along one run. -/
def Judged : Prop := JudgedWithin M app draws caps caps.budget

/-- **A fee judgment within a budget gives the value within the budget**, under every
allowance: an allowance only bounds each fee. -/
theorem value_of_judged {allowance : List Frame → Occurrence → ℚ≥0} {budget : ℚ≥0}
    (judged : JudgedUnder M app draws allowance budget) :
    Soundness.ValueWithin M app draws (toProbability budget) :=
  fun path ↦ mapInputs M _ _ _ _ (fun _ h rejected ↦
    charged_bounds_value (lawSamplers M draws) (Permitted M)
      (paysWithin (lawSamplers M draws) fun op ↦ allowance path (ROp.occurrence M op))
      (fun _ _ _ paid ↦ paid.1) (fun _ ↦ True) _ budget
      (by simpa [Fees.judgment] using h rejected)) (judged path)

/-- A fee judgment within a budget gives the installed bound at that budget: the value is within
the budget, and the installed bounds are those at or above the value. -/
theorem installed_under {allowance : List Frame → Occurrence → ℚ≥0} {budget : ℚ≥0}
    (judged : JudgedUnder M app draws allowance budget) :
    Soundness.Installed M app draws (toProbability budget) :=
  (Soundness.installed_iff M app draws _).mpr (value_of_judged M app draws judged)

/-- A fee judgment within a budget, under a table, gives the installed bound at that budget. -/
theorem installed_at_budget {budget : ℚ≥0} (judged : JudgedWithin M app draws caps budget) :
    Soundness.Installed M app draws (toProbability budget) :=
  installed_under M app draws judged

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

What the command of the fee facts (`ZkcFormal.Written.FeeFacts`) evaluates and applies. The
decisions `Budget.within` and `Budget.atBound` are those of `ZkcFormal.Written.Budget`, which the
command of a challenge reads too; each fact is a theorem from a decision's value. -/

/-- A bound's rational, as a probability, is its limit. -/
theorem toProbability_ratio (b : Bound) : toProbability (Budget.ratio b) = b.limit :=
  toProbability_natCast_div b.numerator b.denominator b.positive

/-- The numerator of the number at which the budget is stated: the bound's where the budget is
the bound, the budget's own in lowest terms otherwise. -/
def budgetNumerator (b : Bound) : ℕ := if Budget.atBound caps b then b.numerator else caps.budget.num

/-- The denominator of the number at which the budget is stated. -/
def budgetDenominator (b : Bound) : ℕ := if Budget.atBound caps b then b.denominator else caps.budget.den

/-- Whether the table's budget is `count / total`. -/
def budgetIs (count total : ℕ) : Bool := decide (caps.budget = (count : ℚ≥0) / total)

/-- The table's budget as a number. -/
theorem budget_eq (count total : ℕ) (is : budgetIs caps count total = true) :
    caps.budget = (count : ℚ≥0) / total :=
  of_decide_eq_true is

/-- The total of a table whose budget is the bound is the bound's limit. -/
theorem total_eq_limit_of_atBound (b : Bound) (at_ : Budget.atBound caps b = true) : caps.total = b.limit := by
  rw [CapTable.total, of_decide_eq_true at_, toProbability_ratio]

/-- **The fee judgment within the budget `count / total`**: the judgment that the fee facts name. -/
def JudgedAt (count total : ℕ) : Prop := JudgedWithin M app draws caps ((count : ℚ≥0) / total)

/-- **The step of fees to a goal's bound**: a fee judgment within the table's budget, where that
budget is at most the bound. -/
theorem installed_of_judgedAt {count total : ℕ} (judged : JudgedAt M app draws caps count total)
    (is : budgetIs caps count total = true) (b : Bound) (le : Budget.within caps b = true) :
    Soundness.Installed M app draws b.limit :=
  installed_of_judged M app draws caps judged <| by
    rw [← budget_eq caps count total is, ← toProbability_ratio]
    exact toProbability_mono (of_decide_eq_true le)

end ZkcFormal.Written.Fees
