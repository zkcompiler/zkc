import ZkcFormal.Written.Fees

/-!
The author's chain from a judgment by fees to the library's result of soundness at a chosen
bound.

A judgment by fees has its own budget; the table of caps bounds each fee. A judgment within a
budget gives `Soundness.Result` at every bound that is at least that budget, with a coverage
fact, by two steps of the library. A bound below the budget is not reached by them: the step
asks for the comparison. A goal publishes `Soundness.Result` at its row's bound; the fee facts of
a row (`ZkcFormal.Written.FeeFacts`) give the step from a judgment within the table's budget.

These theorems take a judgment as given. That a judgment exists within a budget other than its
table's is shown on a subject: the guarded verifier of `checks/WrittenBoundGuard.lean` is
judged within zero under a table whose budget is one over four.
-/

open Zkc.Core Zkc.Subject ZkcFormal ZkcFormal.ProbabilisticProcess ZkcFormal.Written
open scoped ENNReal

namespace ZkcFormalTests.FeeJudgment

variable {V : Vocabulary} (M : Model V)
variable {pkg : Package V} {scheme : WrittenRoot pkg} (app : ShortApplication scheme)
variable (draws : LawDraws M) (caps : CapTable)

/-- From a judgment within a budget and coverage to the result at a bound above the budget. -/
theorem result_of_judged {covers : NamedProgram V → Key → Key → Bool} {budget : ℚ≥0} {b : ℝ≥0∞}
    (covered : covers pkg.stored scheme.entry.header.key app.relation.header.key = true)
    (judged : Fees.JudgedWithin M app draws caps budget) (le : toProbability budget ≤ b) :
    Soundness.Result M app draws covers b :=
  Soundness.result_of_installed M app draws covered (Fees.installed_of_judged M app draws caps judged le)

/-- The judgment within the table's own budget is the judgment at the table's total. -/
theorem result_at_total {covers : NamedProgram V → Key → Key → Bool}
    (covered : covers pkg.stored scheme.entry.header.key app.relation.header.key = true)
    (judged : Fees.Judged M app draws caps) : Soundness.Result M app draws covers caps.total :=
  Soundness.result_of_installed M app draws covered (Fees.installed_at_total M app draws caps judged)

/-- A budget of one over four is the limit of the bound one over four. -/
example : toProbability ((1 : ℕ) / (4 : ℕ)) = (⟨1, 4, by decide⟩ : Bound).limit :=
  Fees.toProbability_eq_limit (by decide)

/-- A judgment within one over four reaches the bound one over four and not, by this step, a
bound below it: the comparison that the step asks for is false at one over eight. -/
example : ¬ toProbability ((1 : ℕ) / (4 : ℕ)) ≤ (⟨1, 8, by decide⟩ : Bound).limit := by
  rw [Fees.toProbability_eq_limit (by decide)]
  simp only [Bound.limit, not_le]
  rw [ENNReal.div_lt_div_iff_right (by norm_num) (by norm_num)]
  norm_num

end ZkcFormalTests.FeeJudgment
