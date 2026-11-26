module

public import ZkcFormal.ChargedProbability
public import Zkc.Core.World.Stack
public import Zkc.Core.Program.Links
public import Zkc.Subject.Charges
public import ZkcFormal.WalkLabels

@[expose] public section

/-!
What a table of caps allows the effects of a run, and what it adds up to.

A root has a table (`CapTable`): the uses that it reaches, a use being a definition at the
proof arguments of one of its applications, with the caps of its charged draws and with its
calls. Three numbers stay apart.

- **The cap of a draw** is what each occurrence of the draw may be charged at most. The
  allowance of an effect of a run that starts at `start` is the cap of the draw at its site
  below `start`, found from the root's use through the applications of the site
  (`CapTable.allowance`), whatever iteration or attempt the occurrence is in; an effect at a
  draw without a cap, or not below `start`, is allowed nothing.
- **The sum of the fees along a path** is what the judgment with fees bounds by its budget.
- **The total** of a use is what one run of its definition can be charged at most: the caps
  of its draws times their counts and, for each call, its count times the total of the callee's
  use, in sequence, and at a choice the larger of the two arms, of which a run takes one
  (`CapTable.totals`, `Core.Tally.total`); the total of the table is that of the root (`CapTable.budget`, and `CapTable.total` as a probability). It is a bound that a
  proof has to meet and never an assumption: a judgment checks the fees against the budget on
  every path.

The cap of a draw is read by the frontend from the `charge` of the definition that holds it.
The counts are not taken from the frontend: `CapTable.counted` says of a stored program and a
root that every use has the counts that its definition gives, and the kernel decides it on the
stored program of a module.
-/

namespace ZkcFormal.Written
open Zkc.Core ProbabilisticProcess OracleComp
open Zkc.Subject (CapTable UseCaps DrawCap CallCap)
open scoped NNRat NNReal ENNReal

/-- The cap of a draw: its numerator over its denominator. -/
def _root_.Zkc.Subject.DrawCap.cap (draw : DrawCap) : ℚ≥0 :=
  (draw.numerator : ℚ≥0) / draw.denominator

/-- The cap of a draw below the use at a place, through applications: nothing where the use has
no cap for the draw, or no call at an application. -/
def _root_.Zkc.Subject.CapTable.capFrom (table : CapTable) (place : Nat) (through : List Key)
    (key : Key) : ℚ≥0 :=
  ((table.useAtPath place through).bind fun use => use.draws.find? fun draw => draw.key = key).elim 0
    DrawCap.cap

/-- Below a call, the caps are those of the callee's use. -/
theorem _root_.Zkc.Subject.CapTable.capFrom_call (table : CapTable) (place : Nat)
    (application : Key) (through : List Key) (key : Key) (call : CallCap)
    (has : table.callAt place application = some call) :
    table.capFrom place (application :: through) key = table.capFrom call.callee through key := by
  simp [CapTable.capFrom, CapTable.useAtPath, has]

/-- The cap of a site in a table, from the root's use. -/
def _root_.Zkc.Subject.CapTable.cap (table : CapTable) (site : Site) : ℚ≥0 :=
  table.capFrom table.root site.through site.key

/-- What a table allows an effect of a run of the use at `place` that starts at `start`: the cap
of the site of the effect below `start`. -/
def _root_.Zkc.Subject.CapTable.allowanceFrom {V : Vocabulary} (M : Model V)
    (table : CapTable) (place : Nat) (start : List Frame) (op : ROp M) : ℚ≥0 :=
  ((ROp.occurrence M op).siteBelow start).elim 0 fun site =>
    table.capFrom place site.through site.key

/-- What a table allows an effect of a run of the root that starts at `start`. -/
abbrev _root_.Zkc.Subject.CapTable.allowance {V : Vocabulary} (M : Model V)
    (table : CapTable) (start : List Frame) (op : ROp M) : ℚ≥0 :=
  table.allowanceFrom M table.root start op

/-- **The allowance at an occurrence.** An effect that occurs at the start's path and a rest is
allowed the cap of the site with the applications of the rest: under iterations alone, the cap
of the use's own draw, whatever their numbers. -/
theorem _root_.Zkc.Subject.CapTable.allowanceFrom_at {V : Vocabulary} (M : Model V)
    (table : CapTable) (place : Nat) (start rest : List Frame) (key : Key) (op : ROp M)
    (occurs : ROp.occurrence M op = ⟨start ++ rest, key⟩) :
    table.allowanceFrom M place start op = table.capFrom place (Frame.applications rest) key := by
  simp [CapTable.allowanceFrom, occurs, Occurrence.siteBelow_append]

/-- The total of each use of a table. -/
def _root_.Zkc.Subject.CapTable.totals (table : CapTable) : List ℚ≥0 :=
  table.totalsIn ℚ≥0

/-- The budget of the use at a place: its total. -/
def _root_.Zkc.Subject.CapTable.budgetAt (table : CapTable) (place : Nat) : ℚ≥0 :=
  table.totalAt ℚ≥0 place

/-- The budget of a table: the total of the root's use. -/
def _root_.Zkc.Subject.CapTable.budget (table : CapTable) : ℚ≥0 :=
  table.budgetAt table.root

/-- The total of a table, as a probability. -/
noncomputable def _root_.Zkc.Subject.CapTable.total (table : CapTable) : ℝ≥0∞ :=
  toProbability table.budget

/-- A table whose budget is within a ratio of naturals has its total within that ratio. -/
theorem _root_.Zkc.Subject.CapTable.total_le_div (table : CapTable) (numerator denominator : ℕ)
    (positive : 0 < denominator)
    (within : table.budget ≤ (numerator : ℚ≥0) / denominator) :
    table.total ≤ (numerator : ℝ≥0∞) / denominator := by
  rw [← toProbability_natCast_div numerator denominator positive]
  exact toProbability_mono within

section
variable {S : Sig} {H A : Type}

/-- **The budget frame.** A process judged within a budget is judged within the budget and
`extra` more, with a postcondition and a stop that see `extra` more. -/
theorem charged_frame (allowed : ∀ op, S.Reply op → Prop)
    (small : (op : S.Op) → ℚ≥0 → (S.Reply op → Prop) → Prop) (extra : ℚ≥0)
    (done done' : A → ℚ≥0 → Prop) (halt halt' : H → ℚ≥0 → Prop)
    (shiftDone : ∀ a t, done a t → done' a (t + extra))
    (shiftHalt : ∀ e t, halt e t → halt' e (t + extra)) (p : Process S H A) :
    ∀ budget, p.interpret (.charged allowed small) done halt budget →
      p.interpret (.charged allowed small) done' halt' (budget + extra) := by
  induction p with
  | done a => exact fun budget judged => shiftDone a budget judged
  | halt e => exact fun budget judged => shiftHalt e budget judged
  | call op k ih =>
    rintro budget ⟨fee, bad, le, ok, next⟩
    refine ⟨fee, bad, le.trans le_self_add, ok, fun v allowedV kept => ?_⟩
    rw [← tsub_add_eq_add_tsub le]
    exact ih v (budget - fee) (next v allowedV kept)

end

end ZkcFormal.Written
