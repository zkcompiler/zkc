module

public import ZkcFormal.ChargedProbability
public import Zkc.Core.World.Stack
public import Zkc.Core.Program.Links
public import Zkc.Subject.Charges
public import ZkcFormal.Written.Budget

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

Two rules meet the judgment at an effect (`charged_free`, `charged_pay`), `charged_pay_at` is
the second at a draw of the table, and the frame moves a judgment to a larger budget
(`charged_frame`).
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

/-- What a table allows at an occurrence of a run of the use at `place` that starts at `start`:
the cap of the occurrence's site below `start`. An allowance is of an occurrence: it reads
where an effect occurs and nothing else of the effect. -/
def _root_.Zkc.Subject.CapTable.allowedFrom (table : CapTable) (place : Nat) (start : List Frame)
    (at_ : Occurrence) : ℚ≥0 :=
  (at_.siteBelow start).elim 0 fun site => table.capFrom place site.through site.key

/-- What a table allows at an occurrence of a run of the root that starts at `start`. -/
abbrev _root_.Zkc.Subject.CapTable.allowed (table : CapTable) (start : List Frame)
    (at_ : Occurrence) : ℚ≥0 :=
  table.allowedFrom table.root start at_

/-- What a table allows an effect of a run of the use at `place` that starts at `start`: what it
allows where the effect occurs. -/
def _root_.Zkc.Subject.CapTable.allowanceFrom {V : Vocabulary} (M : Model V)
    (table : CapTable) (place : Nat) (start : List Frame) (op : ROp M) : ℚ≥0 :=
  table.allowedFrom place start (ROp.occurrence M op)

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
  simp [CapTable.allowanceFrom, CapTable.allowedFrom, occurs, Occurrence.siteBelow_append]

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

/-- **An effect at which nothing is excluded costs nothing**: a message got, a value heard, or
a coin whose every reply is followed. -/
theorem charged_free (samplers : Samplers S) (allowance : S.Op → ℚ≥0)
    (allowed : ∀ op, S.Reply op → Prop) (op : S.Op) (next : S.Reply op → ℚ≥0 → Prop)
    (budget : ℚ≥0) (all : ∀ v, allowed op v → next v budget) :
    (ProcessJudgment.charged allowed (paysWithin samplers allowance)).node op next budget :=
  ⟨0, fun _ => False, zero_le, ⟨Or.inl ⟨rfl, fun _ excluded => excluded⟩, zero_le⟩,
    fun v ok _ => by simpa only [tsub_zero] using all v ok⟩

/-- **An effect with a sampler is paid for**: a fee within the budget and within what the
effect is allowed pays for a set of replies of at most the fee's weight under the sampler; the
replies outside the set are followed with what is left of the budget. -/
theorem charged_pay (samplers : Samplers S) (allowance : S.Op → ℚ≥0)
    (allowed : ∀ op, S.Reply op → Prop) (op : S.Op) (next : S.Reply op → ℚ≥0 → Prop)
    (budget fee : ℚ≥0) (excluded : S.Reply op → Prop) (draw : ProbComp (S.Reply op))
    (has : samplers op = some draw) (weight : Pr{let v ← draw}[excluded v] ≤ toProbability fee)
    (within : fee ≤ budget) (cap : fee ≤ allowance op)
    (outside : ∀ v, allowed op v → ¬ excluded v → next v (budget - fee)) :
    (ProcessJudgment.charged allowed (paysWithin samplers allowance)).node op next budget :=
  ⟨fee, excluded, within, ⟨Or.inr ⟨draw, has, weight⟩, cap⟩, outside⟩

end

/-- **A draw of the table is paid within its cap.** At an effect that occurs at the start's path
and a rest, a fee within the budget and within the cap of the draw's site pays for a set of
replies of at most the fee's weight under the sampler; the replies outside the set are followed
with what is left of the budget. The occurrence is read from the effect. -/
theorem charged_pay_at {V : Vocabulary} (M : Model V) (samplers : Samplers (RSig M))
    (table : CapTable) (place : Nat) {start rest : List Frame} {key : Key}
    (allowed : ∀ op, (RSig M).Reply op → Prop) (op : ROp M)
    (next : (RSig M).Reply op → ℚ≥0 → Prop) (budget fee : ℚ≥0)
    (excluded : (RSig M).Reply op → Prop) (draw : ProbComp ((RSig M).Reply op))
    (occurs : ROp.occurrence M op = ⟨start ++ rest, key⟩)
    (has : samplers op = some draw) (weight : Pr{let v ← draw}[excluded v] ≤ toProbability fee)
    (within : fee ≤ budget) (cap : fee ≤ table.capFrom place (Frame.applications rest) key)
    (outside : ∀ v, allowed op v → ¬ excluded v → next v (budget - fee)) :
    (ProcessJudgment.charged allowed
      (paysWithin samplers (table.allowanceFrom M place start))).node op next budget :=
  charged_pay samplers _ allowed op next budget fee excluded draw has weight within
    (by rw [CapTable.allowanceFrom_at M table place start rest key op occurs]; exact cap) outside

end ZkcFormal.Written
