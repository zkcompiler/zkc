module

public import Zkc.Formal.Application
public import Zkc.Formal.Written.SiteCaps
public import Zkc.Formal.Written.LawSamplers
public import Zkc.Formal.WalkLabels

@[expose] public section

/-!
The judgment with fees of a written goal reads no peer.

What the world may give (`Permitted`), the samplers of the laws (`lawSamplers`) and what a
table of caps allows an effect (`CapTable.allowanceFrom`, which reads where the effect occurs)
do not read who gives, gets, hears or owns. So the judgment in which the statements of a goal
are made is `Blind`, and a walk goes into an application under it. So are the judgments "on
every permitted reply" and "on some permitted reply", in which a text states what a role
returns. The theorems carry the label `walk_blind`, by which the walk finds that a judgment
reads no peer. The judgment that records the trace of a run (`ProcessJudgment.trace`) reads the
peers, and is not among them.
-/

namespace Zkc.Formal.Written
open Core ProbabilisticProcess OracleComp
open Frontend.Written (CapTable)
open scoped NNRat ENNReal

variable {V : Vocabulary} {M : Model V}

/-- Where an effect occurs does not change with its peers. -/
theorem occurrence_renameOp (ρ : Role → Role) (op : ROp M) :
    ROp.occurrence M (renameOp ρ op) = ROp.occurrence M op := by
  cases op <;> rfl

/-- The judgment with fees reads no peer when what it allows and what it calls small read none. -/
theorem charged_blind (ρ : Role → Role) (allowed : ∀ op, (RSig M).Reply op → Prop)
    (small : (op : ROp M) → ℚ≥0 → ((RSig M).Reply op → Prop) → Prop)
    (hAllowed : ∀ op, allowed (renameOp ρ op) = carryReply ρ op (allowed op))
    (hSmall : ∀ op fee bad, small (renameOp ρ op) fee (carryReply ρ op bad) ↔ small op fee bad) :
    Blind ρ (.charged allowed small) := by
  intro op next
  funext budget
  have ha := hAllowed op
  have hs := hSmall op
  cases op <;> simp only [renameOp, carryReply] at ha hs ⊢ <;>
    simp only [ProcessJudgment.charged, ha, hs]

/-- What the world may give reads no peer. -/
theorem permitted_blind (ρ : Role → Role) :
    ∀ op : ROp M, Permitted M (renameOp ρ op) = carryReply ρ op (Permitted M op) := by
  intro op; cases op <;> rfl

/-- Fees of the samplers of the laws within the allowances of a table read no peer. -/
theorem paysWithin_blind (ρ : Role → Role) (draws : LawDraws M) (table : CapTable) (place : Nat)
    (start : List Frame) :
    ∀ (op : ROp M) fee bad,
      paysWithin (lawSamplers M draws) (table.allowanceFrom M place start) (renameOp ρ op) fee
          (carryReply ρ op bad) ↔
        paysWithin (lawSamplers M draws) (table.allowanceFrom M place start) op fee bad := by
  intro op fee bad
  have allowance : table.allowanceFrom M place start (renameOp ρ op) =
      table.allowanceFrom M place start op := by
    simp only [CapTable.allowanceFrom, occurrence_renameOp]
  unfold paysWithin
  rw [allowance]
  cases op with
  | own kind => cases kind <;> exact Iff.rfl
  | _ => exact Iff.rfl

/-- The judgment "on every permitted reply" reads no peer when what is permitted reads none. -/
theorem every_blind (ρ : Role → Role) (allowed : ∀ op, (RSig M).Reply op → Prop)
    (hAllowed : ∀ op, allowed (renameOp ρ op) = carryReply ρ op (allowed op)) :
    Blind ρ (.every allowed) := by
  intro op next
  have ha := hAllowed op
  cases op <;> simp only [renameOp, carryReply] at ha ⊢ <;> simp only [ProcessJudgment.every, ha]

/-- The judgment "on some permitted reply" reads no peer when what is permitted reads none. -/
theorem possible_blind (ρ : Role → Role) (allowed : ∀ op, (RSig M).Reply op → Prop)
    (hAllowed : ∀ op, allowed (renameOp ρ op) = carryReply ρ op (allowed op)) :
    Blind ρ (.possible allowed) := by
  intro op next
  have ha := hAllowed op
  cases op <;> simp only [renameOp, carryReply] at ha ⊢ <;> simp only [ProcessJudgment.possible, ha]

/-- **Every permitted reply**: the judgment in which a text states that a role returns on every
run, at what the world may give, reads no peer. -/
@[walk_blind]
theorem every_permitted_blind (ρ : Role → Role) : Blind (M := M) ρ (.every (Permitted M)) :=
  every_blind ρ _ (permitted_blind ρ)

/-- **Some permitted reply**: the judgment in which a text states that a role can return reads
no peer. -/
@[walk_blind]
theorem possible_permitted_blind (ρ : Role → Role) : Blind (M := M) ρ (.possible (Permitted M)) :=
  possible_blind ρ _ (permitted_blind ρ)

/-- **The judgment of a written goal reads no peer.** -/
@[walk_blind]
theorem judgment_blind (ρ : Role → Role) (draws : LawDraws M) (table : CapTable) (place : Nat)
    (start : List Frame) :
    Blind ρ (.charged (Permitted M)
      (paysWithin (lawSamplers M draws) (table.allowanceFrom M place start))) :=
  charged_blind ρ _ _ (permitted_blind ρ) (paysWithin_blind ρ draws table place start)

end Zkc.Formal.Written
