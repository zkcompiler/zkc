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
are made is `Blind`, and a walk goes into an application under it. The theorems carry the label
`walk_blind`, by which the walk finds that a judgment reads no peer.
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

/-- **The judgment of a written goal reads no peer.** -/
@[walk_blind]
theorem judgment_blind (ρ : Role → Role) (draws : LawDraws M) (table : CapTable) (place : Nat)
    (start : List Frame) :
    Blind ρ (.charged (Permitted M)
      (paysWithin (lawSamplers M draws) (table.allowanceFrom M place start))) :=
  charged_blind ρ _ _ (permitted_blind ρ) (paysWithin_blind ρ draws table place start)

end Zkc.Formal.Written
