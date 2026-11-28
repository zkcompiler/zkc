module

public import ZkcFormal.Application
public import ZkcFormal.Written.SiteCaps
public import ZkcFormal.Written.LawSamplers

@[expose] public section

/-!
The judgment with fees of a written goal reads no peer.

The judgment by fees (`Fees.judgment`) is the judgment with fees at what the world may give
(`Permitted`), the samplers of the laws (`lawSamplers`) and an allowance of occurrences: what
each occurrence of an effect may be charged at most (a table of caps gives one,
`CapTable.allowed`). None of the three reads who gives, gets, hears or owns. So the judgment
in which the statements of a goal are made is blind. The judgment that records the trace of a run (`ProcessJudgment.trace`) reads the peers, and is
not among them: under it the goal in a callee is stated under `ProcessJudgment.renamed`.
-/

namespace ZkcFormal.Written
open Zkc.Core ProbabilisticProcess OracleComp
open Zkc.Subject (CapTable)
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

/-- **The judgment by fees over an allowance of occurrences.** What the world may give is
permitted; a fee is a fee of the samplers of the laws, and is at most what the allowance gives
where the effect occurs. An allowance bounds the fee of one occurrence; the budget, which the
judgment carries along a run, bounds their sum. -/
def Fees.judgment (draws : LawDraws M) (allowance : Occurrence → ℚ≥0) :
    ProcessJudgment (RSig M) (ℚ≥0 → Prop) :=
  .charged (Permitted M) (paysWithin (lawSamplers M draws) fun op => allowance (ROp.occurrence M op))

theorem Fees.judgment_monotone (draws : LawDraws M) (allowance : Occurrence → ℚ≥0) :
    (Fees.judgment draws allowance).Monotone :=
  ProcessJudgment.charged_mono _ _

/-- Fees of the samplers of the laws within an allowance of occurrences read no peer. -/
theorem paysWithin_blind (ρ : Role → Role) (draws : LawDraws M) (allowance : Occurrence → ℚ≥0) :
    ∀ (op : ROp M) fee bad,
      paysWithin (lawSamplers M draws) (fun op => allowance (ROp.occurrence M op)) (renameOp ρ op)
          fee (carryReply ρ op bad) ↔
        paysWithin (lawSamplers M draws) (fun op => allowance (ROp.occurrence M op)) op fee bad := by
  intro op fee bad
  unfold paysWithin
  simp only [occurrence_renameOp]
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
theorem every_permitted_blind (ρ : Role → Role) : Blind (M := M) ρ (.every (Permitted M)) :=
  every_blind ρ _ (permitted_blind ρ)

/-- **Some permitted reply**: the judgment in which a text states that a role can return reads
no peer. -/
theorem possible_permitted_blind (ρ : Role → Role) : Blind (M := M) ρ (.possible (Permitted M)) :=
  possible_blind ρ _ (permitted_blind ρ)

/-- **The judgment by fees reads no peer**, at every allowance of occurrences. -/
theorem Fees.judgment_blind (ρ : Role → Role) (draws : LawDraws M) (allowance : Occurrence → ℚ≥0) :
    Blind ρ (Fees.judgment draws allowance) :=
  charged_blind ρ _ _ (permitted_blind ρ) (paysWithin_blind ρ draws allowance)

end ZkcFormal.Written
