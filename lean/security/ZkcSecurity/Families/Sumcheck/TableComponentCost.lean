module

public import ZkcSecurity.Families.Sumcheck.TableComponentRoots

@[expose] public section

/-! Actual query budgets for complete table roots and source-order composition.
Escape prices and pathwise resource bounds remain separate obligations.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent
open Zkc.Transcript ZkcSecurity.FiatShamir

variable {F : Type} [Field F] [DecidableEq F]
  {I : PIR.Signature} {Context : Type} {State : Nat → Type}
  {program : Program I Context State (Message.endpoints F)}
  {E P : Type} {Raw : E → Type} {absorb : Interface I E P Raw}

/-- Cost includes the actual receive stage and every reached query. Terminal
algebra contributes no oracle queries in this selected presentation. -/
theorem root_cost (layout : Layout program) (queries : QueryInterface program absorb)
    (charge : List E → E → ENNReal) (receiveCost queryCost deliveryCost : ENNReal)
    (receives : ∀ {k} (context : Context) (s : State (k + 1)) history,
      (absorb.walk (absorb.lossCharge charge)).Bound (program.receive context s) history receiveCost)
    (queryPrice : ∀ {k} (context : Context) (s : State (k + 1)) m history,
      charge history (queries.event context s m) ≤ queryCost)
    (deliveries : ∀ {k} (context : Context) (s : State (k + 1)) m r history,
      (absorb.walk (absorb.lossCharge charge)).Bound (program.deliver context s m r) history deliveryCost)
    (count : Nat) (context : Context) (s : State (0 + count)) (history : List E) :
    Typed.ChargedCostBound absorb charge (root layout count context s) history
      (count • (receiveCost + queryCost + deliveryCost)) := by
  apply (Typed.chargedCostBound_iff absorb charge _ _ _).mpr
  have rounds := (Typed.chargedCostBound_iff absorb charge _ _ _).mp
    (Cost.remaining queries charge receiveCost queryCost deliveryCost receives queryPrice
      deliveries count context s history)
  simpa only [add_zero, root] using Walk.Bound.bind
    (absorb.walk (absorb.lossCharge charge)) (fun _ => bot_le)
    (terminal layout) (second := 0) (by intro _ _; trivial) _ rounds

/-- The full sequential budget counts both children at the request's prices,
without an independence or challenge-sharing assumption. -/
theorem twoRoots_cost (layout : Layout program)
    (charge : List E → E → ENNReal)
    (leftCount rightCount : Nat) (leftContext rightContext : Context)
    (left : State (0 + leftCount)) (right : State (0 + rightCount))
    (leftBudget rightBudget : ENNReal)
    (first : ∀ history, Typed.ChargedCostBound absorb charge
      (root layout leftCount leftContext left) history leftBudget)
    (second : ∀ history, Typed.ChargedCostBound absorb charge
      (root layout rightCount rightContext right) history rightBudget)
    (history : List E) :
    Typed.ChargedCostBound absorb charge
      (twoRoots layout leftCount rightCount leftContext rightContext left right) history
      (leftBudget + rightBudget) := by
  apply (Typed.chargedCostBound_iff absorb charge _ _ _).mpr
  apply Walk.Bound.bind (absorb.walk (absorb.lossCharge charge)) (fun _ => bot_le)
  · intro leftAccepted reached
    have bound := (Typed.chargedCostBound_iff absorb charge _ _ _).mp (second reached)
    simpa only [add_zero] using Walk.Bound.bind
      (absorb.walk (absorb.lossCharge charge)) (fun _ => bot_le)
      (fun rightAccepted => PIR.Process.done (leftAccepted && rightAccepted))
      (second := 0) (by intro _ _; trivial) _ bound
  · exact (Typed.chargedCostBound_iff absorb charge _ _ _).mp (first history)

end ZkcSecurity.Families.Sumcheck.TableComponent
