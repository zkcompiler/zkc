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

end ZkcSecurity.Families.Sumcheck.TableComponent
