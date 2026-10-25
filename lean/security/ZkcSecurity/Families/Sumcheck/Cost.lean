module

public import ZkcSecurity.Families.Sumcheck.Derivation
public import ZkcSecurity.FiatShamir.Budget
public import Zkc.Transcript.ReturnBudget

@[expose] public section

/-! Resource bounds at the selected history-sensitive ENNReal schedule. A local
escape inequality supplies none of these path bounds. Return-sensitive bind
uses the existing all-typed-replies return reading and the existing cost walk. -/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.Cost
open Zkc.Transcript

variable {I : PIR.Signature} {F : Type} [Field F] [DecidableEq F] {Context : Type} {State : Nat → Type}
  {message : Message F} {program : Program I Context State message}
  {E P : Type} {Raw : E → Type} {absorb : Interface I E P Raw}

/-- Bound the actual charged walk, including any calls in the receive/decoding
stage. Request prices must dominate all reached query prices separately. -/
theorem remaining (queries : QueryInterface program absorb)
    (charge : List E → E → ENNReal) (receiveCost queryCost deliveryCost : ENNReal)
    (receives : ∀ {k} (context : Context) (s : State (k + 1)) history,
      (absorb.walk (absorb.lossCharge charge)).Bound (program.receive context s) history receiveCost)
    (queryPrice : ∀ {k} (context : Context) (s : State (k + 1)) m history,
      charge history (queries.event context s m) ≤ queryCost)
    (deliveries : ∀ {k} (context : Context) (s : State (k + 1)) m r history,
      (absorb.walk (absorb.lossCharge charge)).Bound (program.deliver context s m r) history deliveryCost)
    {n : Nat} (count : Nat) (context : Context) (s : State (n + count)) (history : List E) :
    ZkcSecurity.FiatShamir.Typed.ChargedCostBound absorb charge
      (program.remaining count context s) history (count • (receiveCost + queryCost + deliveryCost)) := by
  apply (ZkcSecurity.FiatShamir.Typed.chargedCostBound_iff absorb charge _ _ _).mpr
  induction count generalizing history with
  | zero => trivial
  | succ count ih =>
      rw [Program.remaining, succ_nsmul']
      have costEq : receiveCost + queryCost + deliveryCost +
          count • (receiveCost + queryCost + deliveryCost) =
          receiveCost + (queryCost + (deliveryCost +
            count • (receiveCost + queryCost + deliveryCost))) := by simp only [add_assoc]
      rw [costEq]
      apply Walk.Bound.bind _ (fun _ => bot_le) _ ?_ _ (receives context s history)
      intro decoded reached
      cases decoded with
      | none => trivial
      | some m =>
          dsimp only
          split
          · refine ⟨trivial, deliveryCost + count • (receiveCost + queryCost + deliveryCost), ?_, ?_⟩
            · simp only [Interface.walk_charge, Interface.lossCharge, queries.absorbed]
              exact add_le_add (queryPrice context s m reached) le_rfl
            · intro reply later _
              apply Walk.Bound.bind _ (fun _ => bot_le) _ ?_ _ (deliveries context s m _ later)
              intro _ next
              exact ih _ next
          · trivial

end ZkcSecurity.Families.Sumcheck.Cost
