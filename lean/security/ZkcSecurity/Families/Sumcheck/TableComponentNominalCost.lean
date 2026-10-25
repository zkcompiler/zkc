module

public import ZkcSecurity.Families.Sumcheck.TableComponentFrame
public import ZkcSecurity.Families.Sumcheck.TableComponentCost

@[expose] public section

/-! Query costs of the nominal table component. Receiving both unrestricted
endpoints and delivering the challenge have zero oracle charge. Every reached
challenge is charged at the selected history, including repeated ROM keys.
-/

set_option autoImplicit false
namespace ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
open Zkc.Source Zkc.Construction Zkc.Transcript ZkcSecurity.FiatShamir

variable {F G Frame : Type} [Field F] [DecidableEq F]

omit [DecidableEq F] in
theorem receive_cost (field : String) (update : FrameUpdate F Frame field)
    (charge : Domain.History (Structured.uniformCarriers F G) →
      Domain.Event (Structured.uniformCarriers F G) → ENNReal)
    {n : Nat} (schedule : Schedule field) (state : PrefixState F Frame (n + 1))
    (history : Domain.History (Structured.uniformCarriers F G)) :
    ((interface field).walk ((interface field).lossCharge charge)).Bound
      ((programWithFrame field update).receive schedule state) history 0 := by
  refine ⟨trivial, 0, ?_, ?_⟩
  · simp [Interface.walk_charge, Interface.lossCharge, interface]
  · intro low reached _
    refine ⟨trivial, 0, ?_, ?_⟩
    · simp [Interface.walk_charge, Interface.lossCharge, interface]
    · intro high final _
      trivial

omit [DecidableEq F] in
theorem delivery_cost (field : String) (update : FrameUpdate F Frame field)
    (charge : Domain.History (Structured.uniformCarriers F G) →
      Domain.Event (Structured.uniformCarriers F G) → ENNReal)
    {n : Nat} (schedule : Schedule field) (state : PrefixState F Frame (n + 1))
    (message : F × F) (challenge : F)
    (history : Domain.History (Structured.uniformCarriers F G)) :
    ((interface field).walk ((interface field).lossCharge charge)).Bound
      ((programWithFrame field update).deliver schedule state message challenge) history 0 := by
  refine ⟨trivial, 0, ?_, ?_⟩
  · simp [Interface.walk_charge, Interface.lossCharge, interface]
  · intro reply reached _
    trivial

/-- This is a pathwise charged bound, independent of the truth of the scalar
claim and of whether any reply is honest. -/
theorem root_chargedCost (field : String) (update : FrameUpdate F Frame field)
    (charge : Domain.History (Structured.uniformCarriers F G) →
      Domain.Event (Structured.uniformCarriers F G) → ENNReal)
    (price : ENNReal)
    (priced : ∀ history origin, charge history (.challenge origin) ≤ price)
    (count : Nat) (schedule : Schedule field) (state : PrefixState F Frame (0 + count))
    (history : Domain.History (Structured.uniformCarriers F G)) :
    Typed.ChargedCostBound (interface field) charge
      (root (layoutWithFrame field update) count schedule state) history (count • price) := by
  simpa only [zero_add, add_zero] using root_cost (layoutWithFrame field update)
    (queriesWithFrame field update) charge 0 price 0
    (fun context state history => receive_cost field update charge context state history)
    (fun context state message history => priced history (context.query state.point.length))
    (fun context state message challenge history =>
      delivery_cost field update charge context state message challenge history)
    count schedule state history

end ZkcSecurity.Families.Sumcheck.TableComponent.Nominal
