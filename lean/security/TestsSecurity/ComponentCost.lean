module

public import ZkcSecurity.Tools.ComponentCost

@[expose] public section

/-! Composition is independent of Sumcheck and of the installed component's
representation. Bounds must cover every actual continuation history. -/
set_option autoImplicit false
namespace TestsSecurity.ComponentCost
open Zkc.Transcript ZkcSecurity.FiatShamir
variable {I : PIR.Signature} {E P A B : Type} {Raw : E → Type}
  (absorb : Interface I E P Raw) (charge : List E → E → ENNReal)
  (head : PIR.Process I A) (next : A → PIR.Process I B)
  (history : List E) (price : ENNReal)
  (headBound : Typed.ChargedCostBound absorb charge head history (2 • price))
  (nextBound : ∀ value reached,
    Typed.ChargedCostBound absorb charge (next value) reached (3 • price))

include headBound in
theorem installed : Typed.ChargedCostBound absorb charge head history (2 • price) := by
  derive_component_cost [headBound] unfolding []

include headBound nextBound

theorem sequential : Typed.ChargedCostBound absorb charge
    (head.bind next) history (5 • price) := by
  derive_component_cost [headBound, nextBound] unfolding []

theorem guarded (condition : Prop) [Decidable condition] :
    Typed.ChargedCostBound absorb charge
      (if condition then head.bind next else .halt .refused) history (5 • price) := by
  derive_component_cost [headBound, nextBound] unfolding []

/-- The same supplied component bounds do not justify a smaller sum, and
omitting the continuation theorem cannot silently discard its cost. -/
theorem controls : Typed.ChargedCostBound absorb charge
    (head.bind next) history (5 • price) := by
  fail_if_success
    have : Typed.ChargedCostBound absorb charge (head.bind next) history (4 • price) := by
      derive_component_cost [headBound, nextBound] unfolding []
  fail_if_success
    have : Typed.ChargedCostBound absorb charge (head.bind next) history (5 • price) := by
      derive_component_cost [headBound] unfolding []
  derive_component_cost [headBound, nextBound] unfolding []

/-- An independent caller goal remains visible after the cost tactic closes
its own goal. -/
theorem pending_goal : Typed.ChargedCostBound absorb charge
    (head.bind next) history (5 • price) ∧ True := by
  constructor
  derive_component_cost [headBound, nextBound] unfolding []
  trivial

#print axioms installed
#print axioms sequential
#print axioms guarded
#print axioms controls
#print axioms pending_goal
end TestsSecurity.ComponentCost
