module

public import ZkcSecurity.Claims.Endpoint

@[expose] public section

/-! Reusable arithmetic adapters for uniform-rate libraries. These consume
checked mathematical implications to the already requested quantity; they do
not participate in expression resolution or choose any source quantity. -/

set_option autoImplicit false
namespace ZkcSecurity.Claims
open Zkc.Claims Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Endpoint ZkcSecurity.FiatShamir

theorem query_rate_add_cost (queries overhead : Nat) (denominator : ENNReal) :
    (queries : ENNReal) * (1 / denominator) + (overhead : ENNReal) / denominator =
      (queries + overhead : ENNReal) / denominator := by
  simp only [div_eq_mul_inv, one_mul, add_mul]

theorem nnrat_inv_card_value (F : Type) [Fintype F] [Nonempty F] :
    ((1 / (Fintype.card F : ℚ≥0) : ℚ≥0) : ENNReal) = 1 / (Fintype.card F : ENNReal) := by
  rw [← ENNReal.coe_nnratCast]
  simp [ENNReal.coe_inv, Fintype.card_ne_zero]

section
variable {F G : Type} [Field F] [DecidableEq F] [AddCommGroup G] [Module F G] [DecidableEq G]
  [SampleableType F] {art : Artifacts} {endpoint : Semantics} {form : Form}
  {claim : art.Statement F G → Prop}

/-- A uniform family rate and an independent validator bound suffice for an
ordinary scalar query theorem. No charged capability is needed. -/
def BoundImplication.ofConstantRate
    (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F))
    (model : Model) (error : Nat → ENNReal) (rate validatorCost : ENNReal)
    (charge : ∀ history event, evidence.family.charge history event ≤ rate)
    (cost : ∀ statement, evidence.cost statement ≤ validatorCost)
    (requestedCost : ∀ queries, validatorCost ≤ model.validatorCost.value queries)
    (conclusion : ∀ queries, model.queries.allows queries →
      queries * rate + model.validatorCost.value queries ≤ error queries) :
    BoundImplication evidence model error where
  rate _ := rate
  charge _ := charge
  cost queries statement := (cost statement).trans (requestedCost queries)
  conclusion := conclusion

/-- Equal prices permit reusing the family's validator cost proof. Domination
alone is deliberately insufficient: raising prices can raise validator cost. -/
theorem requestedCost_of_equal_charge
    (subject : Subject F G art endpoint) (schedule : ChargeSchedule subject) (queries : Nat)
    (evidence : SoundnessEvidence art endpoint form claim (Regime.exact F)) (cost : ENNReal)
    (same : schedule.charge queries = evidence.family.charge)
    (bounded : ∀ statement, evidence.cost statement ≤ cost) :
    ∀ statement initial, Typed.ChargedCostBound
      (interface (G := G) evidence.compiled.context id) (schedule.charge queries)
      (evidence.compiled.original statement evidence.handle) initial cost := by
  intro statement initial
  rw [same]
  exact chargedCostBound_mono_bound _ _ _ _ _ _ (evidence.costBound statement initial) (bounded statement)

end
end ZkcSecurity.Claims
