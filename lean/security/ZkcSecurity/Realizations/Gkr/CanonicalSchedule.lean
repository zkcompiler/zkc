module

public import ZkcSecurity.Claims.CompiledSoundness
public import ZkcSecurity.Realizations.Gkr.Generated.Subject

@[expose] public section

/-! The four actual source-selected charge sites share the proved degree-four
price. The pathwise source cost and adaptive adversary queries are explicit. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalSchedule
open Zkc.Source.Structured Zkc.Construction
open ZkcSecurity ZkcSecurity.Claims ZkcSecurity.Obligations
open Generated.Subject
abbrev Scalar := ZMod blsModulus

def price : ENNReal := 4 / (Fintype.card Scalar : ENNReal)
def priceBound : Claims.Bound := .div (.constant 4) (Fintype.card Scalar : ℚ≥0)
theorem priceBound_value (queries : Nat) : priceBound.value queries = price := by
  simp only [priceBound, Claims.Bound.value, ennreal_nnrat_natural, price]
  norm_num

def schedule : Domain.ChargeSchedule validatorSubject :=
  CompiledSoundness.uniformSchedule validatorSubject priceBound
    (by decide +kernel) (by decide +kernel)

theorem schedule_prices (queries : Nat) :
    ∀ entry ∈ schedule.entries, entry.2.value queries = price := by
  intro entry member
  exact (CompiledSoundness.uniformSchedule_prices priceBound _ _ queries entry member).trans
    (priceBound_value queries)

def validatorCost (_queries : Nat) : ENNReal := 40 * price
def scalarBound (queries : Nat) : ENNReal :=
  4 * ((queries : ENNReal) + 40) / (Fintype.card Scalar : ENNReal)

theorem scalar_bound (queries : Nat) :
    (queries : ENNReal) * schedule.maximum queries + validatorCost queries ≤ scalarBound queries := by
  rw [CompiledSoundness.maximum_constant schedule queries price (by decide +kernel) (schedule_prices queries)]
  simp only [validatorCost, scalarBound, price, div_eq_mul_inv]
  exact le_of_eq (by ring)

end ZkcSecurity.Realizations.Gkr.CanonicalSchedule
