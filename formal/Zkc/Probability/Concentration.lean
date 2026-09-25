import Mathlib.Data.ENNReal.BigOperators

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace Zkc.Probability
open scoped ENNReal BigOperators
/-- An event with finitely many members inherits a cardinality-times-point-mass cap.
This algebraic inequality alone asserts neither normalization nor independence. -/
theorem finite_event_bound {D : Type} [Fintype D] (mass : D → ℝ≥0∞)
    (event : D → Prop) [DecidablePred event] (ε : ℝ≥0∞)
    (cap : ∀ d, mass d ≤ ε) :
    (∑ d ∈ Finset.univ.filter event, mass d) ≤
      ((Finset.univ.filter event).card : ℝ≥0∞) * ε := by
  calc
    _ ≤ ∑ _d ∈ Finset.univ.filter event, ε := Finset.sum_le_sum (fun d _ => cap d)
    _ = _ := by simp

end Zkc.Probability
