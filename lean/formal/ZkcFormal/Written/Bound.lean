module

public import Zkc.Subject.Bound
public import Mathlib.Basic.ENNReal.Inv

@[expose] public section
set_option autoImplicit false

/-! The one spelling of a goal's bound as a probability: its numerator over its positive
denominator, in `ℝ≥0∞`. A property that bounds a probability reads a `Bound` through `limit`. -/

namespace Zkc.Subject
open scoped ENNReal

/-- A bound as a probability. -/
noncomputable def Bound.limit (b : Bound) : ℝ≥0∞ := (b.numerator : ℝ≥0∞) / (b.denominator : ℝ≥0∞)

/-- A bound is a finite number: its denominator is positive. -/
theorem Bound.limit_lt_top (b : Bound) : b.limit < ∞ :=
  ENNReal.div_lt_top (ENNReal.natCast_ne_top _) (by exact_mod_cast b.positive.ne')

end Zkc.Subject
