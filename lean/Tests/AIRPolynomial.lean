import Zkc.Relation.AIR.Polynomial
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

namespace Tests.AIRPolynomial

open Zkc.Relation.AIR Polynomial

private abbrev F := ZMod 17
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

private def point (row : Fin 4) : F := (4 : F) ^ row.val
private def trace (row : Fin 4) (_ : Fin 1) : F := point row
private def step : Constraint F 0 1 :=
  ⟨.transition 1, .add (.read 1 0) (.mul (.constant (-4)) (.read 0 0))⟩

example : Function.Injective point := by decide

-- This consumer uses the actual multiplicative-read theorem, not an assumed
-- equality between the source and polynomial predicates.
example : step.Holds (fun i => Fin.elim0 i) trace ↔
    vanishing (activeRows step.scope 4) point ∣
      step.expression.polynomial (fun i => Fin.elim0 i)
        (fun read => (X : Polynomial F).comp (C ((4 : F) ^ read.1) * X)) := by
  apply step.holds_iff_shifted_divisibility _ trace 4 (fun _ => X)
  · decide
  · intro row column
    simp [trace, point]
  · intro row active
    exact transition_window_fits _ 1 (by decide) row active

example : step.Holds (fun i => Fin.elim0 i) trace := by
  unfold Constraint.Holds
  decide

-- The same offset expression on all rows remains illegal at the final row.
example : ¬ (⟨.every, step.expression⟩ : Constraint F 0 1).Holds
    (fun i => Fin.elim0 i) trace := by
  unfold Constraint.Holds
  decide

-- Empty active sets do not accidentally demand a nonempty quotient domain.
example (q : Polynomial F) : vanishing (∅ : Finset (Fin 1)) (fun _ => (1 : F)) ∣ q := by
  simp [vanishing]

example (q : Polynomial F) (rows : Finset (Fin 4)) :
    q * vanishing rows point ∣ (X + 1) * vanishing rows point ↔ q ∣ X + 1 :=
  selector_divisibility _ _ _ (vanishing_monic _ _).ne_zero

end Tests.AIRPolynomial
