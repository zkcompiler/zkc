import Zkc.Relation.AIR
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation

set_option autoImplicit false

namespace Tests.RelationAIR

open Zkc.Relation.AIR

private def step : Expr (ZMod 101) 2 1 :=
  .add (.read 1 0) (.mul (.constant (-1)) (.add (.read 0 0) (.constant 1)))

private def boundary (j : Fin 2) : Expr (ZMod 101) 2 1 :=
  .add (.read 0 0) (.mul (.constant (-1)) (.publicInput j))

private def transition : Constraint (ZMod 101) 2 1 := ⟨.transition 1, step⟩
private def first : Constraint (ZMod 101) 2 1 := ⟨.first, boundary 0⟩
private def last : Constraint (ZMod 101) 2 1 := ⟨.last, boundary 1⟩
private def trace : Fin 3 → Fin 1 → ZMod 101 := fun i _ => (![3, 4, 5] : Fin 3 → ZMod 101) i
private def statement : Fin 2 → ZMod 101 := ![3, 5]

example : step.maxOffset = 1 ∧ step.degree = 1 ∧ step.reads = [(1, 0), (0, 0)] := by decide
example : step.evaluateAt statement trace 0 = some 0 := by decide
example : step.evaluateAt statement trace 1 = some 0 := by decide
example : step.evaluateAt statement trace 2 = none := by decide

example : transition.Holds statement trace := by
  unfold Constraint.Holds
  decide

example : first.Holds statement trace ∧ last.Holds statement trace := by
  unfold Constraint.Holds
  decide

-- The same transition expression applied everywhere must refuse the final read.
example : ¬ (⟨.every, step⟩ : Constraint (ZMod 101) 2 1).Holds statement trace := by
  unfold Constraint.Holds
  decide

-- A missing final boundary leaves the output unrelated to the declared statement.
example : transition.Holds (![3, 6] : Fin 2 → ZMod 101) trace ∧
    first.Holds (![3, 6] : Fin 2 → ZMod 101) trace ∧
    ¬ last.Holds (![3, 6] : Fin 2 → ZMod 101) trace := by
  unfold Constraint.Holds
  decide

example : (family [first, transition, last] 2).holds statement trace := by
  change ∀ constraint ∈ [first, transition, last], constraint.Holds statement trace
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  intro constraint h
  rcases h with rfl | rfl | rfl <;> unfold Constraint.Holds <;> decide

example : Scope.first.Active (0 : Fin 1) ∧ Scope.last.Active (0 : Fin 1) ∧
    ¬ (Scope.transition 1).Active (0 : Fin 1) := by decide

-- An incorrect declared lookahead cannot make an out-of-range read succeed.
example : ¬ (⟨.transition 0, step⟩ : Constraint (ZMod 101) 2 1).Holds statement trace := by
  unfold Constraint.Holds
  decide

-- Degree is a proved upper bound on interpreted polynomials, not a field hint.
example (read : Nat × Fin 1 → Polynomial (ZMod 101)) (D : Nat)
    (h : ∀ r ∈ step.reads, (read r).natDegree ≤ D) :
    (step.polynomial statement read).natDegree ≤ D := by
  simpa [step, Expr.degree] using step.polynomial_degree statement read D h

example : (Expr.mul step step).degree = 2 := by decide

end Tests.RelationAIR
