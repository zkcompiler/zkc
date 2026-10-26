module

public import ZkcSecurity.Examples.Components.TwoSumsHelpers
public import ZkcSecurity.Families.Sumcheck.TableComponentFold
public import Zkc.Source.RegionDerivation

@[expose] public section

/-! The actual source-owned BothSums formula, with its complete checked finite
sum bodies. This equation states both sums; it assumes neither target truth
nor an honest protocol transcript.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.TwoSums
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcExamples.Structured.Generated.Bindings
open ZkcExamples.Structured.Generated.Mathematics.TwoSums
open ZkcSecurity.Families.Sumcheck.TableComponent

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def targetFold : FoldSpec := public_sums.callee.fold

theorem target_step (raw : List F) (a value : F) :
    invoke (helperMeanings (G := G)) targetFold.stepHelper
      (.cons a (.cons value (.cons raw .nil))) = .done (.cons (a + value) .nil) := by
  change invoke (helperMeanings (G := G)) public_sums.callee.foldStep.helper _ = _
  erw [public_sums.callee.foldStep.association.invoke TwoSumsInputs.unit.linked]
  simp only [public_sums.callee.foldStep.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [public_sums.callee.foldStep.calleeDependency0.association.invoke TwoSumsInputs.unit.linked]
  rfl

theorem target_total (raw : List F) (bounded : raw.length < indexLimit) :
    invoke (helperMeanings (G := G)) public_sums.callee.helper (.cons raw .nil) =
      .done (.cons raw.sum .nil) := by
  erw [public_sums.callee.association.invoke TwoSumsInputs.unit.linked]
  simp only [public_sums.callee.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push, Nat.cast_zero]
  change (Evaluation.denoteFold _ targetFold
    ((Values.cons raw .nil).append ((Values.cons (0 : F) .nil).append .nil))).bind _ = _
  erw [sumFold_equation _ _ _ _ raw 0 bounded (target_step raw)]
  simp only [zero_add, PIR.Process.bind, Environment.prepend, Environment.push]

/-- Complete Boolean adequacy of the retained actual conjunction formula. -/
theorem target_equation (left right : List F) (leftClaim rightClaim : F)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    invoke (helperMeanings (G := G)) public_sums.helper
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      .done (.cons (decide (left.sum = leftClaim ∧ right.sum = rightClaim)) .nil) := by
  erw [public_sums.association.invoke TwoSumsInputs.unit.linked]
  simp only [public_sums.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  rw [target_total left leftBound]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  erw [target_total right rightBound]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  change (PIR.Process.done (I := closedInterface)
    (Values.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum))
      .nil : Values (assignment F G) [.boolean])) = _
  simp only [← Bool.decide_and, eq_comm]

end ZkcSecurity.Examples.Components.TwoSums
