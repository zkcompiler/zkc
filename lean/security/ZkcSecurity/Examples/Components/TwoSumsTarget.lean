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
open ZkcSecurity.Families.Sumcheck.TableComponent

structured_associations TwoSumsInputs
  [helper0 := TwoSumsInputs.helper0, helper1 := TwoSumsInputs.helper1,
    helper2 := TwoSumsInputs.helper2, helper3 := TwoSumsInputs.helper3]

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

def targetFold : FoldSpec := sumFold "bls12-381.fr"
  "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_domain"
  "finite_zkl_9d89739f0825e451fe8a58993c7a5d6dc7767d148c154dbd13182e883a66e305_s1_body"

theorem target_step (raw : List F) (a value : F) :
    invoke (helperMeanings (G := G)) targetFold.stepHelper
      (.cons a (.cons value (.cons raw .nil))) = .done (.cons (a + value) .nil) := by
  change invoke (helperMeanings (G := G)) TwoSumsInputs.helper1Helper _ = _
  erw [helper1_association.invoke TwoSumsInputs.unit.linked]
  simp only [TwoSumsInputs.helper1Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [helper0_association.invoke TwoSumsInputs.unit.linked]
  rfl

theorem target_total (raw : List F) (bounded : raw.length < indexLimit) :
    invoke (helperMeanings (G := G)) TwoSumsInputs.helper2Helper (.cons raw .nil) =
      .done (.cons raw.sum .nil) := by
  rw [helper2_association.invoke TwoSumsInputs.unit.linked]
  simp only [TwoSumsInputs.helper2Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push, Nat.cast_zero]
  change (Evaluation.denoteFold _ targetFold
    ((Values.cons raw .nil).append ((Values.cons (0 : F) .nil).append .nil))).bind _ = _
  erw [sumFold_equation _ _ _ _ raw 0 bounded (target_step raw)]
  simp only [zero_add, PIR.Process.bind, Environment.prepend, Environment.push]

/-- Complete Boolean adequacy of the retained actual conjunction formula. -/
theorem target_equation (left right : List F) (leftClaim rightClaim : F)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    invoke (helperMeanings (G := G)) TwoSumsInputs.helper3Helper
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      .done (.cons (decide (left.sum = leftClaim ∧ right.sum = rightClaim)) .nil) := by
  rw [helper3_association.invoke TwoSumsInputs.unit.linked]
  simp only [TwoSumsInputs.helper3Body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  rw [target_total left leftBound]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  erw [target_total right rightBound]
  simp only [PIR.Process.bind, Environment.prepend, Environment.push]
  change (PIR.Process.done (I := closedInterface)
    (Values.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum))
      .nil : Values (assignment F G) [.boolean])) = _
  congr 3
  simp only [Bool.decide_and, eq_comm]

end ZkcSecurity.Examples.Components.TwoSums
