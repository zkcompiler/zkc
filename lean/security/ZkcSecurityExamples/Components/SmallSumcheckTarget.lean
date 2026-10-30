module

public import ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck
public import ZkcSecurity.Bindings.Sumcheck.Table.TableComponentFold
public import Zkc.Source.RegionDerivation

@[expose] public section

/-! The actual source-owned public sum formula, with its complete checked finite
sum bodies. This equation states the original table sum; it assumes neither target truth
nor an honest protocol transcript.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.SmallSumcheck
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
open ZkcExamples.Structured.Generated.Bindings
open ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck
open ZkcSecurity.Families.Sumcheck.TableComponent

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

noncomputable def targetMeanings : Meanings F G :=
  closedMeanings SmallSumcheckInputs.imported.program.payload.definitions

def targetFold : FoldSpec := public_sum.callee.fold

theorem target_step (raw : List F) (a value : F) :
    invoke (targetMeanings (G := G)) targetFold.stepHelper
      (.cons a (.cons value (.cons raw .nil))) = .done (.cons (a + value) .nil) := by
  change invoke (targetMeanings (G := G)) public_sum.callee.foldStep.helper _ = _
  erw [public_sum.callee.foldStep.association.invoke SmallSumcheckInputs.unit.linked]
  simp only [public_sum.callee.foldStep.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [public_sum.callee.foldStep.calleeDependency0.association.invoke SmallSumcheckInputs.unit.linked]
  rfl

theorem target_total (raw : List F) (bounded : raw.length < indexLimit) :
    invoke (targetMeanings (G := G)) public_sum.callee.helper (.cons raw .nil) =
      .done (.cons raw.sum .nil) := by
  erw [public_sum.callee.association.invoke SmallSumcheckInputs.unit.linked]
  simp only [public_sum.callee.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote,
    PIR.Process.bind, Environment.prepend, Environment.push, Nat.cast_zero]
  change (Evaluation.denoteFold _ targetFold
    ((Values.cons raw .nil).append ((Values.cons (0 : F) .nil).append .nil))).bind _ = _
  erw [sumFold_equation _ _ _ _ raw 0 bounded (target_step raw)]
  simp only [zero_add, PIR.Process.bind, Environment.prepend, Environment.push]

/-- The retained scalar claim is the sum of its fixed original table. -/
theorem target_equation (raw : List F) (claim : F) (bounded : raw.length < indexLimit) :
    invoke (targetMeanings (G := G)) public_sum.helper (.cons raw (.cons claim .nil)) =
      .done (.cons (decide (claim = raw.sum)) .nil) := by
  erw [public_sum.association.invoke SmallSumcheckInputs.unit.linked]
  simp only [public_sum.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [target_total raw bounded]
  rfl

end ZkcSecurity.Examples.Components.SmallSumcheck
