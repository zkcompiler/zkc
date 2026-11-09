module

public import Zkc.Applications.IR.Structured.Generated.Mathematics.TwoSums
public import Zkc.Verification.Bindings.Sumcheck.Table.TableComponentFold
public import Zkc.Program.Source.RegionDerivation
public import Zkc.Applications.IR.Structured.SumcheckSourceSelections

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

noncomputable def targetMeanings : Meanings F G :=
  closedMeanings TwoSumsInputs.imported.program.payload.definitions

def targetFold : FoldSpec := public_sums.callee.fold

theorem target_step (raw : List F) (a value : F) :
    invoke (targetMeanings (G := G)) targetFold.stepHelper
      (.cons a (.cons value (.cons raw .nil))) = .done (.cons (a + value) .nil) := by
  change invoke (targetMeanings (G := G)) public_sums.callee.foldStep.helper _ = _
  erw [public_sums.callee.foldStep.association.invoke TwoSumsInputs.unit.linked]
  simp only [public_sums.callee.foldStep.body, Region.denote, meaning, Evaluation.meaning,
    Evaluation.operation, Operands.eval, Values.get, Regions.denote]
  erw [public_sums.callee.foldStep.calleeDependency0.association.invoke TwoSumsInputs.unit.linked]
  rfl

theorem target_total (raw : List F) (bounded : raw.length < indexLimit) :
    invoke (targetMeanings (G := G)) public_sums.callee.helper (.cons raw .nil) =
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
    invoke (targetMeanings (G := G)) public_sums.helper
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      .done (.cons (decide (left.sum = leftClaim ∧ right.sum = rightClaim)) .nil) := by
  erw [public_sums.association.invoke TwoSumsInputs.unit.linked]
  let model := ringModel F G
  let args : Values (assignment F G) public_sums.helper.inputs :=
    .cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))
  let bindings := SumcheckSourceSelections.outerSumBindings
  let law := ReferenceLibrary.Sum.pairRelation model "bls12-381.fr" bindings
  refine (Evaluation.denote_meaning_eq_meaningOn SiteObservations.closed
    (targetMeanings (G := G)) public_sums.body args.get).trans ?_
  refine (law.valid (targetMeanings (G := G)) args ?_).trans ?_
  · constructor
    · change invoke (targetMeanings (G := G)) public_sums.callee.helper (.cons left .nil) = _
      rw [target_total left leftBound]
      simp [args, ReferenceLibrary.Sum.totalOutcome, leftBound, primitiveOutcome]
    · intro _ _
      change invoke (targetMeanings (G := G)) public_sums.callee.helper (.cons right .nil) = _
      rw [target_total right rightBound]
      simp [args, ReferenceLibrary.Sum.totalOutcome, rightBound, primitiveOutcome]
  · change primitiveOutcome (I := closedInterface) (A := Values (assignment F G) [.boolean]) (if left.length < indexLimit then
      if leftClaim = left.sum then
        if right.length < indexLimit then .returned (.cons (decide (rightClaim = right.sum)) .nil)
        else .stopped .exhausted
      else .returned (.cons false .nil)
    else .stopped .exhausted) = _
    by_cases eqLeft : leftClaim = left.sum <;>
      simp [leftBound, rightBound, eqLeft, eq_comm, primitiveOutcome]

end ZkcSecurity.Examples.Components.TwoSums
