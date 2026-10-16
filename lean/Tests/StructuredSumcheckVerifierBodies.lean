import ZkcExamples.Structured.SumcheckVerifierBodies
import ZkcExamples.Structured.SumcheckReduceLaws
import ZkcExamples.Structured.SumcheckSourceLaws
import Mathlib.Data.ZMod.Basic

/-! Literal associations are checked against both complete originals. The small
mutants below are authored controls, not replacement native captures. -/
namespace Tests.StructuredSumcheckVerifierBodies
open Zkc.Source Zkc.Source.Structured
open ZkcExamples.Structured
open SumcheckVerifierBodies

theorem original_source_maximum_two :
    SumcheckSourceViews.reduceDefinition.raw = (reduceBody 2).erase := by
  refine SumcheckSourceViews.reduce_raw.trans ?_
  have same : SumcheckSourceBodies.reduceBody = reduceBody 2 := by
    unfold reduceBody roundBody roundGuard roundTail reduceReturn
    rfl
  exact congrArg Region.erase same

theorem original_reduction_maximum_four :
    SumcheckReduceViews.reduceDefinition.raw = (reduceBody 4).erase := by
  refine SumcheckReduceViews.reduce_raw.trans ?_
  have same : SumcheckReduceBodies.reduceBody = reduceBody 4 := by
    unfold reduceBody roundBody roundGuard roundTail reduceReturn
    rfl
  exact congrArg Region.erase same

theorem original_return_order :
    (reduceReturn []).erase = .ret [3, 0, 1, 2, 4, 5] := rfl

/-- The verifier point incorrectly selects the absent prover point. -/
def wrongPointReturn : Region protocolDialect repeatState reduceOutputs :=
  .ret (.cons (.there (.there (.there .here))) (.cons .here
    (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there (.there .here))))) .nil))))))

theorem return_mutation_breaks_raw_association :
    wrongPointReturn.erase ≠ (reduceReturn []).erase := by
  intro same
  have : ([3, 0, 1, 2, 3, 5] : List Nat) = [3, 0, 1, 2, 4, 5] := by
    injection same
  contradiction

def verifierState : Values (Component (assignment (ZMod 5) (ZMod 5))) repeatState :=
  .cons none (.cons none (.cons none (.cons none
    (.cons (some [1]) (.cons (some 1) .nil)))))

/-- Distinguish the actual suffix before masking can hide a return permutation. -/
theorem return_mutation_loses_verifier_point :
    wrongPointReturn.denote
        (participantMeaningWith (.silent _) (participantActions (ZMod 5) (ZMod 5))
          ⟨[], []⟩ 1 [] {}) verifierState.get =
      .done (.cons none (.cons none (.cons none (.cons none
        (.cons none (.cons (some 1) .nil)))))) := rfl

theorem original_return_retains_verifier_point :
    (reduceReturn []).denote
        (participantMeaningWith (.silent _) (participantActions (ZMod 5) (ZMod 5))
          ⟨[], []⟩ 1 [] {}) verifierState.get =
      .done (.cons none (.cons none (.cons none (.cons none
        (.cons (some [1]) (.cons (some 1) .nil)))))) := rfl

/-- Same input/output ABI; only the actual append value changes. -/
def zeroAppendBody : Region dialect SumcheckHelperBodies.appendHelper.inputs
    SumcheckHelperBodies.appendHelper.outputs :=
  .letOp (.fieldConstant "bls12-381.fr" 0) .nil .nil <|
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.exec (.vectorAppend "bls12-381.fr"))
    (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

theorem append_mutation_breaks_raw_association :
    SumcheckSourceViews.appendDefinition.raw ≠ zeroAppendBody.erase := by
  intro same
  have operations := congrArg RawRegion.operations same
  have first := congrArg List.head? operations
  change some (Op.mark "s0") = some (.fieldConstant "bls12-381.fr" 0) at first
  cases Option.some.inj first

theorem append_mutation_distinguishes_nonzero_challenge :
    zeroAppendBody.denote
        (Evaluation.meaning (F := ZMod 5) (G := ZMod 5) SiteObservations.closed [])
        (Values.cons ([] : List (ZMod 5)) (.cons 1 .nil)).get =
      .done (.cons [0] .nil) := rfl

end Tests.StructuredSumcheckVerifierBodies
