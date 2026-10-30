import Zkc.Protocols.Sumcheck.Source.VerifierBodies
import ZkcExamples.Structured.SumcheckReduceLaws
import ZkcExamples.Structured.SumcheckSourceLaws
import ZkcExamples.Structured.SumcheckSourceVerifier
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
    unfold reduceBody roundBody reduceReturn
    rfl
  exact congrArg Region.erase same

theorem original_reduction_maximum_four :
    SumcheckReduceViews.reduceDefinition.raw = (reduceBody 4).erase := by
  refine SumcheckReduceViews.reduce_raw.trans ?_
  have same : SumcheckReduceBodies.reduceBody = reduceBody 4 := by
    unfold reduceBody roundBody reduceReturn
    rfl
  exact congrArg Region.erase same

/-- Admission includes the new Math input formula alongside every original helper. -/
theorem original_input_shape :
    SumcheckSourceViews.inputShapeDefinition.helper = SumcheckRelationContract.shapeHelper ∧
      SumcheckSourceViews.inputShapeDefinition.raw = SumcheckRelationContract.shapeBody.erase ∧
      SumcheckSourceViews.unit.definitions.length = 34 :=
  ⟨rfl, SumcheckSourceViews.inputShape_raw, rfl⟩

/-- Keeping the power equation while dropping the maximum changes the actual formula. -/
def shapeWithoutMaximum : Region dialect SumcheckRelationContract.shapeHelper.inputs
    SumcheckRelationContract.shapeHelper.outputs :=
  .letOp (.vectorLength "bls12-381.fr") (.cons .here .nil) .nil <|
  .letOp .indexPowerOfTwo (.cons .here (.cons (.there (.there .here)) .nil)) .nil <|
  .ret (.cons .here .nil)

theorem omitted_maximum_breaks_shape_association :
    SumcheckSourceViews.inputShapeDefinition.raw ≠ shapeWithoutMaximum.erase := by
  intro same
  have lengths := congrArg (fun body => body.operations.length) same
  change 7 = 2 at lengths
  contradiction

theorem original_return_consumes_pending :
    ProtocolOp.localCall SumcheckPendingBodies.atPrefixHelper rfl 1 "s48" ∈
      (reduceReturn []).erase.operations := SumcheckSourceLaws.return_uses_atPrefix

/-- The verifier point incorrectly selects the absent prover point. -/
def wrongPointReturn : Region protocolDialect repeatState reduceOutputs :=
  .ret (.cons (.there (.there (.there .here))) (.cons .here
    (.cons (.there .here) (.cons (.there (.there .here))
      (.cons (.there (.there (.there .here)))
        (.cons (.there (.there (.there (.there (.there .here))))) .nil))))))

theorem return_mutation_breaks_raw_association :
    wrongPointReturn.erase ≠ (reduceReturn []).erase := by
  intro same
  have lengths := congrArg (fun body => body.operations.length) same
  change 0 = 2 at lengths
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

set_option backward.isDefEq.respectTransparency false in
theorem original_return_retains_verifier_point :
    (reduceReturn []).denote
        (participantMeaningWith (.silent _) (participantActions (ZMod 5) (ZMod 5))
          (Zkc.Source.Structured.plainHelpers SumcheckSourceViews.unit) 1 [] {}) verifierState.get =
      .done (.cons none (.cons none (.cons none (.cons none
        (.cons (some [1]) (.cons (some 1) .nil)))))) := by
  kernel_rfl

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
