module

public import ZkcSecurity.Examples.Generated.TwoSums
public import ZkcSecurity.Examples.Generated.Components.TwoSumsABI
public import ZkcSecurity.Claims.Completeness
public meta import ZkcSecurity.Tools.TargetEvaluation
public import ZkcSecurity.Examples.Components.TwoSumsTarget

@[expose] public section

/-! The retained BothSums formula uses the shared checked finite-fold law.
All raw tables and scalar claims remain arbitrary within source capacity. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.TwoSums.Formula
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.TwoSums
open ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI
abbrev Scalar := ZMod blsModulus

theorem equation (left right : List Scalar) (leftClaim rightClaim : Scalar)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    subject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      .done (.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil) := by
  change invoke (closedMeaningsOn (ringModel Scalar Scalar) imported.program.payload.definitions)
    ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.helper3Helper
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      (.done (.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil) :
        Closed (Values (assignment Scalar Scalar) [.boolean]))
  rw [← closedMeanings_eq_closedMeaningsOn]
  have same : imported.program =
      ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.imported.program :=
    Zkc.Verification.Imported.unique _ _
  rw [same]
  change invoke (helperMeanings (F := Scalar) (G := Scalar))
    ZkcExamples.Structured.Generated.Bindings.TwoSumsInputs.helper3Helper
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      (.done (.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil) :
        Closed (Values (assignment Scalar Scalar) [.boolean]))
  simpa only [Bool.decide_and, eq_comm] using
    (target_equation (G := Scalar) left right leftClaim rightClaim leftBound rightBound)

theorem nonvacuous : Nonvacuous subject := by
  refine ⟨inputs [0] [0] 0 0 0 (some 0), ?_, ?_⟩
  · prove_retained_target [Scalar, Scalar] reading (application_read [0] [0] 0 0 0 (some 0))
      evaluating equation solving (decide +kernel)
  · rw [honestInput_iff]
    decide +kernel


end ZkcSecurity.Examples.Components.TwoSums.Formula
