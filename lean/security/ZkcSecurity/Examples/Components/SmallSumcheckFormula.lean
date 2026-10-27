module

public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
public import ZkcSecurity.Claims.Completeness
public meta import ZkcSecurity.Tools.TargetEvaluation
public import ZkcSecurity.Examples.Components.SmallSumcheckTarget

@[expose] public section

/-! Mathematical interpretation of the retained actual SmallSumcheck target.
The formula is identified through its admitted source program; no protocol
success or honest-input premise is used. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ZkcSecurity.Examples.Components.SmallSumcheck.Formula
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
abbrev Scalar := ZMod blsModulus

def formula : FormulaBinding imported subject.target.application.relation := by bind_contract

theorem equation (raw : List Scalar) (claim : Scalar) (bounded : raw.length < indexLimit) :
    formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons raw (.cons claim .nil)) = .done (.cons (decide (claim = raw.sum)) .nil) := by
  change invoke (closedMeaningsOn (ringModel Scalar Scalar) imported.program.payload.definitions)
    ZkcExamples.Structured.Generated.Mathematics.SmallSumcheck.public_sum.helper
      (.cons raw (.cons claim .nil)) =
      (.done (.cons (decide (claim = raw.sum)) .nil) : Closed (Values (assignment Scalar Scalar) [.boolean]))
  rw [← closedMeanings_eq_closedMeaningsOn]
  have same : imported.program =
      ZkcExamples.Structured.Generated.Bindings.SmallSumcheckInputs.imported.program :=
    Zkc.Verification.Imported.unique _ _
  rw [same]
  exact ZkcSecurity.Examples.Components.SmallSumcheck.target_equation (G := Scalar) raw claim bounded


theorem nonvacuous : Nonvacuous subject := by
  refine ⟨inputs [0] 0 0 (some 0), ?_, ?_⟩
  · prove_retained_target [Scalar, Scalar] reading (application_read [0] 0 0 (some 0))
      evaluating equation solving (decide +kernel)
  · rw [honestInput_iff]
    decide +kernel


end ZkcSecurity.Examples.Components.SmallSumcheck.Formula
