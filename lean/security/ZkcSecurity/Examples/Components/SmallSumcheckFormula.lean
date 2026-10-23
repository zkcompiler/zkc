module

public import ZkcSecurity.Examples.Generated.SmallSumcheck
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
public import ZkcSecurity.Claims.Completeness
public import ZkcExamples.Structured.SumcheckContractBindings

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

theorem equation (raw : List Scalar) (claim : Scalar) (bounded : raw.length < indexLimit) :
    subject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons raw (.cons claim .nil)) = .done (.cons (decide (claim = raw.sum)) .nil) := by
  change invoke (closedMeaningsOn (ringModel Scalar Scalar) imported.program.payload.definitions)
    ZkcExamples.Structured.SumcheckRelationContract.sumHelper (.cons raw (.cons claim .nil)) =
      (.done (.cons (decide (claim = raw.sum)) .nil) : Closed (Values (assignment Scalar Scalar) [.boolean]))
  rw [← closedMeanings_eq_closedMeaningsOn]
  have same : imported.program = ZkcExamples.Structured.SumcheckSourceViews.imported.program :=
    Zkc.Verification.Imported.unique _ _
  rw [same]
  exact ZkcExamples.Structured.SumcheckContractBindings.public_formula_equation raw claim bounded


/-- Truth is the actual retained formula, without an honest-input assumption. -/
theorem relation_iff (raw : List Scalar) (claim : Scalar) (count : Nat) (service : Option Nat)
    (bounded : raw.length < indexLimit) :
    subject.Relation (inputs raw claim count service) ↔ raw.sum = claim := by
  refine (Subject.relation_iff_of_read subject _ _ (application_read raw claim count service)).trans ?_
  change subject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
    (.cons raw (.cons claim .nil)) =
      (.done (.cons true .nil) : Closed (Values (assignment Scalar Scalar) [.boolean])) ↔ _
  rw [equation raw claim bounded]
  simp [eq_comm]

theorem nonvacuous : Nonvacuous subject := by
  refine ⟨inputs [0] 0 0 (some 0), ?_, ?_⟩
  · rw [relation_iff _ _ _ _ (by decide +kernel)]
    simp
  · rw [honestInput_iff]
    decide +kernel


end ZkcSecurity.Examples.Components.SmallSumcheck.Formula
