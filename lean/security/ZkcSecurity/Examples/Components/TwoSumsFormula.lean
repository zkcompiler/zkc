module

public import ZkcSecurity.Examples.Generated.TwoSums
public import ZkcSecurity.Examples.Generated.Components.TwoSumsABI
public import ZkcSecurity.Claims.Completeness
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

/-- No honest shape, maximum-round or service assumption enters formula truth. -/
theorem relation_iff (left right : List Scalar) (leftClaim rightClaim : Scalar)
    (count : Nat) (service : Option Nat)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    subject.Relation (inputs left right leftClaim rightClaim count service) ↔
      left.sum = leftClaim ∧ right.sum = rightClaim := by
  refine (Subject.relation_iff_of_read subject _ _
    (application_read left right leftClaim rightClaim count service)).trans ?_
  change subject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
    (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      (.done (.cons true .nil) : Closed (Values (assignment Scalar Scalar) [.boolean])) ↔ _
  rw [equation left right leftClaim rightClaim leftBound rightBound]
  simp only [PIR.Process.done.injEq]
  change (Values.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil :
    Values (assignment Scalar Scalar) [.boolean]) = .cons true .nil ↔ _
  simp only [Values.cons.injEq, and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr eq_comm eq_comm

theorem nonvacuous : Nonvacuous subject := by
  refine ⟨inputs [0] [0] 0 0 0 (some 0), ?_, ?_⟩
  · rw [relation_iff _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)]
    simp
  · rw [honestInput_iff]
    decide +kernel


end ZkcSecurity.Examples.Components.TwoSums.Formula
