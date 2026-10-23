module

public import ZkcSecurity.Examples.Components.TwoSumsFormula
public import ZkcSecurity.Claims.SubjectABI

@[expose] public section

/-! The actual conjunction target of the unrestricted sequential verifier.
Neither the producer's policy nor either child's target truth is assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
namespace ZkcSecurity.Examples.Components.TwoSums.DomainTarget
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.TwoSums
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI
abbrev Scalar := Formula.Scalar

theorem formula_equation (left right : List Scalar) (leftClaim rightClaim : Scalar)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    validatorSubject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      .done (.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil) :=
  Formula.equation left right leftClaim rightClaim leftBound rightBound

theorem holds_iff (left right : List Scalar) (leftClaim rightClaim : Scalar) (count : Nat)
    (witness : validatorSubject.Witness)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    validatorSubject.Holds (statement left right leftClaim rightClaim count) witness ↔
      left.sum = leftClaim ∧ right.sum = rightClaim := by
  refine (ZkcSecurity.Claims.Domain.Subject.holds_iff_of_read validatorSubject _ witness _
    (validator_application_read left right leftClaim rightClaim count witness)).trans ?_
  change validatorSubject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
    (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      (.done (.cons true .nil) : Closed (Values (assignment Scalar Scalar) [.boolean])) ↔ _
  rw [formula_equation left right leftClaim rightClaim leftBound rightBound]
  simp only [PIR.Process.done.injEq]
  change (Values.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil :
    Values (assignment Scalar Scalar) [.boolean]) = .cons true .nil ↔ _
  simp only [Values.cons.injEq, and_true, Bool.and_eq_true, decide_eq_true_eq]
  exact and_congr eq_comm eq_comm

theorem false_iff (left right : List Scalar) (leftClaim rightClaim : Scalar) (count : Nat)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    validatorSubject.FalseStatement (statement left right leftClaim rightClaim count) ↔
      left.sum ≠ leftClaim ∨ right.sum ≠ rightClaim := by
  have transported := ZkcSecurity.Claims.Domain.Subject.falseStatement_iff_of_holds
    validatorSubject (statement left right leftClaim rightClaim count) _
    (fun witness => holds_iff left right leftClaim rightClaim count witness leftBound rightBound)
  simpa only [not_and_or] using transported

end ZkcSecurity.Examples.Components.TwoSums.DomainTarget
