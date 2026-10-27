module

public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.Examples.Components.TwoSumsFormula
public import ZkcSecurity.Claims.SubjectABI
public meta import ZkcSecurity.Tools.TargetEvaluation

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
/-! Independent characterization controls for the actual retained targets.
These test lemmas are not consumed by either generated protocol root. -/
namespace TestsSecurity.SumcheckDomainTargets.Small
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
abbrev Scalar := ZkcSecurity.Examples.Components.SmallSumcheck.Formula.Scalar

theorem formula_equation (raw : List Scalar) (claim : Scalar) (bounded : raw.length < indexLimit) :
    ZkcSecurity.Examples.Components.SmallSumcheck.Formula.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons raw (.cons claim .nil)) =
      .done (.cons (decide (claim = raw.sum)) .nil) :=
  ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation raw claim bounded

theorem holds_iff (raw : List Scalar) (claim : Scalar) (count : Nat)
    (witness : validatorSubject.Witness) (bounded : raw.length < indexLimit) :
    validatorSubject.Holds (statement raw claim count) witness ↔ raw.sum = claim := by
  refine (ZkcSecurity.Claims.Domain.Subject.holds_iff_of_read validatorSubject _ witness _
    (validator_application_read raw claim count witness)).trans ?_
  change ZkcSecurity.Examples.Components.SmallSumcheck.Formula.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
    (.cons raw (.cons claim .nil)) =
      (.done (.cons true .nil) : Closed (Values (assignment Scalar Scalar) [.boolean])) ↔ _
  rw [formula_equation raw claim bounded]
  simp only [PIR.Process.done.injEq]
  change (Values.cons (decide (claim = raw.sum)) .nil : Values (assignment Scalar Scalar) [.boolean]) =
    .cons true .nil ↔ _
  simp only [Values.cons.injEq, and_true, decide_eq_true_eq]
  exact eq_comm

theorem false_iff (raw : List Scalar) (claim : Scalar) (count : Nat)
    (bounded : raw.length < indexLimit) :
    validatorSubject.FalseStatement (statement raw claim count) ↔ raw.sum ≠ claim :=
  ZkcSecurity.Claims.Domain.Subject.falseStatement_iff_of_holds validatorSubject _ _
    (fun witness => holds_iff raw claim count witness bounded)

end TestsSecurity.SumcheckDomainTargets.Small

namespace TestsSecurity.SumcheckDomainTargets.Two
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.TwoSums
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI
abbrev Scalar := ZkcSecurity.Examples.Components.TwoSums.Formula.Scalar

theorem formula_equation (left right : List Scalar) (leftClaim rightClaim : Scalar)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    ZkcSecurity.Examples.Components.TwoSums.Formula.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons left (.cons right (.cons leftClaim (.cons rightClaim .nil)))) =
      .done (.cons (decide (leftClaim = left.sum) && decide (rightClaim = right.sum)) .nil) :=
  ZkcSecurity.Examples.Components.TwoSums.Formula.equation left right leftClaim rightClaim leftBound rightBound

theorem holds_iff (left right : List Scalar) (leftClaim rightClaim : Scalar) (count : Nat)
    (witness : validatorSubject.Witness)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    validatorSubject.Holds (statement left right leftClaim rightClaim count) witness ↔
      left.sum = leftClaim ∧ right.sum = rightClaim := by
  refine (ZkcSecurity.Claims.Domain.Subject.holds_iff_of_read validatorSubject _ witness _
    (validator_application_read left right leftClaim rightClaim count witness)).trans ?_
  change ZkcSecurity.Examples.Components.TwoSums.Formula.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
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

end TestsSecurity.SumcheckDomainTargets.Two

namespace TestsSecurity.SumcheckDomainTargets
open ZkcSecurity.Examples
open Zkc.Source.Structured

example (raw : List Small.Scalar)
    (claim : Small.Scalar) (count : Nat)
    (bounded : raw.length < indexLimit) :
    Generated.SmallSumcheck.validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement raw claim count) ↔ raw.sum ≠ claim :=
  Small.false_iff raw claim count bounded

example (count : Nat) (witness : Generated.SmallSumcheck.validatorSubject.Witness) :
    Generated.SmallSumcheck.validatorSubject.Holds
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement [] 0 count) witness := by
  apply (Small.holds_iff [] 0 count witness
    (by decide +kernel)).mpr
  rfl

example (count : Nat) :
    Generated.SmallSumcheck.validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement [] 1 count) := by
  rw [Small.false_iff [] 1 count (by decide +kernel)]
  norm_num

example (left right : List Two.Scalar)
    (leftClaim rightClaim : Two.Scalar) (count : Nat)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    Generated.TwoSums.validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement left right leftClaim rightClaim count) ↔
      left.sum ≠ leftClaim ∨ right.sum ≠ rightClaim :=
  Two.false_iff left right leftClaim rightClaim count
    leftBound rightBound

example (witness : Generated.TwoSums.validatorSubject.Witness) :
    Generated.TwoSums.validatorSubject.Holds
      (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [] [] 0 0 99) witness := by
  apply (Two.holds_iff [] [] 0 0 99 witness
    (by decide +kernel) (by decide +kernel)).mpr
  exact ⟨rfl, rfl⟩

example : Generated.TwoSums.validatorSubject.FalseStatement
    (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [] [] 0 1 99) := by
  rw [Two.false_iff [] [] 0 1 99
    (by decide +kernel) (by decide +kernel)]
  norm_num

#print axioms Small.holds_iff
#print axioms Small.false_iff
#print axioms Two.holds_iff
#print axioms Two.false_iff

end TestsSecurity.SumcheckDomainTargets

namespace TestsSecurity.TargetEvaluation
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Examples.Generated
open ZkcSecurity.Examples.Generated.Components
abbrev Scalar := ZMod Zkc.Source.Structured.blsModulus

example (count : Nat) (witness : SmallSumcheck.validatorSubject.Witness) :
    SmallSumcheck.validatorSubject.Holds (SmallSumcheckABI.statement [] 0 count) witness ∧ True := by
  constructor
  · prove_retained_target [Scalar, Scalar]
      reading (SmallSumcheckABI.validator_application_read [] 0 count witness)
      evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation
      solving (decide +kernel)
  · trivial

example (witness : TwoSums.validatorSubject.Witness) :
    TwoSums.validatorSubject.Holds (TwoSumsABI.statement [] [] 0 0 99) witness := by
  prove_retained_target [Scalar, Scalar]
    reading (TwoSumsABI.validator_application_read [] [] 0 0 99 witness)
    evaluating ZkcSecurity.Examples.Components.TwoSums.Formula.equation
    solving (decide +kernel)

-- A false retained target cannot be replaced by an honest or chosen predicate.
example : True := by
  fail_if_success
    have bad : SmallSumcheck.validatorSubject.Holds (SmallSumcheckABI.statement [] 1 0)
        (fun _ _ => none) := by
      prove_retained_target [Scalar, Scalar]
        reading (SmallSumcheckABI.validator_application_read [] 1 0 _)
        evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation
        solving (decide +kernel)
  trivial

-- Unavailable finite-fold capacity remains an obligation.
example (raw : List Scalar) (claim : Scalar) (_correct : claim = raw.sum) : True := by
  fail_if_success
    have bad : SmallSumcheck.validatorSubject.Holds (SmallSumcheckABI.statement raw claim 0)
        (fun _ _ => none) := by
      prove_retained_target [Scalar, Scalar]
        reading (SmallSumcheckABI.validator_application_read raw claim 0 _)
        evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation solving assumption
  trivial

-- A read from a different retained target does not select this subject.
set_option linter.unreachableTactic false in
example : True := by
  fail_if_success
    have bad : SmallSumcheck.validatorSubject.Holds (SmallSumcheckABI.statement [] 0 0)
        (fun _ _ => none) := by
      prove_retained_target [Scalar, Scalar]
        reading (TwoSumsABI.validator_application_read [] [] 0 0 0 _)
        evaluating ZkcSecurity.Examples.Components.TwoSums.Formula.equation
        solving (decide +kernel)
  trivial

end TestsSecurity.TargetEvaluation
