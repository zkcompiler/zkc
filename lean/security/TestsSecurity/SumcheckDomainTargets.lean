module

public import ZkcSecurity.Examples.Components.SmallSumcheckDomainTarget
public import ZkcSecurity.Examples.Components.TwoSumsDomainTarget

@[expose] public section

/-! Adversarial target controls use the actual generated validator Subjects.
Malformed table shapes and excessive round counts do not alter target truth. -/
noncomputable section
set_option autoImplicit false
namespace TestsSecurity.SumcheckDomainTargets
open ZkcSecurity.Examples
open Zkc.Source.Structured

example (raw : List Components.SmallSumcheck.DomainTarget.Scalar)
    (claim : Components.SmallSumcheck.DomainTarget.Scalar) (count : Nat)
    (bounded : raw.length < indexLimit) :
    Generated.SmallSumcheck.validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement raw claim count) ↔ raw.sum ≠ claim :=
  Components.SmallSumcheck.DomainTarget.false_iff raw claim count bounded

example (count : Nat) (witness : Generated.SmallSumcheck.validatorSubject.Witness) :
    Generated.SmallSumcheck.validatorSubject.Holds
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement [] 0 count) witness := by
  apply (Components.SmallSumcheck.DomainTarget.holds_iff [] 0 count witness
    (by decide +kernel)).mpr
  rfl

example (count : Nat) :
    Generated.SmallSumcheck.validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.statement [] 1 count) := by
  rw [Components.SmallSumcheck.DomainTarget.false_iff [] 1 count (by decide +kernel)]
  norm_num

example (left right : List Components.TwoSums.DomainTarget.Scalar)
    (leftClaim rightClaim : Components.TwoSums.DomainTarget.Scalar) (count : Nat)
    (leftBound : left.length < indexLimit) (rightBound : right.length < indexLimit) :
    Generated.TwoSums.validatorSubject.FalseStatement
      (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement left right leftClaim rightClaim count) ↔
      left.sum ≠ leftClaim ∨ right.sum ≠ rightClaim :=
  Components.TwoSums.DomainTarget.false_iff left right leftClaim rightClaim count
    leftBound rightBound

example (witness : Generated.TwoSums.validatorSubject.Witness) :
    Generated.TwoSums.validatorSubject.Holds
      (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [] [] 0 0 99) witness := by
  apply (Components.TwoSums.DomainTarget.holds_iff [] [] 0 0 99 witness
    (by decide +kernel) (by decide +kernel)).mpr
  exact ⟨rfl, rfl⟩

example : Generated.TwoSums.validatorSubject.FalseStatement
    (ZkcSecurity.Examples.Generated.Components.TwoSumsABI.statement [] [] 0 1 99) := by
  rw [Components.TwoSums.DomainTarget.false_iff [] [] 0 1 99
    (by decide +kernel) (by decide +kernel)]
  norm_num

#print axioms Components.SmallSumcheck.DomainTarget.holds_iff
#print axioms Components.SmallSumcheck.DomainTarget.false_iff
#print axioms Components.TwoSums.DomainTarget.holds_iff
#print axioms Components.TwoSums.DomainTarget.false_iff

end TestsSecurity.SumcheckDomainTargets
