module

public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.Claims.SubjectABI

@[expose] public section

/-! The unrestricted adversarial Subject reads the same original target as the
honest pair. Finite-fold capacity is used only to evaluate that source formula;
shape, maximum rounds and the honest policy are not assumed. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
namespace ZkcSecurity.Examples.Components.SmallSumcheck.DomainTarget
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
abbrev Scalar := Formula.Scalar

theorem formula_equation (raw : List Scalar) (claim : Scalar) (bounded : raw.length < indexLimit) :
    validatorSubject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
      (.cons raw (.cons claim .nil)) =
      .done (.cons (decide (claim = raw.sum)) .nil) :=
  Formula.equation raw claim bounded

theorem holds_iff (raw : List Scalar) (claim : Scalar) (count : Nat)
    (witness : validatorSubject.Witness) (bounded : raw.length < indexLimit) :
    validatorSubject.Holds (statement raw claim count) witness ↔ raw.sum = claim := by
  refine (ZkcSecurity.Claims.Domain.Subject.holds_iff_of_read validatorSubject _ witness _
    (validator_application_read raw claim count witness)).trans ?_
  change validatorSubject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
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

end ZkcSecurity.Examples.Components.SmallSumcheck.DomainTarget
