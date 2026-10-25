module

public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.Examples.Components.TwoSumsFormula

@[expose] public section

/-! Kernel-checked controls on the fixed generated Subjects: optional handles,
absent data, malformed honest shapes, and retained truth outside honest policy. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000
namespace TestsSecurity.SumcheckSubjectInputs
open Zkc.Source Zkc.Source.Structured
open ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Examples.Components

noncomputable section

namespace Small
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI SmallSumcheck.Formula

/-- Independent test characterization; generated roots do not consume this lemma. -/
theorem relation_iff (raw : List Scalar) (claim : Scalar) (count : Nat) (service : Option Nat)
    (bounded : raw.length < indexLimit) :
    subject.Relation (inputs raw claim count service) ↔ raw.sum = claim := by
  refine (Subject.relation_iff_of_read subject _ _ (application_read raw claim count service)).trans ?_
  change subject.target.formula.invokeRelationOn ZkcSecurity.Domains.PrimeField.blsScalarModel
    (.cons raw (.cons claim .nil)) =
      (.done (.cons true .nil) : Closed (Values (assignment Scalar Scalar) [.boolean])) ↔ _
  rw [equation raw claim bounded]
  simp [eq_comm]

theorem arbitrary_service_honest :
    subject.HonestInput (inputs [0] 0 0 (some indexLimit)) := by
  rw [honestInput_iff]
  decide +kernel

theorem missing_claim_not_honest :
    ¬ subject.HonestInput (sourceInputs (some [0]) none (some 0) (some 7)) := by
  rintro ⟨_, _, producer, validator, prepared, _⟩
  change (none : Option (_ × _)) = some (producer, validator) at prepared
  cases prepared

theorem malformed_shape_related :
    subject.Relation (inputs [0, 0, 0, 0, 0, 0] 0 99 (some 7)) := by
  rw [relation_iff _ _ _ _ (by decide +kernel)]
  simp

theorem malformed_shape_not_honest :
    ¬ subject.HonestInput (inputs [0, 0, 0, 0, 0, 0] 0 99 (some 7)) := by
  rw [honestInput_iff]
  decide +kernel

theorem false_claim_not_related : ¬ subject.Relation (inputs [0] 1 0 none) := by
  rw [relation_iff _ _ _ _ (by decide +kernel)]
  simp
end Small

namespace Two
open ZkcSecurity.Examples.Generated.TwoSums
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI TwoSums.Formula

/-- Independent test characterization; generated roots do not consume this lemma. -/
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

theorem arbitrary_service_honest :
    subject.HonestInput (inputs [0] [0] 0 0 0 (some indexLimit)) := by
  rw [honestInput_iff]
  decide +kernel

theorem missing_right_not_honest :
    ¬ subject.HonestInput (sourceInputs (some [0]) none (some 0) (some 0) (some 0) (some 7)) := by
  rintro ⟨_, _, producer, validator, prepared, _⟩
  change (none : Option (_ × _)) = some (producer, validator) at prepared
  cases prepared

theorem malformed_shape_related :
    subject.Relation (inputs [0, 0, 0, 0, 0, 0] [] 0 0 99 (some 7)) := by
  rw [relation_iff _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)]
  simp

theorem malformed_shape_not_honest :
    ¬ subject.HonestInput (inputs [0, 0, 0, 0, 0, 0] [] 0 0 99 (some 7)) := by
  rw [honestInput_iff]
  decide +kernel

theorem false_right_claim_not_related :
    ¬ subject.Relation (inputs [0] [0] 0 1 0 none) := by
  rw [relation_iff _ _ _ _ _ _ (by decide +kernel) (by decide +kernel)]
  simp
end Two

#print axioms Subject.relation_iff_of_read
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.sourceInputs_surjective
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.policy_iff
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.runtimeInputs_eq
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.preparation
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.honestInput_exists
#print axioms SmallSumcheck.Formula.equation
#print axioms Small.relation_iff
#print axioms SmallSumcheck.Formula.nonvacuous
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.context_eq
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.sourceInputs_surjective
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.policy_iff
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.runtimeInputs_eq
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.preparation
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.honestInput_exists
#print axioms TwoSums.Formula.equation
#print axioms Two.relation_iff
#print axioms TwoSums.Formula.nonvacuous
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.context_eq
#print axioms Small.arbitrary_service_honest
#print axioms Small.malformed_shape_related
#print axioms Two.arbitrary_service_honest
#print axioms Two.malformed_shape_related
end
end TestsSecurity.SumcheckSubjectInputs
