import ZkcSecurity.Examples.Components.SmallSumcheckFormula
import ZkcSecurity.Examples.Components.TwoSumsFormula

/-! Kernel-checked controls on the fixed generated Subjects: optional handles,
absent data, malformed honest shapes, and retained truth outside honest policy. -/
set_option autoImplicit false
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
#print axioms SmallSumcheck.Formula.relation_iff
#print axioms SmallSumcheck.Formula.nonvacuous
#print axioms ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI.context_eq
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.sourceInputs_surjective
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.policy_iff
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.runtimeInputs_eq
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.preparation
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.honestInput_exists
#print axioms TwoSums.Formula.equation
#print axioms TwoSums.Formula.relation_iff
#print axioms TwoSums.Formula.nonvacuous
#print axioms ZkcSecurity.Examples.Generated.Components.TwoSumsABI.context_eq
#print axioms Small.arbitrary_service_honest
#print axioms Small.malformed_shape_related
#print axioms Two.arbitrary_service_honest
#print axioms Two.malformed_shape_related
end
end TestsSecurity.SumcheckSubjectInputs
