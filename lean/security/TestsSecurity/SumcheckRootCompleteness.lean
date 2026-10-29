module

public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckCompleteness
public import ZkcSecurity.Examples.Generated.Components.TwoSumsCompleteness
public import TestsSecurity.SumcheckSubjectInputs

@[expose] public section

/-! Actual generated root controls: both compiled experiments, unrestricted
service handles, retained false claims, and malformed honest-policy inputs. -/
set_option autoImplicit false
namespace TestsSecurity.SumcheckRootCompleteness
noncomputable section
open ZkcSecurity.Claims.HonestPair
open ZkcSecurity.Examples
open ZkcSecurity.Domains.PrimeField
open Zkc.Construction

local instance : ∀ event : Domain.Event blsScalarModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable Zkc.Source.Structured.blsModulus

example : CanonicalCompleteness Generated.SmallSumcheck.subject 0 :=
  Generated.Components.SmallSumcheckCompleteness.compiled_ideal_complete

example : CanonicalCompleteness Generated.TwoSums.subject 0 :=
  Generated.Components.TwoSumsCompleteness.compiled_ideal_complete

example (service : Option Nat) :
    Generated.SmallSumcheck.subject.HonestInput
      (Generated.Components.SmallSumcheckABI.inputs [0] 0 0 service) := by
  rw [Generated.Components.SmallSumcheckABI.honestInput_iff]
  decide +kernel

example (service : Option Nat) :
    Generated.TwoSums.subject.HonestInput
      (Generated.Components.TwoSumsABI.inputs [0] [0] 0 0 0 service) := by
  rw [Generated.Components.TwoSumsABI.honestInput_iff]
  decide +kernel

example (service : Option Nat) :
    ¬ Generated.SmallSumcheck.subject.Relation
      (Generated.Components.SmallSumcheckABI.inputs [0] 1 0 service) := by
  rw [TestsSecurity.SumcheckSubjectInputs.Small.relation_iff _ _ _ _ (by decide +kernel)]
  simp

example (service : Option Nat) :
    ¬ Generated.TwoSums.subject.Relation
      (Generated.Components.TwoSumsABI.inputs [0] [0] 0 1 0 service) := by
  rw [TestsSecurity.SumcheckSubjectInputs.Two.relation_iff _ _ _ _ _ _
    (by decide +kernel) (by decide +kernel)]
  simp

example (service : Option Nat) :
    ¬ Generated.SmallSumcheck.subject.HonestInput
      (Generated.Components.SmallSumcheckABI.inputs [] 0 0 service) := by
  rw [Generated.Components.SmallSumcheckABI.honestInput_iff]
  simp

example (service : Option Nat) :
    ¬ Generated.TwoSums.subject.HonestInput
      (Generated.Components.TwoSumsABI.inputs [0] [] 0 0 0 service) := by
  rw [Generated.Components.TwoSumsABI.honestInput_iff]
  simp

#print axioms Generated.Components.SmallSumcheckCompleteness.compiled_ideal_complete
#print axioms Generated.Components.TwoSumsCompleteness.compiled_ideal_complete
#print axioms ZkcSecurity.Examples.RootProperties.SmallSumcheck.abi_readback
#print axioms ZkcSecurity.Examples.RootProperties.TwoSums.abi_readback

end
end TestsSecurity.SumcheckRootCompleteness
