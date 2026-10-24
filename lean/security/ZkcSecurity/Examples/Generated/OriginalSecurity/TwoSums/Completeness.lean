module

public import ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Honest
public import ZkcSecurity.Examples.Generated.Components.TwoSumsABI
public import ZkcSecurity.Examples.Components.TwoSumsFormula

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Completeness
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.TwoSums (subject)
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI
abbrev Scalar := ZMod blsModulus
abbrev Group := ZMod blsModulus
local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant subject.domainModel ZkcSecurity.Examples.Generated.TwoSums.imported.program subject.selection.context
        ZkcSecurity.Examples.Generated.TwoSums.selected.artifacts.producer (abi.producer values))
      (Domain.participant subject.domainModel ZkcSecurity.Examples.Generated.TwoSums.imported.program subject.selection.context
        ZkcSecurity.Examples.Generated.TwoSums.selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨input0, input1, input2, input3, input4, input5, rfl⟩ := data_surjective values
  change List Scalar at input0
  change List Scalar at input1
  change Scalar at input2
  change Scalar at input3
  change Nat at input4
  change Option Nat at input5
  change Readback _
    (Domain.participant (ringModel Scalar Group) _ _ ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsProducerRoot.artifact (producerInputs input0 input1 input2 input3 input4))
    (Domain.participant (ringModel Scalar Group) _ _ ZkcSecurity.Examples.Generated.OriginalArtifacts.TwoSumsValidatorRoot.artifact (validatorInputs input0 input1 input2 input3 input4))
  prepare_target_readback [Scalar, Group] for subject using honestInput_iff
    reading (application_read input0 input1 input2 input3 input4 input5) evaluating ZkcSecurity.Examples.Components.TwoSums.Formula.equation
  have shape0 : PrimitiveLibrary.HasShape input0 input4 1 := by
    simp only [PrimitiveLibrary.HasShape, Nat.mod_one, Nat.div_one]
    exact ⟨by decide, by omega, trivial, by simpa only [one_mul] using (by assumption : input0.length = 1 * 2 ^ input4)⟩
  have shape1 : PrimitiveLibrary.HasShape input1 input4 1 := by
    simp only [PrimitiveLibrary.HasShape, Nat.mod_one, Nat.div_one]
    exact ⟨by decide, by omega, trivial, by simpa only [one_mul] using (by assumption : input1.length = 1 * 2 ^ input4)⟩
  exact ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Honest.actual input0 input1 input4 (input5.getD 0) shape0 (by assumption) shape1 (by assumption) (by assumption) (initialHistory input0 input1 input0.sum input1.sum input4)

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi ZkcSecurity.Examples.Components.TwoSums.Formula.nonvacuous abi_readback

end ZkcSecurity.Examples.Generated.OriginalSecurity.TwoSums.Completeness
