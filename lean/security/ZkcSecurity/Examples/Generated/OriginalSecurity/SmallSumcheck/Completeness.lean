module

public import ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Honest
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Completeness
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Families.Sumcheck TableComponent
open ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Realizations.Sumcheck.OriginalRaw
open ZkcSecurity.Realizations.Sumcheck.OriginalRoot
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.SmallSumcheck (subject)
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
abbrev Scalar := ZMod blsModulus
abbrev Group := ZMod blsModulus
local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant subject.domainModel ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program subject.selection.context
        ZkcSecurity.Examples.Generated.SmallSumcheck.selected.artifacts.producer (abi.producer values))
      (Domain.participant subject.domainModel ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program subject.selection.context
        ZkcSecurity.Examples.Generated.SmallSumcheck.selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨input0, input1, input2, input3, rfl⟩ := data_surjective values
  change List Scalar at input0
  change Scalar at input1
  change Nat at input2
  change Option Nat at input3
  change Readback _
    (Domain.participant (ringModel Scalar Group) _ _ ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckProducerRoot.artifact (producerInputs input0 input1 input2))
    (Domain.participant (ringModel Scalar Group) _ _ ZkcSecurity.Examples.Generated.OriginalArtifacts.SmallSumcheckValidatorRoot.artifact (validatorInputs input0 input1 input2))
  prepare_target_readback [Scalar, Group] for subject using honestInput_iff
    reading (application_read input0 input1 input2 input3) evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation
  have shape0 : PrimitiveLibrary.HasShape input0 input2 1 := by
    simp only [PrimitiveLibrary.HasShape, Nat.mod_one, Nat.div_one]
    have tableSize : input0.length = 2 ^ input2 := by assumption
    have lengthBound : input0.length < indexLimit := by assumption
    have dimensionBound : input2 < 64 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (tableSize ▸ lengthBound)
    exact ⟨by decide, dimensionBound, trivial, by simpa only [one_mul] using tableSize⟩
  exact ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Honest.actual input0 input2 (input3.getD 0) shape0 (by assumption) (by assumption) (initialHistory input0 input0.sum input2)

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi ZkcSecurity.Examples.Components.SmallSumcheck.Formula.nonvacuous abi_readback

end ZkcSecurity.Examples.Generated.OriginalSecurity.SmallSumcheck.Completeness
