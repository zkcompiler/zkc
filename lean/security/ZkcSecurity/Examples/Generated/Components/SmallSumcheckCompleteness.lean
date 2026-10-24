module

public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView
public import ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
public import ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula
public import ZkcSecurity.Families.Sumcheck.TableComponentReadbackExecution
public import ZkcSecurity.Examples.Components.SumcheckReadbackHelpers
public import ZkcSecurity.FiatShamir.HonestReadbackCompleteness
public meta import ZkcSecurity.Tools.ComponentReadback
public meta import ZkcSecurity.Tools.TargetEvaluation

@[expose] public section
noncomputable section

/-! Generated from the admitted pair by Generation.SumcheckCompleteness.
Installed formula mathematics is explicit; input and execution assembly
is source driven and kernel checked. Regenerate; do not hand edit. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
namespace ZkcSecurity.Examples.Generated.Components.SmallSumcheckCompleteness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Examples.Components ZkcExamples.Structured
open ZkcSecurity.Families.Sumcheck.TableComponent
open ZkcSecurity.Families.Sumcheck.TableComponent.Execution ReadbackRound
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.FiatShamir
open ZkcSecurity.Examples.Generated.SmallSumcheck (subject)
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckRounds

abbrev Scalar := ZMod blsModulus
abbrev Group := ZMod blsModulus
local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback
      (fun _ result => HonestCompiled.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant subject.domainModel ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program
        subject.selection.context ZkcSecurity.Examples.Generated.SmallSumcheck.selected.artifacts.producer (abi.producer values))
      (Domain.participant subject.domainModel ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program
        subject.selection.context ZkcSecurity.Examples.Generated.SmallSumcheck.selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨input0, input1, input2, input3, rfl⟩ := data_surjective values
  change List Scalar at input0
  change Scalar at input1
  change Nat at input2
  change Option Nat at input3
  change Readback _
    (Domain.participant (ringModel Scalar Group) _ _ ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.artifact (producerInputs input0 input1 input2))
    (Domain.participant (ringModel Scalar Group) _ _ ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.artifact (validatorInputs input0 input1 input2))
  prepare_target_readback [Scalar, Group] for subject using honestInput_iff
    reading (application_read input0 input1 input2 input3)
    evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation
  have indexCapacity : 64 < indexLimit := by decide +kernel
  have helpers0 := SumcheckDomainHelpers.round_helpers (K := Scalar) (H := Group)
    ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView.helper_bodies round0.plan rfl rfl rfl rfl
  have sourceRule0 := ReadbackRound.sourceLoopBind
    (A := Domain.Result (ringModel Scalar Group).toCarriers) (B := Domain.Result (ringModel Scalar Group).toCarriers)
    round0.plan ("bls12-381.fr") rfl ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program helpers0
    subject.selection.context round0.sites _ _ _ _
    (round0.producer_block Scalar Group _ subject.selection.context rfl)
    (round0.validator_block Scalar Group _ subject.selection.context rfl)
  dsimp only [round0.producerCapture, round0.validatorCapture, round0.descriptor] at sourceRule0
  simp only [ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView.context_suite, Nat.reduceAdd] at sourceRule0
  compose_component_readback [sourceRule0]
    normalizing (
      try (
        rw [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.participant_eq, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.participant_eq]
        simp only [producerInputs, validatorInputs]
        unfold_component_bodies [ZkcExamples.Structured.Generated.Constructed.SmallSumcheckProducer.view, ZkcExamples.Structured.Generated.Constructed.SmallSumcheckValidator.view])
      normalize_sumcheck_readback [Scalar, Group, ZkcSecurity.Examples.Generated.SmallSumcheck.imported.program, ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView.helper_bodies]
        unfolding [ZkcSecurity.Examples.Generated.Components.SmallSumcheckValidatorView.context_suite])
    solving (first | rfl | assumption | omega)
    finishing rfl

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi ZkcSecurity.Examples.Components.SmallSumcheck.Formula.nonvacuous readback

end ZkcSecurity.Examples.Generated.Components.SmallSumcheckCompleteness
