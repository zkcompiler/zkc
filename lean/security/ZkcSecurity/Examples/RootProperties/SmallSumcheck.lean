module

public import ZkcExamples.Structured.Generated.Connections.SmallSumcheck
public import ZkcSecurity.Source.Installation
public import ZkcSecurity.FiatShamir.RootConnectionEndpoint
public import ZkcSecurity.Realizations.Sumcheck.SourcePairInstallations
public import ZkcSecurity.FiatShamir.HonestReadbackCompleteness
public import ZkcSecurity.Examples.Components.SmallSumcheckFormula

@[expose] public section

/-! Actual SmallSumcheck honest-pair completeness through the generated roots.
The same validator root remains available to the fixed soundness installation;
this module does not substitute a validator-handler success premise.
-/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.RootProperties.SmallSumcheck
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Source ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.SmallSumcheck
open ZkcSecurity.Examples.Generated.Components.SmallSumcheckABI
open ZkcExamples.Structured.Generated.Connections.SmallSumcheck
abbrev Scalar := ZMod blsModulus
abbrev serviceHandle : Nat := (capabilities.head?.map Prod.snd).getD 0
local instance : Fact (IsField (model.Field SumcheckReferenceInstallation.field)) :=
  ⟨Field.toIsField Scalar⟩

theorem noLocal : validatorRouting.locals = [] := by decide +kernel

theorem foldLaws : Pair.FoldLaws (carriers := model.toCarriers)
    (PairScope.ofContext context) producerRouting validatorRouting :=
  publicFoldLaws context _ rfl _ _ rfl rfl rfl rfl noLocal

theorem actual (original : List Scalar) (scalar : Scalar) (count : Nat)
    (shape : original.length = 2^count) (bounded : count ≤ SumcheckSourceSelections.maximum .small)
    (small : count < 64) (finite : original.length < indexLimit) (honest : scalar = original.sum) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model program context producerArtifact
        (producerInputs original scalar count))
      (Domain.participant model program context validatorArtifact
        (validatorInputs original scalar count)) := by
  have paired := SourcePairInstallations.small model (PairScope.ofContext context)
    ⟨rfl, rfl⟩ (by decide +kernel) original count serviceHandle scalar shape bounded small finite honest
  exact Installation.accepted validatorCompiled producer validator rfl model _ _
    (SourceProducerRoot.rootInputs model .small (.cons original (.cons count .nil)))
    (SourceRootReference.rootInputs model .small (.cons (some original) (.cons (some scalar) (.cons (some count) (.cons (some serviceHandle) .nil)))))
    (by kernel_rfl) (by kernel_rfl) _ foldLaws _ paired (by kernel_rfl)
    (by intro p v accepted; rw [accepted]; rfl)

local instance : ∀ event : Domain.Event model.toCarriers,
    SampleableType (Domain.Raw event) := rawSampleable blsModulus

theorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model imported.program subject.selection.context selected.artifacts.producer
        (abi.producer values))
      (Domain.participant model imported.program subject.selection.context selected.artifacts.validator
        (abi.validator values)) := by
  obtain ⟨original, scalar, count, service, rfl⟩ := data_surjective values
  change List Scalar at original
  change Scalar at scalar
  change Nat at count
  change Option Nat at service
  prepare_target_readback [Scalar, Scalar] for subject using honestInput_iff
    reading (application_read original scalar count service)
    evaluating ZkcSecurity.Examples.Components.SmallSumcheck.Formula.equation
  have shape : original.length = 2^count := by assumption
  have finite : original.length < indexLimit := by assumption
  have small : count < 64 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (shape ▸ finite)
  exact actual original original.sum count shape (by assumption) small finite rfl

/-- The unchanged request's canonical completeness game, with zero failure mass. -/
theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi ZkcSecurity.Examples.Components.SmallSumcheck.Formula.nonvacuous abi_readback

#print axioms actual
#print axioms compiled_ideal_complete
end ZkcSecurity.Examples.RootProperties.SmallSumcheck
