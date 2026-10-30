module

public import ZkcExamples.Structured.Generated.Connections.TwoSums
public import ZkcSecurity.Bindings.Source.Installation
public import ZkcSecurity.Bindings.Transcript.RootConnectionEndpoint
public import ZkcSecurityExamples.Sumcheck.SourcePairInstallations
public import ZkcSecurity.Claims.Methods.HonestReadbackCompleteness
public import ZkcSecurityExamples.Components.TwoSumsFormula

@[expose] public section

/-! Two actual source reductions compose through the generated root pair.
Both phases share the actual service and accumulated transcript history.
-/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Examples.RootProperties.TwoSums
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Source ZkcSecurity.Families.Sumcheck ZkcSecurity.Realizations.Sumcheck
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.TwoSums
open ZkcSecurity.Examples.Generated.Components.TwoSumsABI
open ZkcExamples.Structured.Generated.Connections.TwoSums
abbrev Scalar := ZMod blsModulus
abbrev serviceHandle : Nat := (capabilities.head?.map Prod.snd).getD 0
local instance : Fact (IsField (model.Field SumcheckReferenceInstallation.field)) :=
  ⟨Field.toIsField Scalar⟩

theorem noLocal : validatorRouting.locals = [] := by decide +kernel

theorem foldLaws : Pair.FoldLaws (carriers := model.toCarriers)
    (PairScope.ofContext context) producerRouting validatorRouting :=
  publicFoldLaws context _ rfl _ _ rfl rfl rfl rfl noLocal

theorem actual (left right : List Scalar) (a b : Scalar) (count : Nat)
    (leftShape : left.length = 2^count) (rightShape : right.length = 2^count)
    (bounded : count ≤ SumcheckSourceSelections.maximum .twoSums) (small : count < 64)
    (leftFinite : left.length < indexLimit) (rightFinite : right.length < indexLimit)
    (honest : a = left.sum ∧ b = right.sum) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model program context producerArtifact
        (producerInputs left right a b count))
      (Domain.participant model program context validatorArtifact
        (validatorInputs left right a b count)) := by
  have paired := SourcePairInstallations.two model (PairScope.ofContext context)
    ⟨rfl, rfl⟩ (by decide +kernel) (by decide +kernel) left right count serviceHandle a b
    leftShape rightShape bounded small leftFinite rightFinite honest
  exact Installation.accepted validatorCompiled producer validator rfl model _ _
    (SourceProducerRoot.rootInputs model .twoSums (.cons left (.cons right (.cons count .nil))))
    (SourceRootReference.rootInputs model .twoSums (.cons (some left) (.cons (some right) (.cons (some a) (.cons (some b) (.cons (some count) (.cons (some serviceHandle) .nil)))))))
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
  obtain ⟨left, right, a, b, count, service, rfl⟩ := data_surjective values
  change List Scalar at left right
  change Scalar at a b
  change Nat at count
  change Option Nat at service
  prepare_target_readback [Scalar, Scalar] for subject using honestInput_iff
    reading (application_read left right a b count service)
    evaluating ZkcSecurity.Examples.Components.TwoSums.Formula.equation
  have shape : left.length = 2^count := by assumption
  have finite : left.length < indexLimit := by assumption
  have small : count < 64 :=
    (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (shape ▸ finite)
  exact actual left right left.sum right.sum count shape (by assumption) (by assumption)
    small finite (by assumption) ⟨rfl, rfl⟩

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi ZkcSecurity.Examples.Components.TwoSums.Formula.nonvacuous abi_readback

#print axioms actual
#print axioms compiled_ideal_complete
end ZkcSecurity.Examples.RootProperties.TwoSums
