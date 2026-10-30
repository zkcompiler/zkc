module

public import TestsSecurity.RootComposition.FourProperties
public import TestsSecurity.RootComposition.FourFormula
public import ZkcSecurity.Bindings.Source.Installation
public import ZkcSecurity.Bindings.Transcript.RootConnectionEndpoint
public import ZkcSecurity.Claims.Methods.HonestReadbackCompleteness

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace TestsSecurity.RootComposition.Four.Endpoints
open Zkc.Source Zkc.Source.Structured Zkc.Construction ZkcExamples.Structured
open ZkcSecurity.FiatShamir ZkcSecurity.Source ZkcSecurity.Families.Sumcheck
open ZkcSecurity.Claims.HonestPair ZkcSecurity.Domains.PrimeField
open ZkcSecurity.Examples.Generated.FourSums
open ZkcSecurity.Examples.Generated.Components.FourSumsABI
open ZkcExamples.Structured.Generated.Connections.FourSums
abbrev Scalar := ZMod blsModulus
abbrev serviceHandle : Nat := (capabilities.head?.map Prod.snd).getD 0
local instance : Fact (IsField (model.Field SumcheckReferenceInstallation.field)) :=
  ⟨Field.toIsField Scalar⟩

theorem noLocal : validatorRouting.locals = [] := by decide +kernel

theorem foldLaws : Pair.FoldLaws (carriers := model.toCarriers)
    (PairScope.ofContext context) producerRouting validatorRouting :=
  publicFoldLaws context _ rfl _ _ rfl rfl rfl rfl noLocal

theorem actual (a b c d : List Scalar) (sa sb sc sd : Scalar) (count : Nat)
    (shapeA : a.length = 2^count) (shapeB : b.length = 2^count)
    (shapeC : c.length = 2^count) (shapeD : d.length = 2^count)
    (bounded : count ≤ Source.installation.maximum)
    (finiteA : a.length < indexLimit) (finiteB : b.length < indexLimit)
    (finiteC : c.length < indexLimit) (finiteD : d.length < indexLimit)
    (honest : sa = a.sum ∧ sb = b.sum ∧ sc = c.sum ∧ sd = d.sum) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model program context producerArtifact (producerInputs a b c d sa sb sc sd count))
      (Domain.participant model program context validatorArtifact (validatorInputs a b c d sa sb sc sd count)) := by
  have paired := Source.paired model a b c d sa sb sc sd count serviceHandle
    shapeA shapeB shapeC shapeD bounded finiteA finiteB finiteC finiteD honest
  exact Installation.accepted validatorCompiled producer validator rfl model _ _
    (NormalizedRoot.inputs model (Source.producerArguments model a b c d count))
    (NormalizedRoot.inputs model (Source.arguments model a b c d sa sb sc sd count serviceHandle))
    (by kernel_rfl) (by kernel_rfl) _ foldLaws _ paired (by kernel_rfl)
    (by intro p v accepted; rw [accepted]; rfl)

local instance : ∀ event : Domain.Event model.toCarriers, SampleableType (Domain.Raw event) :=
  rawSampleable blsModulus

theorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model imported.program subject.selection.context selected.artifacts.producer (abi.producer values))
      (Domain.participant model imported.program subject.selection.context selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨a, b, c, d, sa, sb, sc, sd, count, service, rfl⟩ := data_surjective values
  change List Scalar at a b c d
  change Scalar at sa sb sc sd
  change Nat at count
  change Option Nat at service
  prepare_target_readback [Scalar, Scalar] for subject using honestInput_iff
    reading (application_read a b c d sa sb sc sd count service)
    evaluating Formula.equation
  exact actual a b c d a.sum b.sum c.sum d.sum count
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption) ⟨rfl, rfl, rfl, rfl⟩

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi Formula.nonvacuous abi_readback

#print axioms actual
#print axioms compiled_ideal_complete
end TestsSecurity.RootComposition.Four.Endpoints
