module

public import ZkcSecurity.Realizations.Gkr.CanonicalInstallation
public import ZkcSecurity.Realizations.Gkr.CanonicalPolicy
public import ZkcSecurity.Realizations.Gkr.CanonicalReadback
public import ZkcSecurity.FiatShamir.OriginalReadback
public import ZkcSecurity.FiatShamir.HonestReadbackCompleteness

@[expose] public section

/-! Perfect completeness of the actual current compiled pair. The source
producer computes its proof and the same full nominal certificates transport
both participants, with their exact shared transcript. -/
set_option autoImplicit false
set_option maxRecDepth 50000
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace ZkcSecurity.Realizations.Gkr.CanonicalCompleteness
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.FiatShamir ZkcSecurity.Claims.HonestPair
open Generated.Subject Generated.ABI
abbrev Scalar := ZMod blsModulus
local instance : ∀ event : Domain.Event subject.domainModel.toCarriers,
    SampleableType (Domain.Raw event) := ZkcSecurity.Domains.PrimeField.rawSampleable blsModulus

def history (values : Data) : Domain.History model.toCarriers :=
  Domain.PublicBinding.history subject.originalExport selected.policy.publicInputs
    (Canonical.statement model (CanonicalPolicy.runtime values)) subject.publicBindingArity subject.publicBindingData

/-- Actual producer simulation for every typed ABI input, before any circuit
truth or admission assumption. Outputs are masked by the producer role. -/
def producerCertificate (values : Data) :=
  OriginalCertificates.producer (F := Scalar) (G := Scalar) 0
    (CanonicalPolicy.runtime values).inputs (CanonicalPolicy.runtime values).outputs
    (CanonicalPolicy.runtime values).add (CanonicalPolicy.runtime values).mul
    (CanonicalPolicy.runtime values).layers (CanonicalPolicy.runtime values).selector
    (CanonicalPolicy.runtime values).width (history values)

def validatorCertificate (values : Data) :=
  CanonicalInstallation.certificate
    (Canonical.statement model (CanonicalPolicy.runtime values)) (history values)

theorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model imported.program subject.selection.context
        selected.artifacts.producer (abi.producer values))
      (Domain.participant model imported.program subject.selection.context
        selected.artifacts.validator (abi.validator values)) := by
  obtain ⟨initial, outputs, add, mul, layers, selector, width, service, rfl⟩ := data_surjective values
  let values := data initial outputs add mul layers selector width service
  have admitted := CanonicalPolicy.admitted values honest
  have correct := (CanonicalPolicy.relation_exact values).mp related
  have source := CanonicalReadback.actual (G := Scalar) _ _ admitted correct 0 (some 0) (history values)
  apply (Readback.original (producerCertificate values) (validatorCertificate values) source).mono
  intro actualP actualV aligned
  obtain ⟨sourceP, sourceV, ⟨finalHistory, rfl, rfl⟩, _, returnedV⟩ := aligned
  obtain ⟨value, valueEq, valuesEq, _⟩ := returnedV
  have same : true = value := by
    have := congrArg (fun values => values.get .here) valueEq
    exact Option.some.inj this
  cases same
  change Domain.acceptanceAt 0 actualV.values = some true
  rw [valuesEq]
  rfl

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi CanonicalPolicy.nonvacuous
    abi_readback
end ZkcSecurity.Realizations.Gkr.CanonicalCompleteness
