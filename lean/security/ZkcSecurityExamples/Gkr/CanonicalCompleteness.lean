module

public import ZkcSecurityExamples.Gkr.CanonicalConnection
public import ZkcSecurity.Bindings.Transcript.RootConnectionExecution
public import ZkcSecurity.Bindings.Transcript.RootConnectionEndpoint
public import ZkcSecurity.Claims.Methods.HonestReadbackCompleteness
public import Zkc.Construction.OriginalRoutingCongruence

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

theorem abi_readback (values : Data) (related : subject.Relation (abi.pack values))
    (honest : subject.HonestInput (abi.pack values)) :
    Readback (fun _ result => Domain.acceptanceAt subject.selection.position result.values = some true)
      (Domain.participant model imported.program subject.selection.context
        selected.artifacts.producer (abi.producer values))
      (Domain.participant model imported.program subject.selection.context
        selected.artifacts.validator (abi.validator values)) := by
  have admitted := CanonicalPolicy.admitted values honest
  have correct := (CanonicalPolicy.relation_exact values).mp related
  let runtime := CanonicalPolicy.runtime values
  have source := CanonicalReadback.actual (G := Scalar) _ _ admitted correct 7 none
    CanonicalConnection.scope ⟨rfl, rfl⟩ (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
  let producerValues := (ZkcExamples.Structured.Generated.Connections.Gkr.producer.inputs.abi.read (abi.producer values)
    imported.program.payload.entry.inputs).getD
      (SourceRows.circuitInputs runtime.encoding runtime.outputs none)
  have readP : ZkcExamples.Structured.Generated.Connections.Gkr.producer.inputs.abi.read (abi.producer values)
      imported.program.payload.entry.inputs = some producerValues := by
    obtain ⟨fields, rfl⟩ := Canonical.InputView.pack_surjective values
    kernel_rfl
  have sourceP : Occurrence.participant model imported.program 0 producerValues =
      Occurrence.participant model imported.program 0
        (SourceRows.circuitInputs runtime.encoding runtime.outputs none) := by
    apply Occurrence.participant_mask_congr
    obtain ⟨fields, rfl⟩ := Canonical.InputView.pack_surjective values
    rfl
  change ZkcSecurity.Source.Pair CanonicalConnection.scope CanonicalReadback.Post
    (Occurrence.participant model imported.program 0
      (SourceRows.circuitInputs runtime.encoding runtime.outputs none))
    (Occurrence.participant model imported.program 1
      (SourceRows.circuitInputs runtime.encoding runtime.outputs (some 7))) at source
  rw [← sourceP] at source
  apply ZkcSecurity.Source.Installation.accepted validatorCompiled
    ZkcExamples.Structured.Generated.Connections.Gkr.producer ZkcExamples.Structured.Generated.Connections.Gkr.validator rfl model
    (abi.producer values) (abi.validator values) producerValues
    (SourceRows.circuitInputs runtime.encoding runtime.outputs (some 7)) readP ?_
    CanonicalConnection.scope CanonicalConnection.foldLaws CanonicalReadback.Post source ?_ ?_
  · obtain ⟨fields, rfl⟩ := Canonical.InputView.pack_surjective values
    kernel_rfl
  · obtain ⟨fields, rfl⟩ := Canonical.InputView.pack_surjective values
    kernel_rfl
  · rintro p v ⟨_, rfl⟩
    rfl

theorem compiled_ideal_complete : CanonicalCompleteness subject 0 :=
  Readback.perfect_abi subject abi CanonicalPolicy.nonvacuous
    abi_readback
end ZkcSecurity.Realizations.Gkr.CanonicalCompleteness
