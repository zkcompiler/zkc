module

public import TestsSecurity.SourceAdmission.HistoricalPolicy
public import ZkcSecurity.Bindings.Subjects.ABI

@[expose] public section

/-! Transport the unchanged preparation domain through a checked ABI.
The premise compares policies on every prepared typed row, before execution.
For the two historical roots the old retained input-clause list was empty. -/
set_option autoImplicit false
namespace TestsSecurity.SourceAdmission.HistoricalPolicy
open Zkc.Source Zkc.Source.Structured Zkc.Construction
open ZkcSecurity.Claims.HonestPair (Subject)

variable {model : DomainModel} {original : Snapshot} {imported : Imported original}
  {selected : AuthoredPair.Selection original}

/-- The old registered policy and unchanged preparation for roots whose former
source had no input clauses. This definition is deliberately test-only. -/
def HonestInput (subject : Subject model original imported selected)
    (policy : InputPolicy subject.target.owner.protocol.inputs) (inputs : subject.Inputs) : Prop :=
  policy.Holds inputs ∧
    ∃ producer validator, subject.runtimeInputs inputs = some (producer, validator) ∧
      Domain.sortsMatch selected.artifacts.producer.inputs producer = true ∧
      Domain.sortsMatch selected.artifacts.validator.inputs validator = true

theorem honestInput_iff (subject : Subject model original imported selected)
    (policy : InputPolicy subject.target.owner.protocol.inputs) (abi : Subject.ABI subject)
    (equivalent : ∀ data, policy.Holds (abi.pack data) ↔
      inputsRepresentable (abi.pack data) ∧
        ∀ index isInput, subject.inputClause (abi.pack data) index isInput)
    (inputs : subject.Inputs) : HonestInput subject policy inputs ↔ subject.HonestInput inputs := by
  constructor
  · rintro ⟨policyHolds, prepared⟩
    obtain ⟨data, rfl⟩ := (abi.prepared_iff_exists inputs).mp prepared
    exact (abi.honest_pack_iff data).mpr ((equivalent data).mp policyHolds)
  · intro honest
    obtain ⟨data, rfl⟩ := abi.honest_exists inputs honest
    exact ⟨(equivalent data).mpr ((abi.honest_pack_iff data).mp honest),
      (abi.prepared_iff_exists _).mpr ⟨data, rfl⟩⟩

end TestsSecurity.SourceAdmission.HistoricalPolicy
