module

public import ZkcExamples.Structured.RepeatData
public import ZkcExamples.Structured.RepeatBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatViews
open Zkc.Source Zkc.Source.Structured RepeatBodies

set_option smartUnfolding false

def roundDefinition : CheckedProtocol where
  toProtocolSignature := roundSignature
  raw := roundBody.erase
  body := roundBody
  formed := roundBody.elaborate_erase

theorem round_signature : roundDefinition.signature = roundSignature := rfl
theorem round_raw : roundDefinition.raw = roundBody.erase := rfl
theorem round_body : roundDefinition.body = roundBody := rfl

def runDefinition : CheckedProtocol where
  toProtocolSignature := runSignature
  raw := runBody.erase
  body := runBody
  formed := runBody.elaborate_erase

theorem run_signature : runDefinition.signature = runSignature := rfl
theorem run_raw : runDefinition.raw = runBody.erase := rfl
theorem run_body : runDefinition.body = runBody := rfl

def definitions : List CheckedDefinition :=
  []

def ordered : List OrderedDefinition :=
  []

def headers : List ProtocolSignature := [runSignature, roundSignature]

def domains : List DomainSpec := []

def summaries : IdentitySummaries := []

def unit : UnitPayload where
  definitions := definitions
  protocols := [roundDefinition, runDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨RepeatData.snapshot, unit⟩

theorem headers_checked : checkUnitHeaders RepeatData.snapshot =
    .ok (domains, headers, summaries) := rfl

theorem helpers_checked : checkUnitHelpers RepeatData.snapshot domains summaries = .ok ordered := rfl

theorem protocols_checked :
    checkUnitProtocols RepeatData.snapshot domains summaries headers ordered = .ok unit.protocols := rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets RepeatData.snapshot).isOk = true := by decide +kernel

theorem effective_sites_checked :
    checkEffectiveProtocolSites RepeatData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata RepeatData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

theorem payload_linked : linkUnitPayload RepeatData.snapshot ordered unit.protocols = .ok unit := rfl

/-- All declarations, callback trees and metadata phases of the original unit. -/
theorem kernel_admission : check RepeatData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported RepeatData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = RepeatData.snapshot := imported.exactSubject

theorem round_member : roundDefinition ∈ unit.protocols := List.mem_cons_self

theorem run_member : runDefinition ∈ unit.protocols := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl

/-- Complete original-to-checked association includes every nested callback. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ RepeatData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders RepeatData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol RepeatData.snapshot domains summaries function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol RepeatData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-- Every original protocol is admitted to one exact checked tree. -/
theorem complete_original_protocol (function : Zkc.Source.Structured.Function)
    (member : .function function ∈ RepeatData.snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders RepeatData.snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ unit.protocols ∧
        checkProtocol RepeatData.snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ unit.protocols →
          checkProtocol RepeatData.snapshot domains summaries function headers = .ok other →
            other = definition :=
  imported.protocolChecked member kind

end ZkcExamples.Structured.RepeatViews
