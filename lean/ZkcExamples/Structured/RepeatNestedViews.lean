module

public import ZkcExamples.Structured.RepeatNestedData
public import ZkcExamples.Structured.RepeatNestedBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatNestedViews
open Zkc.Source Zkc.Source.Structured RepeatNestedBodies

set_option smartUnfolding false

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

def headers : List ProtocolSignature := [runSignature]

def domains : List DomainSpec := []

def summaries : IdentitySummaries := []

def unit : UnitPayload where
  definitions := definitions
  protocols := [runDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨RepeatNestedData.snapshot, unit⟩

theorem headers_checked : checkUnitHeaders RepeatNestedData.snapshot =
    .ok (domains, headers, summaries) := rfl

theorem helpers_checked : checkUnitHelpers RepeatNestedData.snapshot domains summaries = .ok ordered := rfl

theorem protocols_checked :
    checkUnitProtocols RepeatNestedData.snapshot domains summaries headers ordered = .ok unit.protocols := rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets RepeatNestedData.snapshot).isOk = true := by decide +kernel

theorem effective_sites_checked :
    checkEffectiveProtocolSites RepeatNestedData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata RepeatNestedData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

theorem payload_linked : linkUnitPayload RepeatNestedData.snapshot ordered unit.protocols = .ok unit := rfl

/-- All declarations, callback trees and metadata phases of the original unit. -/
theorem kernel_admission : check RepeatNestedData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported RepeatNestedData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = RepeatNestedData.snapshot := imported.exactSubject

theorem run_member : runDefinition ∈ unit.protocols := List.mem_cons_self

theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl

/-- Complete original-to-checked association includes every nested callback. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ RepeatNestedData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders RepeatNestedData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol RepeatNestedData.snapshot domains summaries function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol RepeatNestedData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-- Every original protocol is admitted to one exact checked tree. -/
theorem complete_original_protocol (function : Zkc.Source.Structured.Function)
    (member : .function function ∈ RepeatNestedData.snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders RepeatNestedData.snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ unit.protocols ∧
        checkProtocol RepeatNestedData.snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ unit.protocols →
          checkProtocol RepeatNestedData.snapshot domains summaries function headers = .ok other →
            other = definition :=
  imported.protocolChecked member kind

end ZkcExamples.Structured.RepeatNestedViews
