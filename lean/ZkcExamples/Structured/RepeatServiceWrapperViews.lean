module

public import ZkcExamples.Structured.RepeatServiceWrapperData
public import ZkcExamples.Structured.RepeatServiceWrapperBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatServiceWrapperViews
open Zkc.Source Zkc.Source.Structured RepeatServiceWrapperBodies

set_option smartUnfolding false

def drawDefinition : CheckedProtocol where
  toProtocolSignature := drawSignature
  raw := drawBody.erase
  body := drawBody
  formed := drawBody.elaborate_erase

theorem draw_signature : drawDefinition.signature = drawSignature := rfl
theorem draw_raw : drawDefinition.raw = drawBody.erase := rfl
theorem draw_body : drawDefinition.body = drawBody := rfl

def runDefinition : CheckedProtocol where
  toProtocolSignature := runSignature
  raw := runBody.erase
  body := runBody
  formed := runBody.elaborate_erase

theorem run_signature : runDefinition.signature = runSignature := rfl
theorem run_raw : runDefinition.raw = runBody.erase := rfl
theorem run_body : runDefinition.body = runBody := rfl

def outerDefinition : CheckedProtocol where
  toProtocolSignature := outerSignature
  raw := outerBody.erase
  body := outerBody
  formed := outerBody.elaborate_erase

theorem outer_signature : outerDefinition.signature = outerSignature := rfl
theorem outer_raw : outerDefinition.raw = outerBody.erase := rfl
theorem outer_body : outerDefinition.body = outerBody := rfl

def definitions : List CheckedDefinition :=
  []

def ordered : List OrderedDefinition :=
  []

def headers : List ProtocolSignature := [outerSignature, runSignature, drawSignature]

def domains : List DomainSpec := []

def summaries : IdentitySummaries := []

def unit : UnitPayload where
  definitions := definitions
  protocols := [drawDefinition, runDefinition, outerDefinition]
  entryIndex := ⟨2, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨RepeatServiceWrapperData.snapshot, unit⟩

theorem headers_checked : checkUnitHeaders RepeatServiceWrapperData.snapshot =
    .ok (domains, headers, summaries) := rfl

theorem helpers_checked : checkUnitHelpers RepeatServiceWrapperData.snapshot domains summaries = .ok ordered := rfl

theorem protocols_checked :
    checkUnitProtocols RepeatServiceWrapperData.snapshot domains summaries headers ordered = .ok unit.protocols := rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets RepeatServiceWrapperData.snapshot).isOk = true := by decide +kernel

theorem effective_sites_checked :
    checkEffectiveProtocolSites RepeatServiceWrapperData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata RepeatServiceWrapperData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

theorem payload_linked : linkUnitPayload RepeatServiceWrapperData.snapshot ordered unit.protocols = .ok unit := rfl

/-- All declarations, callback trees and metadata phases of the original unit. -/
theorem kernel_admission : check RepeatServiceWrapperData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported RepeatServiceWrapperData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = RepeatServiceWrapperData.snapshot := imported.exactSubject

theorem draw_member : drawDefinition ∈ unit.protocols := List.mem_cons_self

theorem run_member : runDefinition ∈ unit.protocols := List.mem_cons_of_mem _ (List.mem_cons_self)

theorem outer_member : outerDefinition ∈ unit.protocols := List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem entry_selection : unit.entry = outerDefinition := rfl
theorem entry_signature : program.payload.entry.signature = outerSignature := rfl
theorem entry_raw : program.payload.entry.raw = outerBody.erase := rfl

/-- Complete original-to-checked association includes every nested callback. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ RepeatServiceWrapperData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders RepeatServiceWrapperData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol RepeatServiceWrapperData.snapshot domains summaries function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol RepeatServiceWrapperData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-- Every original protocol is admitted to one exact checked tree. -/
theorem complete_original_protocol (function : Zkc.Source.Structured.Function)
    (member : .function function ∈ RepeatServiceWrapperData.snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders RepeatServiceWrapperData.snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ unit.protocols ∧
        checkProtocol RepeatServiceWrapperData.snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ unit.protocols →
          checkProtocol RepeatServiceWrapperData.snapshot domains summaries function headers = .ok other →
            other = definition :=
  imported.protocolChecked member kind

end ZkcExamples.Structured.RepeatServiceWrapperViews
