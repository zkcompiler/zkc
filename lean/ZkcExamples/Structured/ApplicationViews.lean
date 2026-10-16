module

public import ZkcExamples.Structured.ApplicationData
public import ZkcExamples.Structured.ApplicationBodies

public section

/-! One explicit checked candidate and one complete original admission proof.
Named signature, membership and erasure equalities keep downstream proof types
independent of repeated normalization of whole-unit admission. -/
namespace ZkcExamples.Structured.ApplicationViews
open Zkc.Source Zkc.Source.Structured ApplicationBodies

set_option smartUnfolding false

@[expose] def stepDefinition : CheckedProtocol where
  name := stepSignature.name
  roles := stepSignature.roles
  inputs := pairTypes
  outputs := pairTypes
  inputScopes := stepSignature.inputScopes
  outputScopes := stepSignature.outputScopes
  raw := stepBody.erase
  body := stepBody
  formed := stepBody.elaborate_erase

@[expose] def observeDefinition : CheckedProtocol where
  name := observeSignature.name
  roles := observeSignature.roles
  inputs := []
  outputs := []
  inputScopes := []
  outputScopes := []
  raw := observeBody.erase
  body := observeBody
  formed := observeBody.elaborate_erase

@[expose] def segmentDefinition : CheckedProtocol where
  name := segmentSignature.name
  roles := segmentSignature.roles
  inputs := pairTypes
  outputs := pairTypes
  inputScopes := segmentSignature.inputScopes
  outputScopes := segmentSignature.outputScopes
  raw := segmentBody.erase
  body := segmentBody
  formed := segmentBody.elaborate_erase

@[expose] def runDefinition : CheckedProtocol where
  name := runSignature.name
  roles := runSignature.roles
  inputs := pairTypes
  outputs := pairTypes
  inputScopes := runSignature.inputScopes
  outputScopes := runSignature.outputScopes
  raw := runBody.erase
  body := runBody
  formed := runBody.elaborate_erase

@[expose] def unit : UnitPayload where
  definitions := []
  protocols := [stepDefinition, observeDefinition, segmentDefinition, runDefinition]
  entryIndex := ⟨3, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := by rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

@[expose] def program : Program := ⟨ApplicationData.snapshot, unit⟩

@[expose] def headers : List ProtocolSignature :=
  [runSignature, segmentSignature, stepSignature, observeSignature]

theorem headers_checked : checkUnitHeaders ApplicationData.snapshot = .ok ([], headers, []) := rfl

theorem helpers_checked : checkUnitHelpers ApplicationData.snapshot [] [] = .ok [] := rfl

theorem protocols_checked :
    checkUnitProtocols ApplicationData.snapshot [] [] headers [] = .ok unit.protocols := rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets ApplicationData.snapshot).isOk = true := by decide +kernel

private theorem effective_sites_checked :
    checkEffectiveProtocolSites ApplicationData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata ApplicationData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

theorem payload_linked : linkUnitPayload ApplicationData.snapshot [] unit.protocols = .ok unit := rfl

/-- Admission covers the complete unchanged source, including dormant declarations.
The canonical phases are normalized once; dependent client types use the candidate. -/
theorem kernel_admission : check ApplicationData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

@[expose] def imported : Imported ApplicationData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = ApplicationData.snapshot := imported.exactSubject

theorem step_signature : stepDefinition.signature = stepSignature := rfl
theorem observe_signature : observeDefinition.signature = observeSignature := rfl
theorem segment_signature : segmentDefinition.signature = segmentSignature := rfl
theorem run_signature : runDefinition.signature = runSignature := rfl

theorem step_raw : stepDefinition.raw = stepBody.erase := rfl
theorem observe_raw : observeDefinition.raw = observeBody.erase := rfl
theorem segment_raw : segmentDefinition.raw = segmentBody.erase := rfl
theorem run_raw : runDefinition.raw = runBody.erase := rfl

theorem step_member : stepDefinition ∈ unit.protocols := List.mem_cons_self
theorem observe_member : observeDefinition ∈ unit.protocols :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem segment_member : segmentDefinition ∈ unit.protocols :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem run_member : runDefinition ∈ unit.protocols :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl

end ZkcExamples.Structured.ApplicationViews
