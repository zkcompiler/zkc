module

public import ZkcExamples.Structured.ServiceOrderData
public import ZkcExamples.Structured.ServiceOrderBodies

@[expose] public section

/-! Complete original-source admission with explicit normalized candidates.
The original source order is Run, Draw; the linked order is Draw, Run. -/
namespace ZkcExamples.Structured.ServiceOrderViews
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies

set_option smartUnfolding false

def drawDefinition : CheckedProtocol where
  toProtocolSignature := drawSignature
  raw := drawBody.erase
  body := drawBody
  formed := drawBody.elaborate_erase

def runDefinition : CheckedProtocol where
  toProtocolSignature := runSignature
  raw := runBody.erase
  body := runBody
  formed := runBody.elaborate_erase

def unit : UnitPayload where
  definitions := []
  protocols := [drawDefinition, runDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨ServiceOrderData.snapshot, unit⟩

private theorem headers_checked :
    checkUnitHeaders ServiceOrderData.snapshot = .ok ([], [runSignature, drawSignature], []) := rfl

private theorem helpers_checked :
    checkUnitHelpers ServiceOrderData.snapshot [] [] = .ok [] := rfl

private theorem protocols_checked :
    checkUnitProtocols ServiceOrderData.snapshot [] [] [runSignature, drawSignature] [] =
      .ok [drawDefinition, runDefinition] := by
  rfl

private theorem native_budgets_checked :
    (checkNativeApplicationBudgets ServiceOrderData.snapshot).isOk = true := by
  decide +kernel

private theorem effective_sites_checked :
    checkEffectiveProtocolSites ServiceOrderData.snapshot = .ok () := by
  rfl

private theorem metadata_checked :
    checkApplicationMetadata ServiceOrderData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_budgets_checked effective_sites_checked

private theorem payload_linked :
    linkUnitPayload ServiceOrderData.snapshot [] [drawDefinition, runDefinition] = .ok unit := rfl

/-- All original declarations and admission phases participate in this equality. -/
theorem kernel_admission : check ServiceOrderData.snapshot = .ok program :=
  check_parts _ _ (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported ServiceOrderData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = ServiceOrderData.snapshot := imported.exactSubject
theorem draw_signature : drawDefinition.signature = drawSignature := rfl
theorem run_signature : runDefinition.signature = runSignature := rfl
theorem draw_raw : drawDefinition.raw = drawBody.erase := rfl
theorem run_raw : runDefinition.raw = runBody.erase := rfl
theorem draw_member : drawDefinition ∈ unit.protocols := List.mem_cons_self
theorem run_member : runDefinition ∈ unit.protocols :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl

end ZkcExamples.Structured.ServiceOrderViews
