module

public import ZkcExamples.Structured.ApplicationWrapperData
public import ZkcExamples.Structured.ServiceOrderViews

@[expose] public section

/-! Complete retained wrapper source with one exact admission theorem. Draw and
Run reuse their literal bodies; the wrapper retains its own complete snapshot. -/
namespace ZkcExamples.Structured.ApplicationWrapperViews
open Zkc.Source Zkc.Source.Structured ServiceOrderBodies

def outerSignature : ProtocolSignature where
  name := "s6h73616d706c655h4f75746572"
  roles := roles
  inputs := inputTypes
  outputs := resultTypes
  inputScopes := [[1], [1], [1]]
  outputScopes := [[0], [1]]

def outerBody : Region protocolDialect inputTypes resultTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.protocolApply runSignature [0, 1] "s0")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here (.cons (.there .here) .nil))

def outerDefinition : CheckedProtocol where
  toProtocolSignature := outerSignature
  raw := outerBody.erase
  body := outerBody
  formed := outerBody.elaborate_erase

set_option smartUnfolding false

def unit : UnitPayload where
  definitions := []
  protocols := [ServiceOrderViews.drawDefinition, ServiceOrderViews.runDefinition, outerDefinition]
  entryIndex := ⟨2, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := rfl
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨ApplicationWrapperData.snapshot, unit⟩

private theorem headers_checked :
    checkUnitHeaders ApplicationWrapperData.snapshot =
      .ok ([], [outerSignature, runSignature, drawSignature], []) := rfl

private theorem helpers_checked :
    checkUnitHelpers ApplicationWrapperData.snapshot [] [] = .ok [] := rfl

private theorem protocols_checked :
    checkUnitProtocols ApplicationWrapperData.snapshot [] []
      [outerSignature, runSignature, drawSignature] [] = .ok unit.protocols := rfl

private theorem native_budgets_checked :
    (checkNativeApplicationBudgets ApplicationWrapperData.snapshot).isOk = true := by
  decide +kernel

private theorem effective_sites_checked :
    checkEffectiveProtocolSites ApplicationWrapperData.snapshot = .ok () := rfl

private theorem metadata_checked :
    checkApplicationMetadata ApplicationWrapperData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_budgets_checked effective_sites_checked

private theorem payload_linked :
    linkUnitPayload ApplicationWrapperData.snapshot [] unit.protocols = .ok unit := rfl

/-- The complete retained wrapper passes every canonical admission phase. -/
theorem kernel_admission : check ApplicationWrapperData.snapshot = .ok program :=
  check_parts _ _ (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported ApplicationWrapperData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = ApplicationWrapperData.snapshot := imported.exactSubject
theorem outer_signature : outerDefinition.signature = outerSignature := rfl
theorem outer_raw : outerDefinition.raw = outerBody.erase := rfl
theorem draw_member : ServiceOrderViews.drawDefinition ∈ unit.protocols := List.mem_cons_self
theorem run_member : ServiceOrderViews.runDefinition ∈ unit.protocols :=
  List.mem_cons_of_mem _ List.mem_cons_self
theorem outer_member : outerDefinition ∈ unit.protocols :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
theorem entry_selection : unit.entry = outerDefinition := rfl
theorem entry_signature : program.payload.entry.signature = outerSignature := rfl
theorem entry_raw : program.payload.entry.raw = outerBody.erase := rfl

end ZkcExamples.Structured.ApplicationWrapperViews
