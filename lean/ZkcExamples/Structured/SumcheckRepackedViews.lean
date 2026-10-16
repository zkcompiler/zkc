module

public import ZkcExamples.Structured.SumcheckReduceViews
public import ZkcExamples.Structured.SumcheckRepackedData
public import ZkcExamples.Structured.SumcheckRepackedBodies

@[expose] public section

/-! Complete checked payload of the repacked Reduction export. Every helper
and the child Reduce reuse the retained Reduction's checked definitions; only
the root is new. Admission is checked against the repacked snapshot itself. -/
namespace ZkcExamples.Structured.SumcheckRepackedViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

def runDefinition : CheckedProtocol where
  toProtocolSignature := SumcheckRepackedBodies.runSignature
  raw := SumcheckRepackedBodies.runBody.erase
  body := SumcheckRepackedBodies.runBody
  formed := SumcheckRepackedBodies.runBody.elaborate_erase

theorem run_signature : runDefinition.signature = SumcheckRepackedBodies.runSignature := rfl
theorem run_raw : runDefinition.raw = SumcheckRepackedBodies.runBody.erase := rfl
theorem run_body : runDefinition.body = SumcheckRepackedBodies.runBody := rfl

def headers : List ProtocolSignature :=
  [SumcheckRepackedBodies.runSignature, SumcheckReduceBodies.reduceSignature]

def unit : UnitPayload where
  definitions := SumcheckReduceViews.definitions
  protocols := [SumcheckReduceViews.reduceDefinition, runDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨SumcheckRepackedData.snapshot, unit⟩

set_option maxRecDepth 1024 in
theorem headers_checked : checkUnitHeaders SumcheckRepackedData.snapshot =
    .ok (SumcheckReduceViews.domains, headers, SumcheckReduceViews.summaries) := rfl

set_option maxRecDepth 1024 in
theorem helpers_checked : checkUnitHelpers SumcheckRepackedData.snapshot SumcheckReduceViews.domains
    SumcheckReduceViews.summaries = .ok SumcheckReduceViews.ordered := rfl

theorem run_checked :
    checkProtocol SumcheckRepackedData.snapshot SumcheckReduceViews.domains SumcheckReduceViews.summaries
      SumcheckRepackedData.snapshot.protocolFunctions[0] headers = .ok runDefinition := rfl

-- The complete original Reduce callback exceeds default depth, as for the
-- retained Reduction; this local kernel check uses depth 1024.
set_option maxRecDepth 1024 in
theorem reduce_checked :
    checkProtocol SumcheckRepackedData.snapshot SumcheckReduceViews.domains SumcheckReduceViews.summaries
      SumcheckRepackedData.snapshot.protocolFunctions[1] headers = .ok SumcheckReduceViews.reduceDefinition := rfl

theorem protocols_checked :
    checkUnitProtocols SumcheckRepackedData.snapshot SumcheckReduceViews.domains SumcheckReduceViews.summaries
      headers SumcheckReduceViews.ordered = .ok unit.protocols := by
  unfold checkUnitProtocols
  rw [show SumcheckRepackedData.snapshot.protocolFunctions =
    [SumcheckRepackedData.snapshot.protocolFunctions[0], SumcheckRepackedData.snapshot.protocolFunctions[1]] from rfl]
  simp only [List.mapM_cons, List.mapM_nil, run_checked, reduce_checked, bind, Except.bind,
    pure, Except.pure]
  rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets SumcheckRepackedData.snapshot).isOk = true := by decide +kernel

theorem effective_sites_checked :
    checkEffectiveProtocolSites SumcheckRepackedData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata SumcheckRepackedData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

private theorem link_literal (snapshot : Snapshot) (ordered : List OrderedDefinition)
    (payload : UnitPayload)
    (definitionsEq : ordered.map (·.definition) = payload.definitions)
    (entryEq : payload.protocols.findIdx (·.name == snapshot.entry) = payload.entryIndex.val) :
    linkUnitPayload snapshot ordered payload.protocols = .ok payload := by
  unfold linkUnitPayload
  rw [definitionsEq]
  simp only [payload.realizationClosed, payload.mapClosed, payload.linked,
    payload.protocolsLinked, entryEq, payload.entryIndex.isLt, ↓reduceDIte]
  split
  · rename_i code unavailable
    have available := payload.available
    rw [unavailable] at available
    cases available
  · rfl

theorem payload_linked :
    linkUnitPayload SumcheckRepackedData.snapshot SumcheckReduceViews.ordered unit.protocols = .ok unit :=
  link_literal _ _ _ rfl rfl

/-- All declarations, callback trees and metadata phases of the repacked unit. -/
theorem kernel_admission : check SumcheckRepackedData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported SumcheckRepackedData.snapshot := ⟨program, kernel_admission⟩

theorem reduce_member : SumcheckReduceViews.reduceDefinition ∈ unit.protocols := List.mem_cons_self

theorem run_member : runDefinition ∈ unit.protocols := by structured_mem

theorem entry_selection : unit.entry = runDefinition := rfl

/-- The two exports differ in source digest, so they are distinct subjects
although their root declaration symbol is the same. -/
theorem distinct_subjects :
    SumcheckRepackedData.snapshot.source ≠ SumcheckReduceData.snapshot.source ∧
    SumcheckRepackedData.snapshot.entry = SumcheckReduceData.snapshot.entry := by
  constructor
  · decide
  · rfl

end ZkcExamples.Structured.SumcheckRepackedViews
