module

public import Zkc.Source.Structured.Association
public import ZkcExamples.Structured.SumcheckReduceData
public import ZkcExamples.Structured.SumcheckReduceBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.SumcheckReduceViews
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

set_option smartUnfolding false

def lessDefinition : CheckedDefinition :=
  ⟨lessHelper.name, lessHelper.kind, lessHelper.inputs, lessHelper.outputs,
    lessBody.erase, lessBody, lessBody.elaborate_erase⟩

theorem less_raw : lessDefinition.raw = lessBody.erase := rfl
theorem less_body : lessDefinition.body = lessBody := rfl

def rowsDefinition : CheckedDefinition :=
  ⟨rowsHelper.name, rowsHelper.kind, rowsHelper.inputs, rowsHelper.outputs,
    rowsBody.erase, rowsBody, rowsBody.elaborate_erase⟩

theorem rows_raw : rowsDefinition.raw = rowsBody.erase := rfl
theorem rows_body : rowsDefinition.body = rowsBody := rfl

def shapeDefinition : CheckedDefinition :=
  ⟨shapeHelper.name, shapeHelper.kind, shapeHelper.inputs, shapeHelper.outputs,
    shapeBody.erase, shapeBody, shapeBody.elaborate_erase⟩

theorem shape_raw : shapeDefinition.raw = shapeBody.erase := rfl
theorem shape_body : shapeDefinition.body = shapeBody := rfl

def tableDefinition : CheckedDefinition :=
  ⟨tableHelper.name, tableHelper.kind, tableHelper.inputs, tableHelper.outputs,
    tableBody.erase, tableBody, tableBody.elaborate_erase⟩

theorem table_raw : tableDefinition.raw = tableBody.erase := rfl
theorem table_body : tableDefinition.body = tableBody := rfl

def widthDefinition : CheckedDefinition :=
  ⟨widthHelper.name, widthHelper.kind, widthHelper.inputs, widthHelper.outputs,
    widthBody.erase, widthBody, widthBody.elaborate_erase⟩

theorem width_raw : widthDefinition.raw = widthBody.erase := rfl
theorem width_body : widthDefinition.body = widthBody := rfl

def variablesDefinition : CheckedDefinition :=
  ⟨variablesHelper.name, variablesHelper.kind, variablesHelper.inputs, variablesHelper.outputs,
    variablesBody.erase, variablesBody, variablesBody.elaborate_erase⟩

theorem variables_raw : variablesDefinition.raw = variablesBody.erase := rfl
theorem variables_body : variablesDefinition.body = variablesBody := rfl

def emptyDefinition : CheckedDefinition :=
  ⟨emptyHelper.name, emptyHelper.kind, emptyHelper.inputs, emptyHelper.outputs,
    emptyBody.erase, emptyBody, emptyBody.elaborate_erase⟩

theorem empty_raw : emptyDefinition.raw = emptyBody.erase := rfl
theorem empty_body : emptyDefinition.body = emptyBody := rfl

def halvesDefinition : CheckedDefinition :=
  ⟨halvesHelper.name, halvesHelper.kind, halvesHelper.inputs, halvesHelper.outputs,
    halvesBody.erase, halvesBody, halvesBody.elaborate_erase⟩

theorem halves_raw : halvesDefinition.raw = halvesBody.erase := rfl
theorem halves_body : halvesDefinition.body = halvesBody := rfl

def sumsDefinition : CheckedDefinition :=
  ⟨sumsHelper.name, sumsHelper.kind, sumsHelper.inputs, sumsHelper.outputs,
    sumsBody.erase, sumsBody, sumsBody.elaborate_erase⟩

theorem sums_raw : sumsDefinition.raw = sumsBody.erase := rfl
theorem sums_body : sumsDefinition.body = sumsBody := rfl

def interpolateDefinition : CheckedDefinition :=
  ⟨interpolateHelper.name, interpolateHelper.kind, interpolateHelper.inputs, interpolateHelper.outputs,
    interpolateBody.erase, interpolateBody, interpolateBody.elaborate_erase⟩

theorem interpolate_raw : interpolateDefinition.raw = interpolateBody.erase := rfl
theorem interpolate_body : interpolateDefinition.body = interpolateBody := rfl

def mapDefinition : CheckedDefinition :=
  ⟨mapHelper.name, mapHelper.kind, mapHelper.inputs, mapHelper.outputs,
    mapBody.erase, mapBody, mapBody.elaborate_erase⟩

theorem map_raw : mapDefinition.raw = mapBody.erase := rfl
theorem map_body : mapDefinition.body = mapBody := rfl

def firstDefinition : CheckedDefinition :=
  ⟨firstHelper.name, firstHelper.kind, firstHelper.inputs, firstHelper.outputs,
    firstBody.erase, firstBody, firstBody.elaborate_erase⟩

theorem first_raw : firstDefinition.raw = firstBody.erase := rfl
theorem first_body : firstDefinition.body = firstBody := rfl

def appendDefinition : CheckedDefinition :=
  ⟨appendHelper.name, appendHelper.kind, appendHelper.inputs, appendHelper.outputs,
    appendBody.erase, appendBody, appendBody.elaborate_erase⟩

theorem append_raw : appendDefinition.raw = appendBody.erase := rfl
theorem append_body : appendDefinition.body = appendBody := rfl

def valuesDefinition : CheckedDefinition :=
  ⟨valuesHelper.name, valuesHelper.kind, valuesHelper.inputs, valuesHelper.outputs,
    valuesBody.erase, valuesBody, valuesBody.elaborate_erase⟩

theorem values_raw : valuesDefinition.raw = valuesBody.erase := rfl
theorem values_body : valuesDefinition.body = valuesBody := rfl

def reduceDefinition : CheckedProtocol where
  toProtocolSignature := reduceSignature
  raw := reduceBody.erase
  body := reduceBody
  formed := reduceBody.elaborate_erase

theorem reduce_signature : reduceDefinition.signature = reduceSignature := rfl
theorem reduce_raw : reduceDefinition.raw = reduceBody.erase := rfl
theorem reduce_body : reduceDefinition.body = reduceBody := rfl

def runDefinition : CheckedProtocol where
  toProtocolSignature := runSignature
  raw := runBody.erase
  body := runBody
  formed := runBody.elaborate_erase

theorem run_signature : runDefinition.signature = runSignature := rfl
theorem run_raw : runDefinition.raw = runBody.erase := rfl
theorem run_body : runDefinition.body = runBody := rfl

def sumAddDefinition : CheckedDefinition :=
  ⟨SumcheckRelationContract.addHelper.name, SumcheckRelationContract.addHelper.kind,
    SumcheckRelationContract.addHelper.inputs, SumcheckRelationContract.addHelper.outputs,
    SumcheckRelationContract.addBody.erase, SumcheckRelationContract.addBody,
    SumcheckRelationContract.addBody.elaborate_erase⟩

def sumStepDefinition : CheckedDefinition :=
  ⟨SumcheckRelationContract.foldSpec.stepHelper.name, SumcheckRelationContract.foldSpec.stepHelper.kind,
    SumcheckRelationContract.foldSpec.stepHelper.inputs, SumcheckRelationContract.foldSpec.stepHelper.outputs,
    SumcheckRelationContract.stepBody.erase, SumcheckRelationContract.stepBody,
    SumcheckRelationContract.stepBody.elaborate_erase⟩

def sumTotalDefinition : CheckedDefinition :=
  ⟨SumcheckRelationContract.totalHelper.name, SumcheckRelationContract.totalHelper.kind,
    SumcheckRelationContract.totalHelper.inputs, SumcheckRelationContract.totalHelper.outputs,
    SumcheckRelationContract.totalBody.erase, SumcheckRelationContract.totalBody,
    SumcheckRelationContract.totalBody.elaborate_erase⟩

def tableSumFormulaDefinition : CheckedDefinition :=
  ⟨SumcheckRelationContract.tableSumHelper.name, SumcheckRelationContract.tableSumHelper.kind,
    SumcheckRelationContract.tableSumHelper.inputs, SumcheckRelationContract.tableSumHelper.outputs,
    SumcheckRelationContract.tableSumBody.erase, SumcheckRelationContract.tableSumBody,
    SumcheckRelationContract.tableSumBody.elaborate_erase⟩

def definitions : List CheckedDefinition :=
  [lessDefinition, rowsDefinition, shapeDefinition, tableDefinition, valuesDefinition, sumAddDefinition, sumStepDefinition, sumTotalDefinition, tableSumFormulaDefinition, widthDefinition, variablesDefinition, emptyDefinition, halvesDefinition, sumsDefinition, interpolateDefinition, mapDefinition, firstDefinition, appendDefinition]

def ordered : List OrderedDefinition :=
  [⟨lessDefinition, 0⟩, ⟨rowsDefinition, 1⟩, ⟨shapeDefinition, 2⟩, ⟨tableDefinition, 3⟩, ⟨valuesDefinition, 0⟩, ⟨sumAddDefinition, 0⟩, ⟨sumStepDefinition, 1⟩, ⟨sumTotalDefinition, 2⟩, ⟨tableSumFormulaDefinition, 3⟩, ⟨widthDefinition, 0⟩, ⟨variablesDefinition, 0⟩, ⟨emptyDefinition, 0⟩, ⟨halvesDefinition, 1⟩, ⟨sumsDefinition, 2⟩, ⟨interpolateDefinition, 0⟩, ⟨mapDefinition, 1⟩, ⟨firstDefinition, 2⟩, ⟨appendDefinition, 0⟩]

def headers : List ProtocolSignature := [runSignature, reduceSignature]

def domains : List DomainSpec := [SumcheckRelationContract.foldSpec.domain]

def summaries : IdentitySummaries := [⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", [none]⟩, ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", [some 1]⟩, ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", [some 2]⟩, ⟨"finite_zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e_s1_body", [none]⟩, ⟨"zkl_3fc17a64a5bb6e75192d0a1362e9954f0d434a10d0f93e319db6b516835a1005", [none]⟩, ⟨"zkf_654a0e58b11e83f398996b9e830df00890bec0f8dc08a65c5750d6d9c759b643", [none]⟩, ⟨"zkl_487d3a841d53a741e8ad1c8bce36b7f95af6b76cba6787c9779c9253587ea90e", [none]⟩, ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", [some 0]⟩]

def unit : UnitPayload where
  definitions := definitions
  protocols := [reduceDefinition, runDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨SumcheckReduceData.snapshot, unit⟩

set_option maxRecDepth 1024 in
theorem headers_checked : checkUnitHeaders SumcheckReduceData.snapshot =
    .ok (domains, headers, summaries) := rfl

set_option maxRecDepth 1024 in
theorem helpers_checked : checkUnitHelpers SumcheckReduceData.snapshot domains summaries = .ok ordered := rfl

theorem run_checked :
    checkProtocol SumcheckReduceData.snapshot domains summaries
      SumcheckReduceData.snapshot.protocolFunctions[0] headers = .ok runDefinition := rfl

-- The complete original Reduce callback still exceeds default depth after
-- factoring the two source checks; this local kernel check uses depth 1024.
set_option maxRecDepth 1024 in
theorem reduce_checked :
    checkProtocol SumcheckReduceData.snapshot domains summaries
      SumcheckReduceData.snapshot.protocolFunctions[1] headers = .ok reduceDefinition := rfl

/-- Separate source checks from dependency ordering of the two complete trees. -/
theorem protocols_checked :
    checkUnitProtocols SumcheckReduceData.snapshot domains summaries headers ordered = .ok unit.protocols := by
  unfold checkUnitProtocols
  rw [show SumcheckReduceData.snapshot.protocolFunctions =
    [SumcheckReduceData.snapshot.protocolFunctions[0], SumcheckReduceData.snapshot.protocolFunctions[1]] from rfl]
  simp only [List.mapM_cons, List.mapM_nil, run_checked, reduce_checked, bind, Except.bind,
    pure, Except.pure]
  rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets SumcheckReduceData.snapshot).isOk = true := by decide +kernel

theorem effective_sites_checked :
    checkEffectiveProtocolSites SumcheckReduceData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata SumcheckReduceData.snapshot = .ok () :=
  checkApplicationMetadata_of_checks native_metadata_checked effective_sites_checked

/-- Linking uses the candidate's already checked obligations, without re-running
availability or preparation normalization in this final composition. -/
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

theorem payload_linked : linkUnitPayload SumcheckReduceData.snapshot ordered unit.protocols = .ok unit :=
  link_literal _ _ _ rfl rfl

/-- All declarations, callback trees and metadata phases of the original unit. -/
theorem kernel_admission : check SumcheckReduceData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported SumcheckReduceData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = SumcheckReduceData.snapshot := imported.exactSubject

theorem reduce_member : reduceDefinition ∈ unit.protocols := List.mem_cons_self

theorem run_member : runDefinition ∈ unit.protocols := by structured_mem

theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl

/-- Complete original-to-checked association includes every nested callback. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ SumcheckReduceData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders SumcheckReduceData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol SumcheckReduceData.snapshot domains summaries function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol SumcheckReduceData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-- Every original protocol is admitted to one exact checked tree. -/
theorem complete_original_protocol (function : Zkc.Source.Structured.Function)
    (member : .function function ∈ SumcheckReduceData.snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders SumcheckReduceData.snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ unit.protocols ∧
        checkProtocol SumcheckReduceData.snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ unit.protocols →
          checkProtocol SumcheckReduceData.snapshot domains summaries function headers = .ok other →
            other = definition :=
  imported.protocolChecked member kind

end ZkcExamples.Structured.SumcheckReduceViews
