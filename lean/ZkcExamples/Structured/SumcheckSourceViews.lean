module

public import Zkc.Source.Structured.Association
public import ZkcExamples.Structured.SumcheckSourceData
public import ZkcExamples.Structured.SumcheckSourceBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.SumcheckSourceViews
open Zkc.Source Zkc.Source.Structured SumcheckSourceBodies

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

def stepDefinition : CheckedDefinition :=
  ⟨stepHelper.name, stepHelper.kind, stepHelper.inputs, stepHelper.outputs,
    stepBody.erase, stepBody, stepBody.elaborate_erase⟩

theorem step_raw : stepDefinition.raw = stepBody.erase := rfl
theorem step_body : stepDefinition.body = stepBody := rfl

def foldStepDefinition : CheckedDefinition :=
  ⟨foldStepHelper.name, foldStepHelper.kind, foldStepHelper.inputs, foldStepHelper.outputs,
    foldStepBody.erase, foldStepBody, foldStepBody.elaborate_erase⟩

theorem foldStep_raw : foldStepDefinition.raw = foldStepBody.erase := rfl
theorem foldStep_body : foldStepDefinition.body = foldStepBody := rfl

def foldDefinition : CheckedDefinition :=
  ⟨foldHelper.name, foldHelper.kind, foldHelper.inputs, foldHelper.outputs,
    foldBody.erase, foldBody, foldBody.elaborate_erase⟩

theorem fold_raw : foldDefinition.raw = foldBody.erase := rfl
theorem fold_body : foldDefinition.body = foldBody := rfl

def foldWrapperDefinition : CheckedDefinition :=
  ⟨foldWrapperHelper.name, foldWrapperHelper.kind, foldWrapperHelper.inputs, foldWrapperHelper.outputs,
    foldWrapperBody.erase, foldWrapperBody, foldWrapperBody.elaborate_erase⟩

theorem foldWrapper_raw : foldWrapperDefinition.raw = foldWrapperBody.erase := rfl
theorem foldWrapper_body : foldWrapperDefinition.body = foldWrapperBody := rfl

def prefixDefinition : CheckedDefinition :=
  ⟨prefixHelper.name, prefixHelper.kind, prefixHelper.inputs, prefixHelper.outputs,
    prefixBody.erase, prefixBody, prefixBody.elaborate_erase⟩

theorem prefix_raw : prefixDefinition.raw = prefixBody.erase := rfl
theorem prefix_body : prefixDefinition.body = prefixBody := rfl

def valuesDefinition : CheckedDefinition :=
  ⟨valuesHelper.name, valuesHelper.kind, valuesHelper.inputs, valuesHelper.outputs,
    valuesBody.erase, valuesBody, valuesBody.elaborate_erase⟩

theorem values_raw : valuesDefinition.raw = valuesBody.erase := rfl
theorem values_body : valuesDefinition.body = valuesBody := rfl

def valuesRealizationDefinition : CheckedDefinition :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.kind, valuesRealizationHelper.inputs, valuesRealizationHelper.outputs,
    valuesRealizationBody.erase, valuesRealizationBody, valuesRealizationBody.elaborate_erase⟩

theorem valuesRealization_raw : valuesRealizationDefinition.raw = valuesRealizationBody.erase := rfl
theorem valuesRealization_body : valuesRealizationDefinition.body = valuesRealizationBody := rfl

def checkTableDefinition : CheckedDefinition :=
  ⟨checkTableHelper.name, checkTableHelper.kind, checkTableHelper.inputs, checkTableHelper.outputs,
    checkTableBody.erase, checkTableBody, checkTableBody.elaborate_erase⟩

theorem checkTable_raw : checkTableDefinition.raw = checkTableBody.erase := rfl
theorem checkTable_body : checkTableDefinition.body = checkTableBody := rfl

def checkDefinition : CheckedDefinition :=
  ⟨checkHelper.name, checkHelper.kind, checkHelper.inputs, checkHelper.outputs,
    checkBody.erase, checkBody, checkBody.elaborate_erase⟩

theorem check_raw : checkDefinition.raw = checkBody.erase := rfl
theorem check_body : checkDefinition.body = checkBody := rfl

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

def definitions : List CheckedDefinition :=
  [lessDefinition, rowsDefinition, shapeDefinition, tableDefinition, widthDefinition, variablesDefinition, emptyDefinition, halvesDefinition, sumsDefinition, interpolateDefinition, mapDefinition, firstDefinition, appendDefinition, stepDefinition, foldStepDefinition, foldDefinition, foldWrapperDefinition, prefixDefinition, valuesDefinition, valuesRealizationDefinition, checkTableDefinition, checkDefinition]

def ordered : List OrderedDefinition :=
  [⟨lessDefinition, 0⟩, ⟨rowsDefinition, 1⟩, ⟨shapeDefinition, 2⟩, ⟨tableDefinition, 3⟩, ⟨widthDefinition, 0⟩, ⟨variablesDefinition, 0⟩, ⟨emptyDefinition, 0⟩, ⟨halvesDefinition, 1⟩, ⟨sumsDefinition, 2⟩, ⟨interpolateDefinition, 0⟩, ⟨mapDefinition, 1⟩, ⟨firstDefinition, 2⟩, ⟨appendDefinition, 0⟩, ⟨stepDefinition, 3⟩, ⟨foldStepDefinition, 4⟩, ⟨foldDefinition, 5⟩, ⟨foldWrapperDefinition, 6⟩, ⟨prefixDefinition, 7⟩, ⟨valuesDefinition, 0⟩, ⟨valuesRealizationDefinition, 1⟩, ⟨checkTableDefinition, 8⟩, ⟨checkDefinition, 9⟩]

def headers : List ProtocolSignature := [runSignature, reduceSignature]

def domains : List DomainSpec := [MapPrefixBodies.foldSpec.domain]

def summaries : IdentitySummaries := [⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33", [some 0]⟩, ⟨"zkl_42fb42b1768a8f815f169ffa0a26ad784504be546e5429d75560cbdb446518b5", [none]⟩, ⟨"zkl_b68fce120956aac980e5e44b80eb16c2f94dc93ad6a8f6349ef7e1b217505a94", [some 1]⟩, ⟨"zkl_d1a35db6ce1dd3faf44d81ee2d033b68f50349356a0525683219ffff3d77f275", [some 2]⟩]

def unit : UnitPayload where
  definitions := definitions
  protocols := [reduceDefinition, runDefinition]
  entryIndex := ⟨1, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨SumcheckSourceData.snapshot, unit⟩

theorem headers_checked : checkUnitHeaders SumcheckSourceData.snapshot =
    .ok (domains, headers, summaries) := rfl

theorem helpers_checked : checkUnitHelpers SumcheckSourceData.snapshot domains summaries = .ok ordered := rfl

theorem run_checked :
    checkProtocol SumcheckSourceData.snapshot domains summaries
      SumcheckSourceData.snapshot.protocolFunctions[0] headers = .ok runDefinition := rfl

-- The complete original Reduce callback still exceeds default depth after
-- factoring the two source checks; this local kernel check uses depth 1024.
set_option maxRecDepth 1024 in
theorem reduce_checked :
    checkProtocol SumcheckSourceData.snapshot domains summaries
      SumcheckSourceData.snapshot.protocolFunctions[1] headers = .ok reduceDefinition := rfl

/-- Separate source checks from dependency ordering of the two complete trees. -/
theorem protocols_checked :
    checkUnitProtocols SumcheckSourceData.snapshot domains summaries headers ordered = .ok unit.protocols := by
  unfold checkUnitProtocols
  rw [show SumcheckSourceData.snapshot.protocolFunctions =
    [SumcheckSourceData.snapshot.protocolFunctions[0], SumcheckSourceData.snapshot.protocolFunctions[1]] from rfl]
  simp only [List.mapM_cons, List.mapM_nil, run_checked, reduce_checked, bind, Except.bind,
    pure, Except.pure]
  rfl

theorem native_metadata_checked :
    (checkNativeApplicationBudgets SumcheckSourceData.snapshot).isOk = true := by decide +kernel

-- Full-source recursive effective-site checking also exceeds default depth
-- after source-check factoring; this local kernel equality uses depth 1024.
set_option maxRecDepth 1024 in
theorem effective_sites_checked :
    checkEffectiveProtocolSites SumcheckSourceData.snapshot = .ok () := rfl

theorem metadata_checked : checkApplicationMetadata SumcheckSourceData.snapshot = .ok () :=
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

theorem payload_linked : linkUnitPayload SumcheckSourceData.snapshot ordered unit.protocols = .ok unit :=
  link_literal _ _ _ rfl rfl

/-- All declarations, callback trees and metadata phases of the original unit. -/
theorem kernel_admission : check SumcheckSourceData.snapshot = .ok program :=
  check_parts _ unit (check_payload_of_phases headers_checked helpers_checked
    protocols_checked metadata_checked payload_linked)

def imported : Imported SumcheckSourceData.snapshot := ⟨program, kernel_admission⟩

theorem exact_subject : program.snapshot = SumcheckSourceData.snapshot := imported.exactSubject

theorem reduce_member : reduceDefinition ∈ unit.protocols := List.mem_cons_self

theorem run_member : runDefinition ∈ unit.protocols := by structured_mem

theorem entry_selection : unit.entry = runDefinition := rfl
theorem entry_signature : program.payload.entry.signature = runSignature := rfl
theorem entry_raw : program.payload.entry.raw = runBody.erase := rfl

/-- Complete original-to-checked association includes every nested callback. -/
theorem complete_protocol_source (definition : CheckedProtocol)
    (member : definition ∈ unit.protocols) :
    ∃ function domains signatures summaries,
      .function function ∈ SumcheckSourceData.snapshot.definitions ∧
      function.kind = .protocol ∧
      checkUnitHeaders SumcheckSourceData.snapshot = .ok (domains, signatures, summaries) ∧
      checkProtocol SumcheckSourceData.snapshot domains summaries function signatures = .ok definition ∧
      resolveProtocolSignature function = .ok definition.signature ∧
      lowerProtocol SumcheckSourceData.snapshot domains summaries signatures function
        definition.signature = .ok definition.raw :=
  imported.protocolSource member

/-- Every original protocol is admitted to one exact checked tree. -/
theorem complete_original_protocol (function : Zkc.Source.Structured.Function)
    (member : .function function ∈ SumcheckSourceData.snapshot.definitions)
    (kind : function.kind = .protocol) :
    ∃ domains headers summaries,
      checkUnitHeaders SumcheckSourceData.snapshot = .ok (domains, headers, summaries) ∧
      ∃ definition, definition ∈ unit.protocols ∧
        checkProtocol SumcheckSourceData.snapshot domains summaries function headers = .ok definition ∧
        ∀ other, other ∈ unit.protocols →
          checkProtocol SumcheckSourceData.snapshot domains summaries function headers = .ok other →
            other = definition :=
  imported.protocolChecked member kind

end ZkcExamples.Structured.SumcheckSourceViews
