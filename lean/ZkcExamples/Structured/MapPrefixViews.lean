module

public import ZkcExamples.Structured.MapPrefixData
public import ZkcExamples.Structured.MapPrefixBodies
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Normalized complete checked payload, with mandatory kernel equality to the
whole retained source admission. Typed views use the existing Region carrier. -/
namespace ZkcExamples.Structured.MapPrefixViews
open Zkc.Source Zkc.Source.Structured
open MapPrefixBodies
set_option smartUnfolding false

def lessDefinition : CheckedDefinition :=
  ⟨lessHelper.name, lessHelper.kind, lessHelper.inputs, lessHelper.outputs,
    lessBody.erase, lessBody, lessBody.elaborate_erase⟩

theorem less_exact : lessDefinition.raw = lessBody.erase := rfl
theorem less_body_exact : lessDefinition.body = lessBody := rfl

def rowsDefinition : CheckedDefinition :=
  ⟨rowsHelper.name, rowsHelper.kind, rowsHelper.inputs, rowsHelper.outputs,
    rowsBody.erase, rowsBody, rowsBody.elaborate_erase⟩

theorem rows_exact : rowsDefinition.raw = rowsBody.erase := rfl
theorem rows_body_exact : rowsDefinition.body = rowsBody := rfl

def shapeDefinition : CheckedDefinition :=
  ⟨shapeHelper.name, shapeHelper.kind, shapeHelper.inputs, shapeHelper.outputs,
    shapeBody.erase, shapeBody, shapeBody.elaborate_erase⟩

theorem shape_exact : shapeDefinition.raw = shapeBody.erase := rfl
theorem shape_body_exact : shapeDefinition.body = shapeBody := rfl

def tableDefinition : CheckedDefinition :=
  ⟨tableHelper.name, tableHelper.kind, tableHelper.inputs, tableHelper.outputs,
    tableBody.erase, tableBody, tableBody.elaborate_erase⟩

theorem table_exact : tableDefinition.raw = tableBody.erase := rfl
theorem table_body_exact : tableDefinition.body = tableBody := rfl

def halvesDefinition : CheckedDefinition :=
  ⟨halvesHelper.name, halvesHelper.kind, halvesHelper.inputs, halvesHelper.outputs,
    halvesBody.erase, halvesBody, halvesBody.elaborate_erase⟩

theorem halves_exact : halvesDefinition.raw = halvesBody.erase := rfl
theorem halves_body_exact : halvesDefinition.body = halvesBody := rfl

def interpolateDefinition : CheckedDefinition :=
  ⟨interpolateHelper.name, interpolateHelper.kind, interpolateHelper.inputs, interpolateHelper.outputs,
    interpolateBody.erase, interpolateBody, interpolateBody.elaborate_erase⟩

theorem interpolate_exact : interpolateDefinition.raw = interpolateBody.erase := rfl
theorem interpolate_body_exact : interpolateDefinition.body = interpolateBody := rfl

def mapDefinition : CheckedDefinition :=
  ⟨mapHelper.name, mapHelper.kind, mapHelper.inputs, mapHelper.outputs,
    mapBody.erase, mapBody, mapBody.elaborate_erase⟩

theorem map_exact : mapDefinition.raw = mapBody.erase := rfl
theorem map_body_exact : mapDefinition.body = mapBody := rfl

def firstDefinition : CheckedDefinition :=
  ⟨firstHelper.name, firstHelper.kind, firstHelper.inputs, firstHelper.outputs,
    firstBody.erase, firstBody, firstBody.elaborate_erase⟩

theorem first_exact : firstDefinition.raw = firstBody.erase := rfl
theorem first_body_exact : firstDefinition.body = firstBody := rfl

def stepDefinition : CheckedDefinition :=
  ⟨stepHelper.name, stepHelper.kind, stepHelper.inputs, stepHelper.outputs,
    stepBody.erase, stepBody, stepBody.elaborate_erase⟩

theorem step_exact : stepDefinition.raw = stepBody.erase := rfl
theorem step_body_exact : stepDefinition.body = stepBody := rfl

def foldStepDefinition : CheckedDefinition :=
  ⟨foldStepHelper.name, foldStepHelper.kind, foldStepHelper.inputs, foldStepHelper.outputs,
    foldStepBody.erase, foldStepBody, foldStepBody.elaborate_erase⟩

theorem foldStep_exact : foldStepDefinition.raw = foldStepBody.erase := rfl
theorem foldStep_body_exact : foldStepDefinition.body = foldStepBody := rfl

def foldDefinition : CheckedDefinition :=
  ⟨foldHelper.name, foldHelper.kind, foldHelper.inputs, foldHelper.outputs,
    foldBody.erase, foldBody, foldBody.elaborate_erase⟩

theorem fold_exact : foldDefinition.raw = foldBody.erase := rfl
theorem fold_body_exact : foldDefinition.body = foldBody := rfl

def foldWrapperDefinition : CheckedDefinition :=
  ⟨foldWrapperHelper.name, foldWrapperHelper.kind, foldWrapperHelper.inputs, foldWrapperHelper.outputs,
    foldWrapperBody.erase, foldWrapperBody, foldWrapperBody.elaborate_erase⟩

theorem foldWrapper_exact : foldWrapperDefinition.raw = foldWrapperBody.erase := rfl
theorem foldWrapper_body_exact : foldWrapperDefinition.body = foldWrapperBody := rfl

def prefixDefinition : CheckedDefinition :=
  ⟨prefixHelper.name, prefixHelper.kind, prefixHelper.inputs, prefixHelper.outputs,
    prefixBody.erase, prefixBody, prefixBody.elaborate_erase⟩

theorem prefix_exact : prefixDefinition.raw = prefixBody.erase := rfl
theorem prefix_body_exact : prefixDefinition.body = prefixBody := rfl

def valuesDefinition : CheckedDefinition :=
  ⟨valuesHelper.name, valuesHelper.kind, valuesHelper.inputs, valuesHelper.outputs,
    valuesBody.erase, valuesBody, valuesBody.elaborate_erase⟩

theorem values_exact : valuesDefinition.raw = valuesBody.erase := rfl
theorem values_body_exact : valuesDefinition.body = valuesBody := rfl

def valuesRealizationDefinition : CheckedDefinition :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.kind, valuesRealizationHelper.inputs, valuesRealizationHelper.outputs,
    valuesRealizationBody.erase, valuesRealizationBody, valuesRealizationBody.elaborate_erase⟩

theorem valuesRealization_exact : valuesRealizationDefinition.raw = valuesRealizationBody.erase := rfl
theorem valuesRealization_body_exact : valuesRealizationDefinition.body = valuesRealizationBody := rfl

def variablesDefinition : CheckedDefinition :=
  ⟨variablesHelper.name, variablesHelper.kind, variablesHelper.inputs, variablesHelper.outputs,
    variablesBody.erase, variablesBody, variablesBody.elaborate_erase⟩

theorem variables_exact : variablesDefinition.raw = variablesBody.erase := rfl
theorem variables_body_exact : variablesDefinition.body = variablesBody := rfl

def variablesRealizationDefinition : CheckedDefinition :=
  ⟨variablesRealizationHelper.name, variablesRealizationHelper.kind, variablesRealizationHelper.inputs, variablesRealizationHelper.outputs,
    variablesRealizationBody.erase, variablesRealizationBody, variablesRealizationBody.elaborate_erase⟩

theorem variablesRealization_exact : variablesRealizationDefinition.raw = variablesRealizationBody.erase := rfl
theorem variablesRealization_body_exact : variablesRealizationDefinition.body = variablesRealizationBody := rfl

def widthDefinition : CheckedDefinition :=
  ⟨widthHelper.name, widthHelper.kind, widthHelper.inputs, widthHelper.outputs,
    widthBody.erase, widthBody, widthBody.elaborate_erase⟩

theorem width_exact : widthDefinition.raw = widthBody.erase := rfl
theorem width_body_exact : widthDefinition.body = widthBody := rfl

def widthRealizationDefinition : CheckedDefinition :=
  ⟨widthRealizationHelper.name, widthRealizationHelper.kind, widthRealizationHelper.inputs, widthRealizationHelper.outputs,
    widthRealizationBody.erase, widthRealizationBody, widthRealizationBody.elaborate_erase⟩

theorem widthRealization_exact : widthRealizationDefinition.raw = widthRealizationBody.erase := rfl
theorem widthRealization_body_exact : widthRealizationDefinition.body = widthRealizationBody := rfl

def wrapperDefinition : CheckedDefinition :=
  ⟨wrapperHelper.name, wrapperHelper.kind, wrapperHelper.inputs, wrapperHelper.outputs,
    wrapperBody.erase, wrapperBody, wrapperBody.elaborate_erase⟩

theorem wrapper_exact : wrapperDefinition.raw = wrapperBody.erase := rfl
theorem wrapper_body_exact : wrapperDefinition.body = wrapperBody := rfl

def definitions : List CheckedDefinition :=
  [lessDefinition, rowsDefinition, shapeDefinition, tableDefinition, halvesDefinition, interpolateDefinition, mapDefinition, firstDefinition, stepDefinition, foldStepDefinition, foldDefinition, foldWrapperDefinition, prefixDefinition, valuesDefinition, valuesRealizationDefinition, variablesDefinition, variablesRealizationDefinition, widthDefinition, widthRealizationDefinition, wrapperDefinition]

def protocolDefinition : CheckedProtocol :=
  ⟨"s12h6d61705f6578616d706c65736h507265666978", ["role00000000"], wrapperHelper.inputs, wrapperHelper.outputs,
    List.replicate 4 [0], List.replicate 3 [0], protocolBody.erase, protocolBody,
    protocolBody.elaborate_erase⟩

def unit : UnitPayload where
  definitions := definitions
  protocols := [protocolDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  rootsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def root : ClosedRoot :=
  ⟨"s12h6d61705f6578616d706c65736h507265666978", wrapperHelper.inputs, wrapperHelper.outputs,
    entryBody.erase, entryBody, entryBody.elaborate_erase⟩

def payload : Payload where
  definitions := definitions
  entry := root
  linked := unit.linked
  entryLinked := by decide +kernel

def program : ClosedProgram := ⟨⟨MapPrefixData.snapshot, unit⟩, payload, by rfl⟩

/-- Complete actual-source admission, including both preparation closures. -/
def imported : ClosedImported MapPrefixData.snapshot := ⟨program, rfl⟩

theorem kernel_admission : checkClosed MapPrefixData.snapshot = .ok program := imported.admitted

theorem exact_subject : program.snapshot = MapPrefixData.snapshot := imported.exactSubject
theorem protocol_exact : program.subject.payload.entry.raw = protocolBody.erase := rfl
theorem protocol_body_exact : program.subject.payload.entry.body = protocolBody := rfl
theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl
theorem entry_body_exact : program.payload.entry.body = entryBody := rfl

/-- Explicit singleton-role projection of the retained protocol body. -/
theorem singleton_projection : ClosedProjection protocolBody entryBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

theorem less_member : lessDefinition ∈ program.payload.definitions :=
  List.mem_cons_self

theorem rows_member : rowsDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_self)

theorem shape_member : shapeDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem table_member : tableDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem halves_member : halvesDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))

theorem interpolate_member : interpolateDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))

theorem map_member : mapDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem first_member : firstDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))

theorem step_member : stepDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))

theorem foldStep_member : foldStepDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))

theorem fold_member : foldDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))

theorem foldWrapper_member : foldWrapperDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))

theorem prefix_member : prefixDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))

theorem values_member : valuesDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))

theorem valuesRealization_member : valuesRealizationDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))

theorem variables_member : variablesDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))

theorem variablesRealization_member : variablesRealizationDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))

theorem width_member : widthDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))

theorem widthRealization_member : widthRealizationDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))))))))))))))

theorem wrapper_member : wrapperDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))))))))))))))))

/-- The same complete subject also carries the ordinary whole-unit admission. -/
def subjectImported : Imported MapPrefixData.snapshot := imported.subject

/-- Retained map metadata is associated with this actual derived Local definition. -/
def mapDeclaration : MapDeclaration :=
  ⟨mapHelper.name, mapHelper.inputs, mapHelper.outputs,
    MapFirstBodies.mapSpec.helperName, MapFirstBodies.mapSpec.rowwise⟩

theorem map_retained : Definition.map mapDeclaration ∈ MapPrefixData.snapshot.definitions :=
  List.mem_cons_self

theorem map_derived : mapDefinition.raw = mapDeclaration.raw := rfl

theorem map_root_selected : mapDeclaration.spec.helper ∈
    preparationHelpers .map program.payload.definitions :=
  subjectImported.mapRootSelected map_retained

def widthRealizationDeclaration : RealizationDeclaration :=
  ⟨widthRealizationHelper.name, widthRealizationHelper.inputs, widthRealizationHelper.outputs, widthHelper.name⟩

theorem widthRealization_retained : Definition.realization widthRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_self)

theorem widthRealization_derived : widthRealizationDefinition.raw = widthRealizationDeclaration.raw := rfl

theorem widthRealization_root_selected : widthRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  subjectImported.realizationRootSelected widthRealization_retained

def variablesRealizationDeclaration : RealizationDeclaration :=
  ⟨variablesRealizationHelper.name, variablesRealizationHelper.inputs, variablesRealizationHelper.outputs, variablesHelper.name⟩

theorem variablesRealization_retained : Definition.realization variablesRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem variablesRealization_derived : variablesRealizationDefinition.raw = variablesRealizationDeclaration.raw := rfl

theorem variablesRealization_root_selected : variablesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  subjectImported.realizationRootSelected variablesRealization_retained

def valuesRealizationDeclaration : RealizationDeclaration :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.inputs, valuesRealizationHelper.outputs, valuesHelper.name⟩

theorem valuesRealization_retained : Definition.realization valuesRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem valuesRealization_derived : valuesRealizationDefinition.raw = valuesRealizationDeclaration.raw := rfl

theorem valuesRealization_root_selected : valuesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  subjectImported.realizationRootSelected valuesRealization_retained

end ZkcExamples.Structured.MapPrefixViews
