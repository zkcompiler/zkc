module

public import ZkcExamples.Structured.RealizationValuesData
public import ZkcExamples.Structured.PrimitiveTableViews
public import Zkc.Source.Structured.ComponentLinking
public import Zkc.Source.Structured.ClosedProjection
public import Zkc.Source.Participant

@[expose] public section

/-! Exact typed views of the complete original table-then-realization caller.
The shared table bodies are reused only with equalities against this payload.
The retained realization remains a declaration with its exact Math helper ABI. -/
namespace ZkcExamples.Structured.RealizationValuesViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

abbrev tableTypes : List Ty := [.vector "bls12-381.fr", .index, .index]
abbrev valueTypes : List Ty := [.vector "bls12-381.fr"]

abbrev projectionHelper : Helper :=
  ⟨"zkl_b24070c290f19cb73c9bf60789c151de579891e3f86a4f1dba90347711916b33",
    .math, tableTypes, valueTypes⟩
abbrev realizationHelper : Helper :=
  ⟨"zkl_realization_0ce8d1f6fa18ecea2634e8a590d8d4d67ef3b2266fc521419daa7adb682a678a",
    .local, tableTypes, valueTypes⟩
abbrev valuesHelper : Helper :=
  ⟨"s12h6d61705f6578616d706c657314h7265616c697a655f76616c756573",
    .local, tableTypes, valueTypes⟩

def realizationDeclaration : RealizationDeclaration :=
  ⟨realizationHelper.name, tableTypes, valueTypes, projectionHelper.name⟩

theorem realization_retained :
    Definition.realization realizationDeclaration ∈ RealizationValuesData.snapshot.definitions :=
  List.mem_cons_self

set_option smartUnfolding true in
def projectionBody : Region dialect tableTypes valueTypes := .ret (.cons .here .nil)

set_option smartUnfolding true in
def realizationBody : Region dialect tableTypes valueTypes :=
  .letOp (.invoke projectionHelper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def valuesBody : Region dialect tableTypes valueTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke realizationHelper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def entryBody : Region dialect tableTypes valueTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke PrimitiveTableViews.tableHelper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.invoke valuesHelper)
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def protocolBody : Region protocolDialect tableTypes valueTypes :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall PrimitiveTableViews.tableHelper rfl 0 "s0")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .letOp (.mark "s2") .nil .nil <|
  .letOp (.localCall valuesHelper rfl 0 "s2")
    (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

def lessDefinition : CheckedDefinition :=
  ⟨PrimitiveTableViews.lessHelper.name, PrimitiveTableViews.lessHelper.kind, PrimitiveTableViews.lessHelper.inputs, PrimitiveTableViews.lessHelper.outputs,
    PrimitiveTableViews.lessBody.erase, PrimitiveTableViews.lessBody, PrimitiveTableViews.lessBody.elaborate_erase⟩

def rowsDefinition : CheckedDefinition :=
  ⟨PrimitiveTableViews.rowsHelper.name, PrimitiveTableViews.rowsHelper.kind, PrimitiveTableViews.rowsHelper.inputs, PrimitiveTableViews.rowsHelper.outputs,
    PrimitiveTableViews.rowsBody.erase, PrimitiveTableViews.rowsBody, PrimitiveTableViews.rowsBody.elaborate_erase⟩

def shapeDefinition : CheckedDefinition :=
  ⟨PrimitiveTableViews.shapeHelper.name, PrimitiveTableViews.shapeHelper.kind, PrimitiveTableViews.shapeHelper.inputs, PrimitiveTableViews.shapeHelper.outputs,
    PrimitiveTableViews.shapeBody.erase, PrimitiveTableViews.shapeBody, PrimitiveTableViews.shapeBody.elaborate_erase⟩

def tableDefinition : CheckedDefinition :=
  ⟨PrimitiveTableViews.tableHelper.name, PrimitiveTableViews.tableHelper.kind, PrimitiveTableViews.tableHelper.inputs, PrimitiveTableViews.tableHelper.outputs,
    PrimitiveTableViews.tableBody.erase, PrimitiveTableViews.tableBody, PrimitiveTableViews.tableBody.elaborate_erase⟩

def projectionDefinition : CheckedDefinition :=
  ⟨projectionHelper.name, projectionHelper.kind, projectionHelper.inputs, projectionHelper.outputs,
    projectionBody.erase, projectionBody, projectionBody.elaborate_erase⟩

def realizationDefinition : CheckedDefinition :=
  ⟨realizationHelper.name, realizationHelper.kind, realizationHelper.inputs, realizationHelper.outputs,
    realizationBody.erase, realizationBody, realizationBody.elaborate_erase⟩

def valuesDefinition : CheckedDefinition :=
  ⟨valuesHelper.name, valuesHelper.kind, valuesHelper.inputs, valuesHelper.outputs,
    valuesBody.erase, valuesBody, valuesBody.elaborate_erase⟩

def definitions : List CheckedDefinition :=
  [lessDefinition, rowsDefinition, shapeDefinition, tableDefinition, projectionDefinition, realizationDefinition, valuesDefinition]

def protocolDefinition : CheckedProtocol where
  toProtocolSignature := ⟨"s12h6d61705f6578616d706c657313h5265616c697a6556616c756573", ["role00000000"], tableTypes, valueTypes,
    List.replicate 3 [0], [[0]]⟩
  raw := protocolBody.erase
  body := protocolBody
  formed := protocolBody.elaborate_erase

def unit : UnitPayload where
  definitions := definitions
  protocols := [protocolDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def root : ClosedRoot :=
  ⟨"s12h6d61705f6578616d706c657313h5265616c697a6556616c756573", tableTypes, valueTypes,
    entryBody.erase, entryBody, entryBody.elaborate_erase⟩

def payload : Payload where
  definitions := definitions
  entry := root
  linked := unit.linked
  entryLinked := by decide +kernel

def program : ClosedProgram := ⟨⟨RealizationValuesData.snapshot, unit⟩, payload, by rfl⟩

/-- Kernel equality to the complete original checker, including all metadata. -/
def imported : ClosedImported RealizationValuesData.snapshot := ⟨program, rfl⟩

theorem kernel_admission : checkClosed RealizationValuesData.snapshot = .ok program :=
  imported.admitted

/-- The identical whole checked unit before singleton-role projection. -/
def subjectImported : Imported RealizationValuesData.snapshot := imported.subject

theorem exact_subject : program.snapshot = RealizationValuesData.snapshot := imported.exactSubject
theorem protocol_exact : program.subject.payload.entry.raw = protocolBody.erase := rfl
theorem protocol_typed : program.subject.payload.entry.body = protocolBody := rfl

theorem singleton_projection : ClosedProjection protocolBody entryBody :=
  .mark "s0" .nil (.localCall PrimitiveTableViews.tableHelper rfl "s0" _
    (.mark "s2" .nil (.localCall valuesHelper rfl "s2" _ (.ret _))))

theorem less_member : lessDefinition ∈ program.payload.definitions :=
  List.mem_cons_self

theorem rows_member : rowsDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_self)

theorem shape_member : shapeDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem table_member : tableDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

theorem projection_member : projectionDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))

theorem realization_member : realizationDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))))

theorem values_member : valuesDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))

theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl
theorem projection_exact : projectionDefinition.raw = projectionBody.erase := rfl
theorem realization_exact : realizationDefinition.raw = realizationBody.erase := rfl
theorem values_exact : valuesDefinition.raw = valuesBody.erase := rfl
theorem table_exact : tableDefinition.raw = PrimitiveTableViews.tableBody.erase := rfl
theorem shape_exact : shapeDefinition.raw = PrimitiveTableViews.shapeBody.erase := rfl
theorem less_exact : lessDefinition.raw = PrimitiveTableViews.lessBody.erase := rfl
theorem rows_exact : rowsDefinition.raw = PrimitiveTableViews.rowsBody.erase := rfl

theorem entry_typed : program.payload.entry.body = entryBody := rfl
theorem projection_typed : projectionDefinition.body = projectionBody := rfl
theorem realization_typed : realizationDefinition.body = realizationBody := rfl
theorem values_typed : valuesDefinition.body = valuesBody := rfl

/-- This derived body belongs to the retained declaration, with every ABI position. -/
theorem realization_derived : realizationDefinition.raw = realizationDeclaration.raw := rfl

theorem table_typed : tableDefinition.body = PrimitiveTableViews.tableBody := rfl
theorem shape_typed : shapeDefinition.body = PrimitiveTableViews.shapeBody := rfl
theorem less_typed : lessDefinition.body = PrimitiveTableViews.lessBody := rfl
theorem rows_typed : rowsDefinition.body = PrimitiveTableViews.rowsBody := rfl

end ZkcExamples.Structured.RealizationValuesViews
