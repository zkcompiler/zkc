module

public import ZkcExamples.Structured.MapConstantData
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Complete checked source payload with mandatory kernel equality to the
original admission result. Body views retain the existing Region carrier. -/
namespace ZkcExamples.Structured.MapConstantViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

abbrev mapSpec : MapSpec := ⟨"s12h6d61705f6578616d706c65738h636f6e7374616e74", "bls12-381.fr", [true, true, false]⟩

abbrev wrapperHelper : Helper := ⟨"s12h6d61705f6578616d706c657313h636f6e7374616e745f726f7773", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def wrapperBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper := ⟨"s12h6d61705f6578616d706c65738h636f6e7374616e74", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

set_option smartUnfolding true in
def formulaBody : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldConstant "bls12-381.fr" 7) .nil .nil <|
  .ret (.cons .here .nil)

abbrev mapHelper : Helper := ⟨"zkl_map_d0cef3b4f0130cd7cc48739618179807e7defff3083f46ef2a798ffc1b23ce96", .local, [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def mapBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map mapSpec) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def entryBody : Region protocolDialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall wrapperHelper rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def ownerBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke wrapperHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

/-- The owner uses the existing projection relation; the complete program
still retains both roles and its participant semantics. -/
theorem owner_projection : ClosedProjection entryBody ownerBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

def formulaDefinition : CheckedDefinition :=
  ⟨formulaHelper.name, formulaHelper.kind, formulaHelper.inputs, formulaHelper.outputs,
    formulaBody.erase, formulaBody, formulaBody.elaborate_erase⟩

theorem formula_exact : formulaDefinition.raw = formulaBody.erase := rfl
theorem formula_body_exact : formulaDefinition.body = formulaBody := rfl
theorem formula_signature : formulaDefinition.helper = formulaHelper := rfl

def mapDefinition : CheckedDefinition :=
  ⟨mapHelper.name, mapHelper.kind, mapHelper.inputs, mapHelper.outputs,
    mapBody.erase, mapBody, mapBody.elaborate_erase⟩

theorem map_exact : mapDefinition.raw = mapBody.erase := rfl
theorem map_body_exact : mapDefinition.body = mapBody := rfl
theorem map_signature : mapDefinition.helper = mapHelper := rfl

def wrapperDefinition : CheckedDefinition :=
  ⟨wrapperHelper.name, wrapperHelper.kind, wrapperHelper.inputs, wrapperHelper.outputs,
    wrapperBody.erase, wrapperBody, wrapperBody.elaborate_erase⟩

theorem wrapper_exact : wrapperDefinition.raw = wrapperBody.erase := rfl
theorem wrapper_body_exact : wrapperDefinition.body = wrapperBody := rfl
theorem wrapper_signature : wrapperDefinition.helper = wrapperHelper := rfl

def definitions : List CheckedDefinition :=
  [formulaDefinition, mapDefinition, wrapperDefinition]

def protocolDefinition : CheckedProtocol :=
  ⟨"s12h6d61705f6578616d706c657312h436f6e7374616e74526f7773", ["role00000000", "role00000001"], wrapperHelper.inputs, wrapperHelper.outputs,
    List.replicate 3 [0], [[0]], entryBody.erase, entryBody, entryBody.elaborate_erase⟩

def unit : UnitPayload where
  definitions := definitions
  protocols := [protocolDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  rootsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨MapConstantData.snapshot, unit⟩

/-- The whole original checker returns this complete payload, including metadata. -/
def imported : Imported MapConstantData.snapshot := ⟨program, rfl⟩

theorem kernel_admission : check MapConstantData.snapshot = .ok program := imported.admitted

theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl
theorem entry_body_exact : program.payload.entry.body = entryBody := rfl

theorem formula_member : formulaDefinition ∈ program.payload.definitions :=
  List.mem_cons_self

theorem map_member : mapDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_self)

theorem wrapper_member : wrapperDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

/-- Original metadata remains distinct from the derived Local body. -/
def mapDeclaration : MapDeclaration :=
  ⟨mapHelper.name, mapHelper.inputs, mapHelper.outputs, mapSpec.helperName, mapSpec.rowwise⟩

theorem map_retained : Definition.map mapDeclaration ∈ MapConstantData.snapshot.definitions :=
  List.mem_cons_self

theorem map_derived : mapDefinition.raw = mapDeclaration.raw := rfl

theorem map_root_selected : mapDeclaration.spec.helper ∈
    preparationHelpers .map program.payload.definitions :=
  imported.mapRootSelected map_retained

end ZkcExamples.Structured.MapConstantViews
