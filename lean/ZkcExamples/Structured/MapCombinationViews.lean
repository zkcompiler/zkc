module

public import ZkcExamples.Structured.MapCombinationData
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Complete checked source payload with mandatory kernel equality to the
original admission result. Body views retain the existing Region carrier. -/
namespace ZkcExamples.Structured.MapCombinationViews
open Zkc.Source Zkc.Source.Structured
set_option smartUnfolding false

abbrev mapSpec : MapSpec := ⟨"s12h6d61705f6578616d706c65736h6c696e656172", "bls12-381.fr", [false, true, false, true, true, false]⟩

abbrev wrapperHelper : Helper := ⟨"s12h6d61705f6578616d706c657311h636f6d62696e6174696f6e", .local, [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def wrapperBody : Region dialect [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke ⟨"zkl_map_69915d69b63fed11da18dc3f9faf1a502e85fc5b9d1dbc28c8d156b3a27304b2", .local, [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

abbrev formulaHelper : Helper := ⟨"s12h6d61705f6578616d706c65736h6c696e656172", .math, [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

set_option smartUnfolding true in
def formulaBody : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.invoke ⟨"s12h6d61705f6578616d706c65735h7363616c65", .math, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩) (.cons .here (.cons (.there .here) .nil)) .nil <|
  .letOp (.invoke ⟨"s12h6d61705f6578616d706c65735h7363616c65", .math, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) .nil)) .nil <|
  .letOp (.fieldSubtract "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .letOp (.fieldConstant "bls12-381.fr" 3) .nil .nil <|
  .letOp (.fieldAdd "bls12-381.fr") (.cons (.there .here) (.cons .here .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev scaleHelper : Helper := ⟨"s12h6d61705f6578616d706c65735h7363616c65", .math, [.field "bls12-381.fr", .field "bls12-381.fr"], [.field "bls12-381.fr"]⟩

set_option smartUnfolding true in
def scaleBody : Region dialect [.field "bls12-381.fr", .field "bls12-381.fr"] [.field "bls12-381.fr"] :=
  .letOp (.fieldMultiply "bls12-381.fr") (.cons .here (.cons (.there .here) .nil)) .nil <|
  .ret (.cons .here .nil)

abbrev mapHelper : Helper := ⟨"zkl_map_69915d69b63fed11da18dc3f9faf1a502e85fc5b9d1dbc28c8d156b3a27304b2", .local, [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"], [.vector "bls12-381.fr"]⟩

set_option smartUnfolding true in
def mapBody : Region dialect [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.map mapSpec) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def entryBody : Region protocolDialect [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.localCall wrapperHelper rfl 0 "s0") (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

set_option smartUnfolding true in
def ownerBody : Region dialect [.field "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr", .vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke wrapperHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) (.cons (.there (.there (.there .here))) (.cons (.there (.there (.there (.there .here)))) (.cons (.there (.there (.there (.there (.there .here))))) .nil)))))) .nil <|
  .ret (.cons .here .nil)

/-- The owner uses the existing projection relation; the complete program
still retains both roles and its participant semantics. -/
theorem owner_projection : ClosedProjection entryBody ownerBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

def scaleDefinition : CheckedDefinition :=
  ⟨scaleHelper.name, scaleHelper.kind, scaleHelper.inputs, scaleHelper.outputs,
    scaleBody.erase, scaleBody, scaleBody.elaborate_erase⟩

theorem scale_exact : scaleDefinition.raw = scaleBody.erase := rfl
theorem scale_body_exact : scaleDefinition.body = scaleBody := rfl
theorem scale_signature : scaleDefinition.helper = scaleHelper := rfl

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
  [scaleDefinition, formulaDefinition, mapDefinition, wrapperDefinition]

def protocolDefinition : CheckedProtocol where
  toProtocolSignature := ⟨"s12h6d61705f6578616d706c657317h4c696e656172436f6d62696e6174696f6e", ["role00000000", "role00000001"], wrapperHelper.inputs, wrapperHelper.outputs,
    List.replicate 6 [0], [[0]]⟩
  raw := entryBody.erase
  body := entryBody
  formed := entryBody.elaborate_erase

def unit : UnitPayload where
  definitions := definitions
  protocols := [protocolDefinition]
  entryIndex := ⟨0, by decide⟩
  linked := by decide +kernel
  protocolsLinked := by decide +kernel
  available := checkUnitAvailability_ok_of_isOk (by decide +kernel)
  realizationClosed := by decide +kernel
  mapClosed := by decide +kernel

def program : Program := ⟨MapCombinationData.snapshot, unit⟩

/-- The whole original checker returns this complete payload, including metadata. -/
def imported : Imported MapCombinationData.snapshot := ⟨program, rfl⟩

theorem kernel_admission : check MapCombinationData.snapshot = .ok program := imported.admitted

theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl
theorem entry_body_exact : program.payload.entry.body = entryBody := rfl

theorem scale_member : scaleDefinition ∈ program.payload.definitions :=
  List.mem_cons_self

theorem formula_member : formulaDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_self)

theorem map_member : mapDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem wrapper_member : wrapperDefinition ∈ program.payload.definitions :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))

/-- Original metadata remains distinct from the derived Local body. -/
def mapDeclaration : MapDeclaration :=
  ⟨mapHelper.name, mapHelper.inputs, mapHelper.outputs, mapSpec.helperName, mapSpec.rowwise⟩

theorem map_retained : Definition.map mapDeclaration ∈ MapCombinationData.snapshot.definitions :=
  List.mem_cons_self

theorem map_derived : mapDefinition.raw = mapDeclaration.raw := rfl

theorem map_root_selected : mapDeclaration.spec.helper ∈
    preparationHelpers .map program.payload.definitions :=
  imported.mapRootSelected map_retained

end ZkcExamples.Structured.MapCombinationViews
