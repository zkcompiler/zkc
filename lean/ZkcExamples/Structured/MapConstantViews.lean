module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.MapConstantData
public import ZkcExamples.Structured.MapConstantBodies
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Exact typed views of the complete retained source, including the private
collection callback and scalar realization. Admission is checked by the kernel. -/
namespace ZkcExamples.Structured.MapConstantViews
open Zkc.Source Zkc.Source.Structured
open MapConstantBodies
set_option smartUnfolding false

structured_views MapConstantData.snapshot
  helpers [formula, formulaRealization, mapCallback, map, wrapper]
  protocols [protocol]

structured_associations MapConstantViews [formula, formulaRealization, mapCallback, map, wrapper]

abbrev entryBody := protocolBody

theorem entry_exact : program.payload.entry.raw = entryBody.erase := rfl

set_option smartUnfolding true in
def ownerBody : Region dialect [.vector "bls12-381.fr", .vector "bls12-381.fr", .field "bls12-381.fr"] [.vector "bls12-381.fr"] :=
  .letOp (.mark "s0") .nil .nil <|
  .letOp (.invoke wrapperHelper) (.cons .here (.cons (.there .here) (.cons (.there (.there .here)) .nil))) .nil <|
  .ret (.cons .here .nil)

/-- The owner uses the existing projection relation; the complete program
still retains both roles and its participant semantics. -/
theorem owner_projection : ClosedProjection entryBody ownerBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

/-- The source retains its exact ordered domain and callback. -/
def mapDeclaration : CollectDeclaration :=
  ⟨mapHelper.name, .privateDef, mapHelper.inputs, mapHelper.outputs,
    collectSpec.domain.name, collectSpec.body, ""⟩

theorem map_retained : Definition.collect mapDeclaration ∈ MapConstantData.snapshot.definitions :=
  by structured_mem

theorem map_derived : mapDefinition.raw = mapBody.erase := rfl

theorem formula_root_selected : formulaHelper ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

end ZkcExamples.Structured.MapConstantViews
