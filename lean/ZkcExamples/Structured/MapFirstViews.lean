module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.MapFirstData
public import ZkcExamples.Structured.MapFirstBodies
public import Zkc.Source.Structured.ClosedProjection

@[expose] public section

/-! Normalized complete checked payload, with mandatory kernel equality to the
whole retained source admission. Typed views use the existing Region carrier. -/
namespace ZkcExamples.Structured.MapFirstViews
open Zkc.Source Zkc.Source.Structured
open MapFirstBodies
set_option smartUnfolding false

def protocolSignature : ProtocolSignature where
  name := "s12h6d61705f6578616d706c65735h4669727374"
  roles := ["role00000000"]
  inputs := [.vector "bls12-381.fr", .index, .index, .field "bls12-381.fr"]
  outputs := [.vector "bls12-381.fr", .index, .index]
  inputScopes := [[0], [0], [0], [0]]
  outputScopes := [[0], [0], [0]]

structured_closed_views MapFirstData.snapshot
  helpers [less, rows, shape, table, halves, interpolate, values, «variables», width,
    valuesRealization, variablesRealization, widthRealization, interpolateRealization,
    mapCallback, map, first, wrapper]
  protocols [protocol]
  root entryBody

/-- Explicit singleton-role projection of the retained protocol body. -/
theorem singleton_projection : ClosedProjection protocolBody entryBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

/-- The actual collection retains its domain and private callback; its scalar
computation is admitted separately through its own realization declaration. -/
def mapDeclaration : CollectDeclaration :=
  ⟨mapHelper.name, .privateDef, mapHelper.inputs, mapHelper.outputs,
    MapFirstBodies.bindings.domain, MapFirstBodies.bindings.callback, ""⟩

theorem map_retained : Definition.collect mapDeclaration ∈ MapFirstData.snapshot.definitions :=
  by structured_mem

theorem map_derived : mapDefinition.raw = mapBody.erase := rfl

theorem map_root_selected : interpolateHelper ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

def widthRealizationDeclaration : RealizationDeclaration :=
  ⟨widthRealizationHelper.name, widthRealizationHelper.inputs, widthRealizationHelper.outputs, widthHelper.name⟩

theorem widthRealization_retained : Definition.realization widthRealizationDeclaration ∈
    MapFirstData.snapshot.definitions :=
  by structured_mem

theorem widthRealization_derived : widthRealizationDefinition.raw = widthRealizationDeclaration.raw := rfl

theorem widthRealization_root_selected : widthRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

def variablesRealizationDeclaration : RealizationDeclaration :=
  ⟨variablesRealizationHelper.name, variablesRealizationHelper.inputs, variablesRealizationHelper.outputs, variablesHelper.name⟩

theorem variablesRealization_retained : Definition.realization variablesRealizationDeclaration ∈
    MapFirstData.snapshot.definitions :=
  by structured_mem

theorem variablesRealization_derived : variablesRealizationDefinition.raw = variablesRealizationDeclaration.raw := rfl

theorem variablesRealization_root_selected : variablesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

def valuesRealizationDeclaration : RealizationDeclaration :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.inputs, valuesRealizationHelper.outputs, valuesHelper.name⟩

theorem valuesRealization_retained : Definition.realization valuesRealizationDeclaration ∈
    MapFirstData.snapshot.definitions :=
  by structured_mem

theorem valuesRealization_derived : valuesRealizationDefinition.raw = valuesRealizationDeclaration.raw := rfl

theorem valuesRealization_root_selected : valuesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

end ZkcExamples.Structured.MapFirstViews
