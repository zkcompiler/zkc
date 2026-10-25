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
  helpers [less, rows, shape, table, halves, interpolate, map, first, values, valuesRealization,
    «variables», variablesRealization, width, widthRealization, wrapper]
  protocols [protocol]
  root entryBody

/-- Explicit singleton-role projection of the retained protocol body. -/
theorem singleton_projection : ClosedProjection protocolBody entryBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

/-- Retained map metadata is associated with this actual derived Local definition. -/
def mapDeclaration : MapDeclaration :=
  ⟨mapHelper.name, mapHelper.inputs, mapHelper.outputs,
    MapFirstBodies.mapSpec.helperName, MapFirstBodies.mapSpec.rowwise⟩

theorem map_retained : Definition.map mapDeclaration ∈ MapFirstData.snapshot.definitions :=
  by structured_mem

theorem map_derived : mapDefinition.raw = mapDeclaration.raw := rfl

theorem map_root_selected : mapDeclaration.spec.helper ∈
    preparationHelpers .map program.payload.definitions :=
  subjectImported.mapRootSelected map_retained

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
