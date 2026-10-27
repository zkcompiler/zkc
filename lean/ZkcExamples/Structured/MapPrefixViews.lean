module

public import Zkc.Source.Structured.UnitViews
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

def protocolSignature : ProtocolSignature where
  name := "s12h6d61705f6578616d706c65736h507265666978"
  roles := ["role00000000"]
  inputs := [.vector "bls12-381.fr", .index, .index, .vector "bls12-381.fr"]
  outputs := [.vector "bls12-381.fr", .index, .index]
  inputScopes := [[0], [0], [0], [0]]
  outputScopes := [[0], [0], [0]]

structured_closed_views MapPrefixData.snapshot
  helpers [less, rows, shape, table, halves, interpolate, values, «variables», width,
    valuesRealization, variablesRealization, widthRealization, interpolateRealization,
    mapCallback, map, first, step, foldStep, fold, foldWrapper, «prefix», wrapper]
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

theorem map_retained : Definition.collect mapDeclaration ∈ MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem map_derived : mapDefinition.raw = mapBody.erase := rfl

theorem map_root_selected : interpolateHelper ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

def widthRealizationDeclaration : RealizationDeclaration :=
  ⟨widthRealizationHelper.name, widthRealizationHelper.inputs, widthRealizationHelper.outputs, widthHelper.name⟩

theorem widthRealization_retained : Definition.realization widthRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem widthRealization_derived : widthRealizationDefinition.raw = widthRealizationDeclaration.raw := rfl

theorem widthRealization_root_selected : widthRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

def variablesRealizationDeclaration : RealizationDeclaration :=
  ⟨variablesRealizationHelper.name, variablesRealizationHelper.inputs, variablesRealizationHelper.outputs, variablesHelper.name⟩

theorem variablesRealization_retained : Definition.realization variablesRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem variablesRealization_derived : variablesRealizationDefinition.raw = variablesRealizationDeclaration.raw := rfl

theorem variablesRealization_root_selected : variablesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

def valuesRealizationDeclaration : RealizationDeclaration :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.inputs, valuesRealizationHelper.outputs, valuesHelper.name⟩

theorem valuesRealization_retained : Definition.realization valuesRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem valuesRealization_derived : valuesRealizationDefinition.raw = valuesRealizationDeclaration.raw := rfl

theorem valuesRealization_root_selected : valuesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  by decide +kernel

end ZkcExamples.Structured.MapPrefixViews
