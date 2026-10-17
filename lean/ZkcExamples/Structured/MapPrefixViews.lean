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
  helpers [less, rows, shape, table, halves, interpolate, map, first, step, foldStep, fold, foldWrapper,
    «prefix», values, valuesRealization, «variables», variablesRealization, width, widthRealization,
    wrapper]
  protocols [protocol]
  root entryBody

/-- Explicit singleton-role projection of the retained protocol body. -/
theorem singleton_projection : ClosedProjection protocolBody entryBody :=
  .mark "s0" .nil (.localCall wrapperHelper rfl "s0" _ (.ret _))

/-- Retained map metadata is associated with this actual derived Local definition. -/
def mapDeclaration : MapDeclaration :=
  ⟨mapHelper.name, mapHelper.inputs, mapHelper.outputs,
    MapFirstBodies.mapSpec.helperName, MapFirstBodies.mapSpec.rowwise⟩

theorem map_retained : Definition.map mapDeclaration ∈ MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem map_derived : mapDefinition.raw = mapDeclaration.raw := rfl

theorem map_root_selected : mapDeclaration.spec.helper ∈
    preparationHelpers .map program.payload.definitions :=
  subjectImported.mapRootSelected map_retained

def widthRealizationDeclaration : RealizationDeclaration :=
  ⟨widthRealizationHelper.name, widthRealizationHelper.inputs, widthRealizationHelper.outputs, widthHelper.name⟩

theorem widthRealization_retained : Definition.realization widthRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem widthRealization_derived : widthRealizationDefinition.raw = widthRealizationDeclaration.raw := rfl

theorem widthRealization_root_selected : widthRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  subjectImported.realizationRootSelected widthRealization_retained

def variablesRealizationDeclaration : RealizationDeclaration :=
  ⟨variablesRealizationHelper.name, variablesRealizationHelper.inputs, variablesRealizationHelper.outputs, variablesHelper.name⟩

theorem variablesRealization_retained : Definition.realization variablesRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem variablesRealization_derived : variablesRealizationDefinition.raw = variablesRealizationDeclaration.raw := rfl

theorem variablesRealization_root_selected : variablesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  subjectImported.realizationRootSelected variablesRealization_retained

def valuesRealizationDeclaration : RealizationDeclaration :=
  ⟨valuesRealizationHelper.name, valuesRealizationHelper.inputs, valuesRealizationHelper.outputs, valuesHelper.name⟩

theorem valuesRealization_retained : Definition.realization valuesRealizationDeclaration ∈
    MapPrefixData.snapshot.definitions :=
  by structured_mem

theorem valuesRealization_derived : valuesRealizationDefinition.raw = valuesRealizationDeclaration.raw := rfl

theorem valuesRealization_root_selected : valuesRealizationDeclaration.helperSpec ∈
    preparationHelpers .realization program.payload.definitions :=
  subjectImported.realizationRootSelected valuesRealization_retained

end ZkcExamples.Structured.MapPrefixViews
