module

public import ZkcExamples.Structured.MapFirstViews
public import ZkcExamples.Structured.MapPrefixViews
public import ZkcExamples.Structured.MapPrefixContracts

@[expose] public section
namespace ZkcExamples.Structured

/-! Separate complete source tables instantiate the same association constructors. -/

namespace MapFirstContractsInstance
open MapFirstViews

theorem first_bodies : MapFirstContracts.Bodies program.payload.definitions := by
  constructor
  · exact ⟨lessDefinition, less_member, rfl, by rfl⟩
  · exact ⟨rowsDefinition, rows_member, rfl, by rfl⟩
  · exact ⟨shapeDefinition, shape_member, rfl, by rfl⟩
  · exact ⟨tableDefinition, table_member, rfl, by rfl⟩
  · exact ⟨halvesDefinition, halves_member, rfl, by rfl⟩
  · exact ⟨interpolateDefinition, interpolate_member, rfl, by rfl⟩
  · exact ⟨mapDefinition, map_member, rfl, by rfl⟩
  · exact ⟨firstDefinition, first_member, rfl, by rfl⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem first_laws : MapFirstContracts.Laws (program.payload.meanings F G) :=
  MapFirstContracts.laws_of_bodies program.payload.linked first_bodies

end MapFirstContractsInstance

namespace MapPrefixContractsInstance
open MapPrefixViews

theorem first_bodies : MapFirstContracts.Bodies program.payload.definitions := by
  constructor
  · exact ⟨lessDefinition, less_member, rfl, by rfl⟩
  · exact ⟨rowsDefinition, rows_member, rfl, by rfl⟩
  · exact ⟨shapeDefinition, shape_member, rfl, by rfl⟩
  · exact ⟨tableDefinition, table_member, rfl, by rfl⟩
  · exact ⟨halvesDefinition, halves_member, rfl, by rfl⟩
  · exact ⟨interpolateDefinition, interpolate_member, rfl, by rfl⟩
  · exact ⟨mapDefinition, map_member, rfl, by rfl⟩
  · exact ⟨firstDefinition, first_member, rfl, by rfl⟩

variable {F G : Type} [CommRing F] [AddCommGroup G] [Module F G]
  [DecidableEq F] [DecidableEq G]

theorem first_laws : MapFirstContracts.Laws (program.payload.meanings F G) :=
  MapFirstContracts.laws_of_bodies program.payload.linked first_bodies

theorem prefix_bodies : MapPrefixContracts.Bodies program.payload.definitions := by
  constructor
  · exact ⟨stepDefinition, step_member, rfl, by rfl⟩
  · exact ⟨foldStepDefinition, foldStep_member, rfl, by rfl⟩
  · exact ⟨foldDefinition, fold_member, rfl, by rfl⟩
  · exact ⟨foldWrapperDefinition, foldWrapper_member, rfl, by rfl⟩
  · exact ⟨prefixDefinition, prefix_member, rfl, by rfl⟩
  · exact ⟨valuesDefinition, values_member, rfl, by rfl⟩
  · exact ⟨valuesRealizationDefinition, valuesRealization_member, rfl, by rfl⟩

theorem prefix_laws : MapPrefixContracts.Laws (program.payload.meanings F G) :=
  MapPrefixContracts.laws_of_bodies program.payload.linked prefix_bodies first_bodies

end MapPrefixContractsInstance

end ZkcExamples.Structured
