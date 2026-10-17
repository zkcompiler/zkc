module

public import ZkcExamples.Structured.MapPrefixViews
public import ZkcExamples.Structured.MapPrefixContracts
public import Zkc.Source.Structured.Association

@[expose] public section

namespace ZkcExamples.Structured.MapPrefixAssociations
open Zkc.Source.Structured MapPrefixViews MapPrefixBodies

/-- Exact body witnesses in this source's complete checked table. -/
theorem first_bodies : MapFirstContracts.Bodies program.payload.definitions := by
  constructor
  · exact_body lessDefinition
  · exact_body rowsDefinition
  · exact_body shapeDefinition
  · exact_body tableDefinition
  · exact_body halvesDefinition
  · exact_body interpolateDefinition
  · exact_body mapDefinition
  · exact_body firstDefinition

theorem values_association :
    BodyIn program.payload.definitions valuesHelper valuesBody := by
  exact_body valuesDefinition

theorem valuesRealization_association :
    BodyIn program.payload.definitions valuesRealizationHelper valuesRealizationBody := by
  exact_body valuesRealizationDefinition

theorem variables_association :
    BodyIn program.payload.definitions variablesHelper variablesBody := by
  exact_body variablesDefinition

theorem variablesRealization_association :
    BodyIn program.payload.definitions variablesRealizationHelper variablesRealizationBody := by
  exact_body variablesRealizationDefinition

theorem width_association :
    BodyIn program.payload.definitions widthHelper widthBody := by
  exact_body widthDefinition

theorem widthRealization_association :
    BodyIn program.payload.definitions widthRealizationHelper widthRealizationBody := by
  exact_body widthRealizationDefinition

theorem prefix_bodies : MapPrefixContracts.Bodies program.payload.definitions := by
  constructor
  · exact_body stepDefinition
  · exact_body foldStepDefinition
  · exact_body foldDefinition
  · exact_body foldWrapperDefinition
  · exact_body prefixDefinition
  · exact_body valuesDefinition
  · exact_body valuesRealizationDefinition

end ZkcExamples.Structured.MapPrefixAssociations
