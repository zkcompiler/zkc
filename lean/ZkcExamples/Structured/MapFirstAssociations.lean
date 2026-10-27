module

public import ZkcExamples.Structured.MapFirstViews
public import ZkcExamples.Structured.MapFirstContracts
public import Zkc.Source.Structured.Association

@[expose] public section

namespace ZkcExamples.Structured.MapFirstAssociations
open Zkc.Source.Structured MapFirstViews MapFirstBodies

/-- Exact body witnesses in this source's complete checked table. -/
theorem first_bodies : MapFirstContracts.Bodies program.payload.definitions := by
  constructor
  · exact_body lessDefinition
  · exact_body rowsDefinition
  · exact_body shapeDefinition
  · exact_body tableDefinition
  · exact_body halvesDefinition
  · exact_body interpolateDefinition
  · exact_body interpolateRealizationDefinition
  · exact_body mapCallbackDefinition
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

end ZkcExamples.Structured.MapFirstAssociations
