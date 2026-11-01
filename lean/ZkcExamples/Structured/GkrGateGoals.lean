module

public import ZkcExamples.Structured.GkrSourceBodies
public import Zkc.Source.Structured.DomainModels
public import Zkc.Protocols.AlgebraicRounds.Gate
public import Zkc.Source.Structured.CollectionReference
public import Zkc.Source.Structured.MapEvaluation
public meta import ZkcTools.StructuredSource.HelperPresentation
public meta import ZkcTools.StructuredSource.NamedValues
public meta import ZkcTools.StructuredSource.ReferenceComposition

@[expose] public section

/-! Complete helper goals derived from the actual admitted gate templates.
Field names describe source coordinates. No mathematical companion is imported
to generate the goal, and all callback captures and returned values are kept. -/
namespace ZkcExamples.Structured.GkrGateGoals
open Zkc.Source Zkc.Source.Structured

helper_presentation Value inputs [addWeight, mulWeight, left, right]
  outputs [value] := GkrSourceBodies.helper31Body

helper_presentation Realization inputs [addWeight, mulWeight, left, right]
  outputs [value] := GkrSourceBodies.scopedHelper42Body

helper_presentation Callback
  inputs [addWeight, mulWeight, left, right, addWeights, mulWeights, lefts, rights]
  outputs [value] := GkrSourceBodies.scopedHelper43Body

helper_presentation Map inputs [addWeights, mulWeights, lefts, rights]
  outputs [values] := GkrSourceBodies.scopedHelper44Body

abbrev collection : CollectSpec :=
  collection_spec% Map.body

named_values Item [addWeight, mulWeight, left, right] := collection.domain.items

/-- Source selection is checked once and shared by every installed gate law. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  value : BodyIn definitions GkrSourceBodies.helper31Helper Value.body
  realization : BodyIn definitions GkrSourceBodies.scopedHelper42Helper Realization.body
  callback : BodyIn definitions GkrSourceBodies.scopedHelper43Helper Callback.body
  map : BodyIn definitions GkrSourceBodies.scopedHelper44Helper Map.body

end ZkcExamples.Structured.GkrGateGoals
