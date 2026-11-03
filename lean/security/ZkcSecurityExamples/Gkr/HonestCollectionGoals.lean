module

public import ZkcExamples.Structured.GkrSourceLaws
public import Zkc.Source.Structured.CollectionFold
public meta import ZkcTools.StructuredSource.HelperPresentation
public meta import ZkcTools.StructuredSource.NamedValues
public meta import ZkcTools.StructuredSource.ReferenceComposition
public meta import ZkcTools.StructuredSource.ProcessReference

@[expose] public section

/-! Complete named goals selected from the admitted collection helpers. No
mathematical reference or companion is needed to generate these interfaces. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers.CollectionGoals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

helper_presentation Repeat inputs [initial, value, count] outputs [values] := GkrSourceBodies.helper14Body
helper_presentation RepeatWrapper inputs [initial, value, count] outputs [values] := GkrSourceBodies.helper15Body
helper_presentation ReplicateStep inputs [initial, value, source, count] outputs [values] := GkrSourceBodies.helper16Body
helper_presentation ReplicateFold inputs [source, initial, count] outputs [values] := GkrSourceBodies.helper58Body
helper_presentation ReplicateWrapper inputs [initial, count, source] outputs [values] := GkrSourceBodies.helper59Body
helper_presentation Replicate inputs [source, count] outputs [values] := GkrSourceBodies.helper60Body
helper_presentation Append inputs [initial, value] outputs [values] := GkrSourceBodies.helper17Body
helper_presentation AppendStep inputs [initial, value, source] outputs [values] := GkrSourceBodies.helper18Body
helper_presentation AppendFold inputs [source, initial] outputs [values] := GkrSourceBodies.helper61Body
helper_presentation Concatenate inputs [initial, source] outputs [values] := GkrSourceBodies.helper62Body
helper_presentation Tile inputs [source, count] outputs [values] := GkrSourceBodies.helper63Body
helper_presentation Prefix inputs [source, dimension, point] outputs [values] := GkrSourceBodies.helper52Body
helper_presentation Layout inputs [add, mul, point, below, width] outputs [addValues, mulValues, leftValues, rightValues] := GkrSourceBodies.helper66Body

abbrev replicateSpec : FoldSpec := (GkrSourceLaws.fold? GkrSourceBodies.helper58Body).get (by decide +kernel)
abbrev appendSpec : FoldSpec := (GkrSourceLaws.fold? GkrSourceBodies.helper61Body).get (by decide +kernel)

named_values CollectionState [values] := appendSpec.state

-- The multi-call processes and all their parameters come from the actual
-- generated equations. These are source references, not pasted source trees.
source_reference prefixProcess from_equation Prefix.equation using [Prefix.run]
source_reference layoutProcess from_equation Layout.equation using [Layout.run]

structure Bodies (definitions : List CheckedDefinition) : Prop where
  repeated : BodyIn definitions GkrSourceBodies.helper14Helper Repeat.body
  repeatWrapper : BodyIn definitions GkrSourceBodies.helper15Helper RepeatWrapper.body
  replicateStep : BodyIn definitions GkrSourceBodies.helper16Helper ReplicateStep.body
  replicateFold : BodyIn definitions GkrSourceBodies.helper58Helper ReplicateFold.body
  replicateWrapper : BodyIn definitions GkrSourceBodies.helper59Helper ReplicateWrapper.body
  replicate : BodyIn definitions GkrSourceBodies.helper60Helper Replicate.body
  append : BodyIn definitions GkrSourceBodies.helper17Helper Append.body
  appendStep : BodyIn definitions GkrSourceBodies.helper18Helper AppendStep.body
  appendFold : BodyIn definitions GkrSourceBodies.helper61Helper AppendFold.body
  concatenate : BodyIn definitions GkrSourceBodies.helper62Helper Concatenate.body
  tile : BodyIn definitions GkrSourceBodies.helper63Helper Tile.body

end ZkcSecurity.Realizations.Gkr.HonestHelpers.CollectionGoals
