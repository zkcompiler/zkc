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

helper_presentation Repeat inputs [initial, value, count] outputs [values] := GkrSourceBodies.helper20Body
helper_presentation RepeatWrapper inputs [initial, value, count] outputs [values] := GkrSourceBodies.helper21Body
helper_presentation ReplicateStep inputs [initial, value, source, count] outputs [values] := GkrSourceBodies.helper22Body
helper_presentation ReplicateFold inputs [source, initial, count] outputs [values] := GkrSourceBodies.scopedHelper45Body
helper_presentation ReplicateWrapper inputs [initial, count, source] outputs [values] := GkrSourceBodies.helper24Body
helper_presentation Replicate inputs [source, count] outputs [values] := GkrSourceBodies.helper25Body
helper_presentation Append inputs [initial, value] outputs [values] := GkrSourceBodies.helper26Body
helper_presentation AppendStep inputs [initial, value, source] outputs [values] := GkrSourceBodies.helper27Body
helper_presentation AppendFold inputs [source, initial] outputs [values] := GkrSourceBodies.scopedHelper48Body
helper_presentation Concatenate inputs [initial, source] outputs [values] := GkrSourceBodies.helper29Body
helper_presentation Tile inputs [source, count] outputs [values] := GkrSourceBodies.helper30Body
helper_presentation Prefix inputs [source, dimension, point] outputs [values] := GkrSourceBodies.helper35Body
helper_presentation Layout inputs [add, mul, point, below, width] outputs [addValues, mulValues, leftValues, rightValues] := GkrSourceBodies.helper36Body

abbrev replicateSpec : FoldSpec := (GkrSourceLaws.fold? GkrSourceBodies.scopedHelper45Body).get (by decide +kernel)
abbrev appendSpec : FoldSpec := (GkrSourceLaws.fold? GkrSourceBodies.scopedHelper48Body).get (by decide +kernel)

named_values CollectionState [values] := appendSpec.state

-- The multi-call processes and all their parameters come from the actual
-- generated equations. These are source references, not pasted source trees.
source_reference prefixProcess from_equation Prefix.equation using [Prefix.run]
source_reference layoutProcess from_equation Layout.equation using [Layout.run]

structure Bodies (definitions : List CheckedDefinition) : Prop where
  repeated : BodyIn definitions GkrSourceBodies.helper20Helper Repeat.body
  repeatWrapper : BodyIn definitions GkrSourceBodies.helper21Helper RepeatWrapper.body
  replicateStep : BodyIn definitions GkrSourceBodies.helper22Helper ReplicateStep.body
  replicateFold : BodyIn definitions GkrSourceBodies.scopedHelper45Helper ReplicateFold.body
  replicateWrapper : BodyIn definitions GkrSourceBodies.helper24Helper ReplicateWrapper.body
  replicate : BodyIn definitions GkrSourceBodies.helper25Helper Replicate.body
  append : BodyIn definitions GkrSourceBodies.helper26Helper Append.body
  appendStep : BodyIn definitions GkrSourceBodies.helper27Helper AppendStep.body
  appendFold : BodyIn definitions GkrSourceBodies.scopedHelper48Helper AppendFold.body
  concatenate : BodyIn definitions GkrSourceBodies.helper29Helper Concatenate.body
  tile : BodyIn definitions GkrSourceBodies.helper30Helper Tile.body

end ZkcSecurity.Realizations.Gkr.HonestHelpers.CollectionGoals
