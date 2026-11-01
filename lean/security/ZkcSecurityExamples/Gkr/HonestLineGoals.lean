module

public import ZkcExamples.Structured.GkrSourceLaws
public import Zkc.Source.Structured.DeterministicFold
public import Zkc.Source.Structured.CollectionFold
public import Zkc.Source.Structured.HelperCallbacks
public meta import ZkcTools.StructuredSource.HelperCallbacks
public meta import ZkcTools.StructuredSource.HelperPresentation
public meta import ZkcTools.StructuredSource.NamedValues
public meta import ZkcTools.StructuredSource.ProcessReference
public meta import ZkcTools.StructuredSource.ReferenceComposition

@[expose] public section

/-! Complete source-selected line helper goals. The source determines every
schema, callback, return and stopping branch before a companion is chosen. -/
namespace ZkcSecurity.Realizations.Gkr.HonestLine.Goals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

helper_presentation Constant inputs [initial, value, width] outputs [values] := GkrSourceBodies.helper48Body
helper_presentation ConstantWrapper inputs [initial, value, width] outputs [values] := GkrSourceBodies.helper49Body
helper_presentation ConstantStep inputs [initial, value, source, width] outputs [values] := GkrSourceBodies.helper50Body
helper_presentation ConstantFold inputs [source, initial, width] outputs [values] := GkrSourceBodies.scopedHelper80Body
helper_presentation Constants inputs [initial, width, source] outputs [values] := GkrSourceBodies.helper52Body
helper_presentation Difference inputs [high, low] outputs [value] := GkrSourceBodies.helper58Body
helper_presentation DifferenceWrapper inputs [high, low] outputs [value] := GkrSourceBodies.scopedHelper67Body
helper_presentation Slope inputs [low, high, delta] outputs [value] := GkrSourceBodies.helper60Body
helper_presentation SlopeWrapper inputs [low, high, delta] outputs [value] := GkrSourceBodies.scopedHelper68Body
helper_presentation SlopeCallback inputs [low, high, left, right, delta] outputs [value] := GkrSourceBodies.scopedHelper69Body
helper_presentation Slopes inputs [left, right, delta] outputs [values] := GkrSourceBodies.scopedHelper70Body
helper_presentation Total inputs [left, right] outputs [value] := GkrSourceBodies.helper67Body
helper_presentation TotalWrapper inputs [left, right] outputs [value] := GkrSourceBodies.scopedHelper71Body
helper_presentation TotalCallback inputs [low, high, left, right] outputs [value] := GkrSourceBodies.scopedHelper72Body
helper_presentation Totals inputs [left, right] outputs [values] := GkrSourceBodies.scopedHelper73Body
helper_presentation ShiftStep inputs [initial, previous, offset, value, count]
  outputs [values, previous, offset] := GkrSourceBodies.helper62Body
helper_presentation ShiftCallback inputs [initial, previous, offset, value, source, count]
  outputs [values, previous, offset] := GkrSourceBodies.helper63Body
helper_presentation ShiftFold inputs [source, initial, previous, offset, count]
  outputs [values, previous, offset] := GkrSourceBodies.scopedHelper86Body
helper_presentation ShiftWrapper inputs [initial, previous, offset, count, source]
  outputs [values, previous, offset] := GkrSourceBodies.helper65Body
helper_presentation Shift inputs [source, count] outputs [values] := GkrSourceBodies.helper66Body
helper_callback lineCallback from GkrSourceBodies.helper69Body
helper_presentation Step inputs [iteration, values, position, start, finish, count]
  outputs [values, position, start, finish, count] := lineCallback
helper_presentation Line inputs [values, start, finish, width] outputs [coefficients] := GkrSourceBodies.helper69Body

abbrev constantSpec : FoldSpec := (GkrSourceLaws.fold? ConstantFold.body).get (by decide +kernel)
abbrev shiftSpec : FoldSpec := (GkrSourceLaws.fold? ShiftFold.body).get (by decide +kernel)
abbrev slopesSpec : CollectSpec := collection_spec% Slopes.body
abbrev totalsSpec : CollectSpec := collection_spec% Totals.body

named_values ConstantState [values] := constantSpec.state
named_values ConstantItem [value] := constantSpec.domain.items
named_values ConstantDomain [source] := constantSpec.domain.inputs
named_values ConstantCaptures [width] := constantSpec.captures
named_values ShiftState [values, previous, offset] := shiftSpec.state
named_values ShiftItem [value] := shiftSpec.domain.items
named_values ShiftDomain [source] := shiftSpec.domain.inputs
named_values ShiftCaptures [count] := shiftSpec.captures
named_values LineState [values, position] := lineCallback_selection.callback.state
named_values LineCaptures [start, finish, count] := lineCallback_selection.callback.captures
named_values StepArguments [iteration, values, position, start, finish, count] := lineCallback_selection.callback.inputs
named_values SlopesItem [low, high] := slopesSpec.domain.items
named_values TotalsItem [low, high] := totalsSpec.domain.items
named_values SlopesDomain [left, right] := slopesSpec.domain.inputs
named_values SlopesCaptures [delta] := slopesSpec.captures
named_values TotalsDomain [left, right] := totalsSpec.domain.inputs
named_values SlopesArguments [left, right, delta] := GkrSourceBodies.scopedHelper70Helper.inputs

source_reference slopesProcess from_equation Slopes.equation
  using [Slopes.run, Slopes.encode, Slopes.decode, PIR.Process.bind_assoc, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Values.get]
source_reference stepProcess from_equation Step.equation
  using [Step.run, Step.encode, Step.decode, PIR.Process.bind_assoc, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Values.get]
source_reference lineProcess from_equation Line.equation
  using [Line.run, Line.encode, Line.decode, PIR.Process.bind_assoc, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Values.get]

named_values DifferenceArguments [high, low] := GkrSourceBodies.helper58Helper.inputs
named_values SlopeArguments [low, high, delta] := GkrSourceBodies.helper60Helper.inputs
named_values TotalArguments [left, right] := GkrSourceBodies.helper67Helper.inputs
named_values DifferenceWrapperArguments [high, low] := GkrSourceBodies.scopedHelper67Helper.inputs
named_values SlopeWrapperArguments [low, high, delta] := GkrSourceBodies.scopedHelper68Helper.inputs
named_values SlopeCallbackArguments [low, high, left, right, delta] := GkrSourceBodies.scopedHelper69Helper.inputs
named_values TotalWrapperArguments [left, right] := GkrSourceBodies.scopedHelper71Helper.inputs
named_values TotalCallbackArguments [low, high, left, right] := GkrSourceBodies.scopedHelper72Helper.inputs

structure ScalarBodies (definitions : List CheckedDefinition) : Prop where
  difference : BodyIn definitions GkrSourceBodies.helper58Helper Difference.body
  slope : BodyIn definitions GkrSourceBodies.helper60Helper Slope.body
  total : BodyIn definitions GkrSourceBodies.helper67Helper Total.body
  differenceWrapper : BodyIn definitions GkrSourceBodies.scopedHelper67Helper DifferenceWrapper.body
  slopeWrapper : BodyIn definitions GkrSourceBodies.scopedHelper68Helper SlopeWrapper.body
  slopeCallback : BodyIn definitions GkrSourceBodies.scopedHelper69Helper SlopeCallback.body
  totalWrapper : BodyIn definitions GkrSourceBodies.scopedHelper71Helper TotalWrapper.body
  totalCallback : BodyIn definitions GkrSourceBodies.scopedHelper72Helper TotalCallback.body

end
end ZkcSecurity.Realizations.Gkr.HonestLine.Goals
