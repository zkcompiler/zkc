module

public import Zkc.Applications.IR.Structured.GkrSourceLaws
public import Zkc.IR.Source.Structured.DeterministicFold
public import Zkc.IR.Source.Structured.CollectionFold
public import Zkc.IR.Source.Structured.HelperCallbacks
public meta import Zkc.Tools.IR.StructuredSource.HelperCallbacks
public meta import Zkc.Tools.IR.StructuredSource.HelperPresentation
public meta import Zkc.Tools.IR.StructuredSource.NamedValues
public meta import Zkc.Tools.IR.StructuredSource.ProcessReference
public meta import Zkc.Tools.IR.StructuredSource.ReferenceComposition

@[expose] public section

/-! Complete source-selected line helper goals. The source determines every
schema, callback, return and stopping branch before a companion is chosen. -/
namespace ZkcSecurity.Realizations.Gkr.HonestLine.Goals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured
noncomputable section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

helper_presentation Constant inputs [initial, value, width] outputs [values] := GkrSourceBodies.helper88Body
helper_presentation ConstantWrapper inputs [initial, value, width] outputs [values] := GkrSourceBodies.helper89Body
helper_presentation ConstantStep inputs [initial, value, source, width] outputs [values] := GkrSourceBodies.helper90Body
helper_presentation ConstantFold inputs [source, initial, width] outputs [values] := GkrSourceBodies.helper93Body
helper_presentation Constants inputs [initial, width, source] outputs [values] := GkrSourceBodies.helper94Body
helper_presentation Difference inputs [high, low] outputs [value] := GkrSourceBodies.helper31Body
helper_presentation DifferenceWrapper inputs [high, low] outputs [value] := GkrSourceBodies.helper80Body
helper_presentation Slope inputs [low, high, delta] outputs [value] := GkrSourceBodies.helper32Body
helper_presentation SlopeWrapper inputs [low, high, delta] outputs [value] := GkrSourceBodies.helper81Body
helper_presentation SlopeCallback inputs [low, high, left, right, delta] outputs [value] := GkrSourceBodies.helper82Body
helper_presentation Slopes inputs [left, right, delta] outputs [values] := GkrSourceBodies.helper83Body
helper_presentation Total inputs [left, right] outputs [value] := GkrSourceBodies.helper33Body
helper_presentation TotalWrapper inputs [left, right] outputs [value] := GkrSourceBodies.helper84Body
helper_presentation TotalCallback inputs [low, high, left, right] outputs [value] := GkrSourceBodies.helper85Body
helper_presentation Totals inputs [left, right] outputs [values] := GkrSourceBodies.helper86Body
helper_presentation ShiftStep inputs [initial, previous, offset, value, count]
  outputs [values, previous, offset] := GkrSourceBodies.helper91Body
helper_presentation ShiftCallback inputs [initial, previous, offset, value, source, count]
  outputs [values, previous, offset] := GkrSourceBodies.helper92Body
helper_presentation ShiftFold inputs [source, initial, previous, offset, count]
  outputs [values, previous, offset] := GkrSourceBodies.helper99Body
helper_presentation ShiftWrapper inputs [initial, previous, offset, count, source]
  outputs [values, previous, offset] := GkrSourceBodies.helper100Body
helper_presentation Shift inputs [source, count] outputs [values] := GkrSourceBodies.helper101Body
helper_callback lineCallback from GkrSourceBodies.helper102Body
helper_presentation Step inputs [iteration, values, position, start, finish, count]
  outputs [values, position, start, finish, count] := lineCallback
helper_presentation Line inputs [values, start, finish, width] outputs [coefficients] := GkrSourceBodies.helper102Body

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

named_values SlopesItem [low, high] := slopesSpec.domain.items
named_values TotalsItem [low, high] := totalsSpec.domain.items
named_values SlopesDomain [left, right] := slopesSpec.domain.inputs
named_values SlopesCaptures [delta] := slopesSpec.captures
named_values TotalsDomain [left, right] := totalsSpec.domain.inputs

source_reference slopesProcess from_equation Slopes.equation
  using [Slopes.run, Slopes.encode, Slopes.decode, PIR.Process.bind_assoc, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Values.get]
source_reference stepProcess from_equation Step.equation
  using [Step.run, Step.encode, Step.decode, PIR.Process.bind_assoc, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Values.get]
source_reference lineProcess from_equation Line.equation
  using [Line.run, Line.encode, Line.decode, PIR.Process.bind_assoc, PIR.Process.bind,
    Zkc.Source.Environment.prepend, Zkc.Source.Environment.push, Values.get]

structure ScalarBodies (definitions : List CheckedDefinition) : Prop where
  difference : BodyIn definitions GkrSourceBodies.helper31Helper Difference.body
  slope : BodyIn definitions GkrSourceBodies.helper32Helper Slope.body
  total : BodyIn definitions GkrSourceBodies.helper33Helper Total.body
  differenceWrapper : BodyIn definitions GkrSourceBodies.helper80Helper DifferenceWrapper.body
  slopeWrapper : BodyIn definitions GkrSourceBodies.helper81Helper SlopeWrapper.body
  slopeCallback : BodyIn definitions GkrSourceBodies.helper82Helper SlopeCallback.body
  totalWrapper : BodyIn definitions GkrSourceBodies.helper84Helper TotalWrapper.body
  totalCallback : BodyIn definitions GkrSourceBodies.helper85Helper TotalCallback.body

end
end ZkcSecurity.Realizations.Gkr.HonestLine.Goals
