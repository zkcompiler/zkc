module

public import ZkcExamples.Structured.GkrSourceLaws
public import Zkc.Source.Structured.DeterministicFold
public meta import ZkcTools.StructuredSource.HelperPresentation
public meta import ZkcTools.StructuredSource.ReferenceComposition
public meta import ZkcTools.StructuredSource.NamedValues

@[expose] public section

/-! Named complete goals from the admitted readback helper bodies. This module
selects no mathematical readback reference and imports no readback companion. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackGoals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

helper_presentation Zero inputs [] outputs [value] := GkrSourceBodies.helper46Body
helper_presentation ZeroWrapper inputs [] outputs [value] := GkrSourceBodies.scopedHelper74Body
helper_presentation Step inputs [current, index, value, position]
  outputs [selected, nextIndex] := GkrSourceBodies.helper53Body
helper_presentation Callback inputs [current, index, value, source, position]
  outputs [selected, nextIndex] := GkrSourceBodies.helper54Body
helper_presentation Scan inputs [source, current, index, position]
  outputs [selected, nextIndex] := GkrSourceBodies.scopedHelper82Body
helper_presentation ScanWrapper inputs [current, index, position, source]
  outputs [selected, nextIndex] := GkrSourceBodies.helper56Body
helper_presentation Element inputs [source, position] outputs [value] := GkrSourceBodies.helper57Body
helper_presentation After inputs [source, position] outputs [value] := GkrSourceBodies.helper70Body

abbrev foldSpec : FoldSpec :=
  (GkrSourceLaws.fold? GkrSourceBodies.scopedHelper82Body).get (by decide +kernel)

named_values State [current, index] := foldSpec.state
named_values Item [value] := foldSpec.domain.items
named_values DomainArguments [source] := foldSpec.domain.inputs
named_values Captures [position] := foldSpec.captures

/-- Every dependency is associated separately; matching its signature alone is
insufficient. This record can be installed for any linked definition list. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  zero : BodyIn definitions GkrSourceBodies.helper46Helper Zero.body
  zeroWrapper : BodyIn definitions GkrSourceBodies.scopedHelper74Helper ZeroWrapper.body
  step : BodyIn definitions GkrSourceBodies.helper53Helper Step.body
  callback : BodyIn definitions GkrSourceBodies.helper54Helper Callback.body
  scan : BodyIn definitions GkrSourceBodies.scopedHelper82Helper Scan.body
  scanWrapper : BodyIn definitions GkrSourceBodies.helper56Helper ScanWrapper.body
  element : BodyIn definitions GkrSourceBodies.helper57Helper Element.body
  after : BodyIn definitions GkrSourceBodies.helper70Helper After.body

end ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackGoals
