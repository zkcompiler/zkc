module

public import Zkc.Applications.IR.Structured.GkrSourceLaws
public import Zkc.IR.Source.Structured.DeterministicFold
public meta import Zkc.Tools.IR.StructuredSource.HelperPresentation
public meta import Zkc.Tools.IR.StructuredSource.ReferenceComposition
public meta import Zkc.Tools.IR.StructuredSource.NamedValues

@[expose] public section

/-! Named complete goals from the admitted readback helper bodies. This module
selects no mathematical readback reference and imports no readback companion. -/
namespace ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackGoals
open Zkc.Source Zkc.Source.Structured ZkcExamples.Structured

helper_presentation Zero inputs [] outputs [value] := GkrSourceBodies.helper28Body
helper_presentation ZeroWrapper inputs [] outputs [value] := GkrSourceBodies.helper87Body
helper_presentation Step inputs [current, index, value, position]
  outputs [selected, nextIndex] := GkrSourceBodies.helper29Body
helper_presentation Callback inputs [current, index, value, source, position]
  outputs [selected, nextIndex] := GkrSourceBodies.helper30Body
helper_presentation Scan inputs [source, current, index, position]
  outputs [selected, nextIndex] := GkrSourceBodies.helper95Body
helper_presentation ScanWrapper inputs [current, index, position, source]
  outputs [selected, nextIndex] := GkrSourceBodies.helper96Body
helper_presentation Element inputs [source, position] outputs [value] := GkrSourceBodies.helper97Body
helper_presentation After inputs [source, position] outputs [value] := GkrSourceBodies.helper98Body

abbrev foldSpec : FoldSpec :=
  (GkrSourceLaws.fold? GkrSourceBodies.helper95Body).get (by decide +kernel)

named_values State [current, index] := foldSpec.state
named_values Item [value] := foldSpec.domain.items
named_values DomainArguments [source] := foldSpec.domain.inputs
named_values Captures [position] := foldSpec.captures

/-- Every dependency is associated separately; matching its signature alone is
insufficient. This record can be installed for any linked definition list. -/
structure Bodies (definitions : List CheckedDefinition) : Prop where
  zero : BodyIn definitions GkrSourceBodies.helper28Helper Zero.body
  zeroWrapper : BodyIn definitions GkrSourceBodies.helper87Helper ZeroWrapper.body
  step : BodyIn definitions GkrSourceBodies.helper29Helper Step.body
  callback : BodyIn definitions GkrSourceBodies.helper30Helper Callback.body
  scan : BodyIn definitions GkrSourceBodies.helper95Helper Scan.body
  scanWrapper : BodyIn definitions GkrSourceBodies.helper96Helper ScanWrapper.body
  element : BodyIn definitions GkrSourceBodies.helper97Helper Element.body
  after : BodyIn definitions GkrSourceBodies.helper98Helper After.body

end ZkcSecurity.Realizations.Gkr.HonestHelpers.ReadbackGoals
