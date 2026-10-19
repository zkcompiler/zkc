module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.RepeatServiceWrapperData
public import ZkcExamples.Structured.RepeatServiceWrapperBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatServiceWrapperViews
open Zkc.Source Zkc.Source.Structured RepeatServiceWrapperBodies

set_option smartUnfolding false

structured_views RepeatServiceWrapperData.snapshot
  helpers []
  protocols [draw, run, outer]

end ZkcExamples.Structured.RepeatServiceWrapperViews
