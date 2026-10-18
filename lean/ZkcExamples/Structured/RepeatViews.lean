module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.RepeatData
public import ZkcExamples.Structured.RepeatBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatViews
open Zkc.Source Zkc.Source.Structured RepeatBodies

set_option smartUnfolding false

structured_views RepeatData.snapshot
  helpers []
  protocols [round, run]

end ZkcExamples.Structured.RepeatViews
