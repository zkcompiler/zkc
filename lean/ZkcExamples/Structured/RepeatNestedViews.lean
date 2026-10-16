module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.RepeatNestedData
public import ZkcExamples.Structured.RepeatNestedBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatNestedViews
open Zkc.Source Zkc.Source.Structured RepeatNestedBodies

set_option smartUnfolding false

structured_views RepeatNestedData.snapshot
  helpers []
  protocols [run]

end ZkcExamples.Structured.RepeatNestedViews
