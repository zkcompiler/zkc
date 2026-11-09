module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.RepeatNestedData
public import Zkc.Applications.IR.Structured.RepeatNestedBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatNestedViews
open Zkc.Source Zkc.Source.Structured RepeatNestedBodies

set_option smartUnfolding false

structured_views RepeatNestedData.snapshot
  helpers []
  protocols [run]

end ZkcExamples.Structured.RepeatNestedViews
