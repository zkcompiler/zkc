module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.RepeatData
public import Zkc.Applications.IR.Structured.RepeatBodies

@[expose] public section

/-! Complete checked payload and named kernel admission phases. -/
namespace ZkcExamples.Structured.RepeatViews
open Zkc.Source Zkc.Source.Structured RepeatBodies

set_option smartUnfolding false

structured_views RepeatData.snapshot
  helpers []
  protocols [round, run]

end ZkcExamples.Structured.RepeatViews
