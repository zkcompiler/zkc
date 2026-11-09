module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.OkamotoData
public import Zkc.Applications.IR.Structured.OkamotoBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.OkamotoViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

open ZkcExamples.Structured.OkamotoBodies in
structured_views OkamotoData.snapshot
  helpers [formula]
  protocols [interactive]

theorem admitted : check OkamotoData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.OkamotoViews
