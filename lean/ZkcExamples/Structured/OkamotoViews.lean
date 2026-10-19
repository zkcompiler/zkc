module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.OkamotoData
public import ZkcExamples.Structured.OkamotoBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage
Okamoto unit, emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.OkamotoViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

structured_views OkamotoData.snapshot
  helpers [formula := OkamotoBodies.formula]
  protocols [interactive := OkamotoBodies.interactive]

theorem admitted : check OkamotoData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.OkamotoViews
