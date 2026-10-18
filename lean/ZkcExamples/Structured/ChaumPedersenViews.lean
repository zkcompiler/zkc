module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.ChaumPedersenData
public import ZkcExamples.Structured.ChaumPedersenBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.ChaumPedersenViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

structured_views ChaumPedersenData.snapshot
  helpers [formula := ChaumPedersenBodies.formula]
  protocols [interactive := ChaumPedersenBodies.interactive]

theorem admitted : check ChaumPedersenData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.ChaumPedersenViews
