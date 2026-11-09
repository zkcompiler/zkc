module

public import Zkc.IR.Source.Structured.UnitViews
public import Zkc.Applications.IR.Structured.ChaumPedersenData
public import Zkc.Applications.IR.Structured.ChaumPedersenBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.ChaumPedersenViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

open ZkcExamples.Structured.ChaumPedersenBodies in
structured_views ChaumPedersenData.snapshot
  helpers [formula, helper1]
  protocols [interactive]

theorem admitted : check ChaumPedersenData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.ChaumPedersenViews
