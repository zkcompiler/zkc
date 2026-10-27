module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SchnorrAndData
public import ZkcExamples.Structured.SchnorrAndBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.SchnorrAndViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

open ZkcExamples.Structured.SchnorrAndBodies in
structured_views SchnorrAndData.snapshot
  helpers [formula]
  protocols [interactive]

theorem admitted : check SchnorrAndData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.SchnorrAndViews
