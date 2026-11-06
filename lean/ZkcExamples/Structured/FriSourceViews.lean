module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.FriSourceData
public import ZkcExamples.Structured.FriSourceBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.FriSourceViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

open ZkcExamples.Structured.FriSourceBodies in
structured_views FriSourceData.snapshot
  helpers [helper0, helper1, helper2, helper3, helper4, helper5, helper6, helper7, helper8, helper9, helper10, helper11, helper12, formula, helper14, helper15, helper16, helper17, helper18, helper19, helper20, helper21, helper22, helper23, helper24, helper25, helper26, helper27, helper28, helper29, helper30, helper31, helper32, helper33, helper34, helper35, helper36]
  protocols [protocol0, protocol1, protocol2, protocol3, protocol4, protocol5, run]

theorem admitted : check FriSourceData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.FriSourceViews
