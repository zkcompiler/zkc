module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckSourceData
public import ZkcExamples.Structured.SumcheckSourceBodies

@[expose] public section

/-! Checked payload and admission phases of the retained original-stage unit,
emitted by `structured_views` from its literal typed bodies. -/
namespace ZkcExamples.Structured.SumcheckSourceViews
open Zkc.Source Zkc.Source.Structured

set_option smartUnfolding false

open ZkcExamples.Structured.SumcheckSourceBodies in
structured_views SumcheckSourceData.snapshot
  helpers [inputShape, sumAdd, sumStep, sumTotal, sumFormula, less, rows, shape, table, pending, width, values, «variables», tableShapeFormula, pendingFormula, empty, openClaim, halves, sums, interpolate, append, atPrefix, interpolateRealization, mapCallback, map, first, step, foldStep, valuesRealization, fold, foldWrapper, «prefix», checkTable, check]
  protocols [reduce, run]

theorem admitted : check SumcheckSourceData.snapshot = .ok program := kernel_admission

end ZkcExamples.Structured.SumcheckSourceViews
