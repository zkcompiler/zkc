module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckSourceData
public import ZkcExamples.Structured.SumcheckSourceBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases. The five formula
helpers reuse the relation-contract bodies; every other body is authored in
`SumcheckSourceBodies`. -/
namespace ZkcExamples.Structured.SumcheckSourceViews
open Zkc.Source Zkc.Source.Structured SumcheckSourceBodies

set_option smartUnfolding false

structured_views SumcheckSourceData.snapshot
  helpers [sumAdd := (SumcheckRelationContract.addHelper, SumcheckRelationContract.addBody),
    sumStep := (SumcheckRelationContract.foldSpec.stepHelper, SumcheckRelationContract.stepBody),
    sumTotal := SumcheckRelationContract.total, sumFormula := SumcheckRelationContract.sum,
    tableSumFormula := SumcheckRelationContract.tableSum,
    less, rows, shape, table, width, «variables», empty, halves, sums, interpolate, map, first,
    append, step, foldStep, fold, foldWrapper, «prefix», values, valuesRealization, checkTable, check]
  protocols [reduce, run]

end ZkcExamples.Structured.SumcheckSourceViews
