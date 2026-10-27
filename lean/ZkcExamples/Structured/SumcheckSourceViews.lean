module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckSourceData
public import ZkcExamples.Structured.SumcheckSourceBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases. The six formula
helpers reuse the relation-contract bodies; every other body is named in
`SumcheckSourceBodies`, whose shared helper bodies abbreviate
`SumcheckHelperBodies`. -/
namespace ZkcExamples.Structured.SumcheckSourceViews
open Zkc.Source Zkc.Source.Structured SumcheckSourceBodies

set_option smartUnfolding false

structured_views SumcheckSourceData.snapshot
  helpers [inputShape := (SumcheckRelationContract.shapeHelper, SumcheckRelationContract.shapeBody),
    sumAdd := (SumcheckRelationContract.addHelper, SumcheckRelationContract.addBody),
    sumStep := (SumcheckRelationContract.foldSpec.stepHelper, SumcheckRelationContract.stepBody),
    sumTotal := SumcheckRelationContract.total, sumFormula := SumcheckRelationContract.sum,
    less, rows, shape, table, values, tableSumFormula := SumcheckRelationContract.tableSum,
    width, «variables», empty, halves, sums, interpolate, append,
    interpolateRealization, mapCallback, map, first, step, foldStep, valuesRealization,
    fold, foldWrapper, «prefix», checkTable, check]
  protocols [reduce, run]

end ZkcExamples.Structured.SumcheckSourceViews
