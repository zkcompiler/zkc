module

public import Zkc.Source.Structured.UnitViews
public import ZkcExamples.Structured.SumcheckReduceData
public import ZkcExamples.Structured.SumcheckReduceBodies
public import ZkcExamples.Structured.SumcheckRelationContract

@[expose] public section

/-! Complete checked payload and named kernel admission phases. The four formula
helpers reuse the relation-contract bodies; every other body is named in
`SumcheckReduceBodies`, whose shared helper bodies abbreviate
`SumcheckHelperBodies`. -/
namespace ZkcExamples.Structured.SumcheckReduceViews
open Zkc.Source Zkc.Source.Structured SumcheckReduceBodies

set_option smartUnfolding false

structured_views SumcheckReduceData.snapshot
  helpers [less, rows, shape, table, values,
    sumAdd := (SumcheckRelationContract.addHelper, SumcheckRelationContract.addBody),
    sumStep := (SumcheckRelationContract.foldSpec.stepHelper, SumcheckRelationContract.stepBody),
    sumTotal := SumcheckRelationContract.total, tableSumFormula := SumcheckRelationContract.tableSum,
    width, «variables», empty, halves, sums, interpolate, append,
    interpolateRealization, mapCallback, map, first]
  protocols [reduce, run]

end ZkcExamples.Structured.SumcheckReduceViews
